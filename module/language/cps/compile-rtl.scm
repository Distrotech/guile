(define-module (language cps compile-rtl)
  #:use-module (language cps)
  #:use-module (language cps primitives)
  #:use-module (language cps allocate)
  #:use-module (system base syntax) ;; for record-case
  #:use-module (ice-9 match)
  #:use-module (ice-9 q) ;; used in generate-shuffle
  #:use-module (ice-9 receive)
  #:use-module (srfi srfi-1)
  #:use-module (system base compile)
  #:use-module (language tree-il compile-cps)
  #:use-module (system vm rtl)
  #:export (cps->rtl generate-shuffle generate-rtl cps-compile))

;; currently, the only way we have to run RTL code is to package it up
;; into a program and call that program. Therefore, all code that we
;; compile will look like a lambda expression, maybe with no arguments.

;; This function generates the name-defn property, which lets us look up
;; the definition of some CPS values. It might be better to get rid of
;; this and directly link names to their definitions, but that's a
;; bigger project.
(define (name-defn-mapping cps)
  (define name-defn (make-object-property))
  
  (define (visit cps)
    (record-case cps
      ((<call>))

      ((<lambda> names rest body)
       (for-each
        (lambda (n) (set! (name-defn n) cps))
        names)

       (visit body))
      
      ((<letval> names vals body)
       (map (lambda (n c)
              (set! (name-defn n) c))
            names vals)

       (visit body))
      
      ((<letcont> names conts body)
       (map (lambda (n c)
              (set! (name-defn n) c))
            names conts)

       (for-each visit conts)
       (visit body))
      
      ((<letrec> names funcs body)
       (map (lambda (n f)
              (set! (name-defn n) f))
            names funcs)

       (for-each visit funcs)
       (visit body))
      
      ((<if> test consequent alternate))))

  (visit cps)

  name-defn)

;; this function should probably be in (ice-9 q)
(define (append-qs! q r)
  (set-cdr! (cdr q) (car r))
  (set-cdr! q (cdr r))
  q)

;; and this is some sort of general utility
(define (int-range start end)
  (if (< start end)
      (cons start (int-range (+ start 1) end))
      '()))

;; this function returns a list of `mov' instructions that accomplish a
;; shuffle in the stack. each tail argument is a pair (from . to) that
;; indicates how a value should move. the first argument is the number
;; of an extra slot that it can use as swap space if it wants to.  NOTE:
;; if the VM had a `swap' instruction, we wouldn't need an extra
;; spot. maybe we should add one.
(define (generate-shuffle swap . args)
  ;; a "move chain" is ((x1 . x2) (x2 . x3) ...). we return a list of
  ;; the swap chains we find in our args, as (ice-9 q) queues.
  (define (make-move-chains chains rest)
    ;; chains is a list of queues of elements, each of which is a move
    ;; chain, and rest is a list of whatever moves have yet to be
    ;; chained.
    (if (null? rest)
        chains
        (let* ((next (car rest))
               (front-match (find (lambda (x) (eq? (car (q-front x)) (cdr next)))
                                  chains))
               (end-match (find (lambda (x) (eq? (cdr (q-rear x)) (car next)))
                                chains)))
          ;; it is possible to get a front-match and an end-match at the
          ;; same time in two different ways. if our set of moves
          ;; includes a cycle, then we expect that at some point, the
          ;; front-match and end-match will be eq?. we need to serialize
          ;; our cycles anyway, so we just pick the front-match
          ;; arbitrarily. however, if we have a front-match and an
          ;; end-match that are not eq?, then it means we have found a
          ;; link between two of our chains, and we need to stitch them
          ;; together.
          (cond
           ((and front-match end-match (not (eq? front-match end-match)))
            ;; stitch two chains together
            (enq! end-match next)
            (append-qs! end-match front-match)
            (make-move-chains (delq front-match chains) (cdr rest)))
           (front-match ;; push next onto the beginning of a chain
            (q-push! front-match next)
            (make-move-chains chains (cdr rest)))
           (end-match ;; push next onto the end of a chain
            (enq! end-match next)
            (make-move-chains chains (cdr rest)))
           (else ;; make a new chain
            (let ((new-chain (make-q)))
              (enq! new-chain next)
              (make-move-chains (cons new-chain chains) (cdr rest))))))))

  ;; given a single move chain, generate a series of moves to implement
  ;; it, using the given swap register
  (define (moves-for-chain swap chain)
    (if (eq? (car (q-front chain))
             (cdr (q-rear chain)))
        ;; a cyclic chain!
        `((mov ,swap ,(car (q-front chain)))
          ;; we remove the first element of the chain, making it acyclic
          ,@(moves-for-acyclic-list (cdar chain))
          (mov ,(cdr (q-front chain)) ,swap))
        (moves-for-acyclic-list (car chain))))

  (define (moves-for-acyclic-list lst)
    ;; this is named -list instead of -chain because it accepts a list
    ;; holding a move chain, instead of a queue like the other -chain
    ;; functions.
    (let iter ((moves (reverse lst)))
      (if (null? moves)
          '()
          (cons `(mov ,(cdar moves) ,(caar moves))
                (iter (cdr moves))))))

  ;; step one: eliminate identity shuffles
  (let* ((no-ids (remove (lambda (x) (eq? (car x) (cdr x))) args))
         ;; step two: make move chains
         (chains (make-move-chains '() no-ids))) 
    ;; step three: generate a series of moves for each chain, using the
    ;; swap space.
    (apply append (map (lambda (x) (moves-for-chain swap x)) chains))))

;; generate-rtl compiles a CPS form to RTL.
(define (generate-rtl cps name-defn register call-frame-start
                      rest-args-start nlocals label next-label!)
  ;; generate-primitive-call: generate a call to primitive prim with the
  ;; given args, placing the result in register(s) dsts. rest is either
  ;; #f or the location of the rest arguments of the destination
  ;; continuation (if it has rest arguments). This is its own function
  ;; because it is called twice in visit - once in the tail case and
  ;; once in the non-tail case.
  (define (generate-primitive-call dsts rest prim args)
    ;; the primitives 'ref and 'set are handled differently than the
    ;; others because they need to know whether they're setting a
    ;; toplevel variable or not. I think there's some bad abstraction
    ;; going on here, but fixing it is hard. The most elegant thing from
    ;; the CPS point of view is to forget about the toplevel-ref and
    ;; toplevel-set VM instructions and just use resolve for everything,
    ;; but that's ugly and probably slow. maybe once we have a peephole
    ;; optimizer we'll be able to do that.

    (case prim
      ((ref) (let* ((var-value (car args))
                    ;; var-value is the value holding the variable
                    ;; object
                    (var (name-defn var-value))
                    ;; var is the actual variable object
                    (dst (if (pair? dsts)
                             (car dsts)
                             rest)))
               (if (toplevel-var? var)
                   ;; the scope is 'foo because we don't meaningfully
                   ;; distinguish scopes yet. we should really just
                   ;; cache the current module once per procedure.
                   `((cache-current-module! ,dst foo)
                     (cached-toplevel-ref ,dst foo
                                          ,(toplevel-var-name var)))
                   `((box-ref ,dst ,(register var-value))))))
      ((set) (let* ((var-value (car args))
                    (new-value (cadr args))
                    (var (name-defn var-value))
                    (dst (if (pair? dsts)
                             (car dsts)
                             rest)))
               (if (toplevel-var? var)
                   `((cache-current-module! ,dst foo)
                     (cached-toplevel-set! ,(register new-value) foo
                                           ,(toplevel-var-name var))
                     (mov ,dst ,(register new-value)))
                   `((box-set!
                      ,(register var-value)
                      ,(register new-value))
                     (mov ,dst ,(register new-value))))))
      (else
       (let ((insn (hashq-ref *primitive-insn-table* prim))
             (in-arity (hashq-ref *primitive-in-arity-table* prim))
             (out-arity (hashq-ref *primitive-out-arity-table* prim))
             (dst (if (pair? dsts)
                      (car dsts)
                      rest)))
         (if (and insn
                  (= in-arity (length args))
                  (= out-arity 1)) ;; we don't support n-ary outputs yet
             `((,insn ,dst ,@(map register args)))
             (error "malformed primitive call" (cons prim args)))))))
  
  (define (visit cps)
    ;; cps is either a let expression or a call
    (match cps
      ;; a call that returns is easy
      (($ <call> 'return #f (arg))
       `((return ,(register arg))))
       ;; more generally, a call whose continuation escapes from our
       ;; scope is easy - it must be a tail call, because it's never
       ;; coming back. (we only check for 'return right now because
       ;; that's the only escaping continuation so far). TO DO: check
       ;; whether proc is a continuation or a real function, and do
       ;; something different if it's a continuation.
       (($ <call> proc 'return args)
        (if (primitive? proc)
            ;; we can't really call primitive procedures in tail
            ;; position, so we just generate them in non-tail manner and
            ;; then return. this seems like it might have to change in
            ;; the future. it's fine to take the maximum register and
            ;; add one, because the allocator reserved us one extra.

            ;; note: this only handles primitives that return exactly
            ;; one value.
            (let ((return-reg
                   (+ 1 (apply max (map register args)))))
              `(,@(generate-primitive-call
                   (list return-reg) #f (primitive-name proc) args)
                (return ,return-reg)))
            
            (let ((num-args (length args)))
              ;; the shuffle here includes the procedure that we're going to
              ;; call, because we don't want to accidentally overwrite
              ;; it. this is a bit ugly - maybe there should be a better
              ;; generate-shuffle procedure that knows that some registers
              ;; are "protected", meaning that their values have to exist
              ;; after the shuffle, but don't have to end up in any specific
              ;; target register.
              (let ((shuffle
                     (cons (cons (register proc)
                                 (+ num-args 1))
                           (let iter ((args args)
                                      (arg-num 0))
                             (if (null? args)
                                 '()
                                 (cons
                                  (cons (register (car args))
                                        arg-num)
                                  (iter (cdr args) (+ arg-num 1))))))))
                `(,@(apply generate-shuffle (+ num-args 2) shuffle)
                  (tail-call ,num-args ,(+ num-args 1)))))))
       
       (($ <call> proc cont args)
        (if (label cont) ;; a call whose continuation is bound in a
                         ;; letcont form
            (let* ((dsts (map register (lambda-names (name-defn cont))))
                   (rest (rest-args-start (lambda-rest (name-defn cont))))
                   (return-start (call-frame-start cps))
                   ;; perm is the permutation we have to execute to put
                   ;; the results of the call in their destinations
                   (perm (map cons (int-range return-start
                                              (+ return-start (length dsts)))
                              dsts))
                   (perm-label (next-label!)))
              (if (primitive? proc)
                  `(,@(generate-primitive-call
                       dsts rest (primitive-name proc) args)
                    (br ,(label cont)))
                  `((call ,(call-frame-start cps) ,(register proc)
                          ,(map register args))
                    ;; shuffle the return values into their place. we
                    ;; pass #f as our swap point because this
                    ;; permutation should never need swap space.
                    (br ,perm-label) ;; MVRA
                    (br ,perm-label) ;; RA
                    (label ,perm-label)
                    ,@(apply generate-shuffle #f perm)
                    ;; the RA and MVRA both branch to the continuation. we
                    ;; don't do error checking yet.
                    (br ,(label cont)))))
            (error "We don't know how to compile" cps)))
       ;; consequent and alternate should both be continuations with no
       ;; arguments, so we call them by just jumping to them.
       (($ <if> test consequent alternate)
        ;; the second argument to br-if-true is either 0 or 1. if it is
        ;; one, the instruction acts like br-if-false.
        `((br-if-true ,(register test) 1 ,(label alternate))
          (br ,(label consequent))))
       (($ <letval> names vals body)
        ;; <letval> values can be either constants, <var>s, or
        ;; <toplevel-var>s. For constants, we intern a constant. For
        ;; <var>s, we make a box. For <toplevel-var>s, we do nothing.
        `(,@(append-map!
             (lambda (name val)
               (cond ((var? val)
                      `((box ,(register name)
                             ,(register (var-value val)))))
                     ((toplevel-var? val)
                      `())
                     ((const? val)
                      `((load-constant ,(register name)
                                       ,(const-value val))))
                     (else
                      (error "Bad cps-data object" val))))
             names vals)
          ,@(visit body)))
       (($ <letcont> names conts body)
        (apply append
               (visit body)
               (map (lambda (n c)
                      `((label ,(label n))
                        ,@(visit (lambda-body c))))
                    names conts)))
       (($ <lambda> names rest body)
        ;; TO DO: save the names of the lambdas
        `((begin-program foo)
          (assert-nargs-ee/locals ,(length names) ,(nlocals cps))
          ,@(visit body)
          (end-program)))))

  (visit cps))

;; this is a wrapper function for the CPS->RTL transformation. Its job
;; is to know about all of the passes that we do.
(define (cps->rtl cps)
  (let ((name-defn (name-defn-mapping cps)))
    (receive (register
              call-frame-start
              rest-args-start
              nlocals
              label
              next-label!)
      (allocate-registers-and-labels cps)
      (generate-rtl cps name-defn register
                    call-frame-start
                    rest-args-start nlocals
                    label next-label!))))

;; since CPS isn't complete yet, we don't want to make it part of the
;; system compiler graph, so we have our own compile function.
(define* (cps-compile x #:key (from 'scheme) (to 'value))
  (cond ((eq? from to) x)
        ((not (memq to '(scheme tree-il cps rtl value)))
         (error "Unrecognized language" to))
        (else
         (case from
           ((scheme) (cps-compile (compile x #:to 'tree-il)
                                  #:from 'tree-il #:to to))
           ((tree-il) (cps-compile (tree-il->cps x)
                                   #:from 'cps #:to to))
           ((cps) (cps-compile (cps->rtl x)
                               #:from 'rtl #:to to))
           ((rtl) (assemble-program x))
           (else (error "Unrecognized language" from))))))
