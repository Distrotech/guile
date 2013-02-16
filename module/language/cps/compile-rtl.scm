(define-module (language cps compile-rtl)
  #:use-module (language cps)
  #:use-module (language cps primitives)
  #:use-module (system vm rtl) ;; for assemble-program
  #:use-module (system base syntax) ;; for record-case
  #:use-module (ice-9 match)
  #:use-module (ice-9 q) ;; used in generate-shuffle
  #:use-module (srfi srfi-1)
  #:export (cps->rtl allocate-registers-and-labels! with-alloc show-alloc!
            cps->program generate-suffle))

;; currently, the only way we have to run RTL code is to package it up
;; into a program and call that program. Therefore, all code that we
;; compile will look like a lambda expression, maybe with no arguments.

;; we associate a register number with every CPS variable (which will
;; always be a symbol)
(define register (make-object-property))

;; and every contination gets a label, so we can jump to it. this is
;; indexed by the names of the continuations, not the actual lambda objects.
(define label (make-object-property))
(define label-counter 0)
(define (next-label!)
  (let ((label
         (string->symbol
          (string-append
           "l-" (number->string label-counter)))))
    (set! label-counter (+ label-counter 1))
    label))

;; the name-defn map lets us find the definitions of names bound in
;; 'let...'  forms. right now it only holds things from 'letval' and
;; 'letcont' forms, but there's no barrier to adding 'letrec' too. it
;; might be better to get rid of this and replace names with direct
;; links to their values, but that's a bigger project.

;; bikeshedding note: what's the correct naming convention here?
;; "name-defn"? "name->defn"? "definition"? "lookup-defn"?
(define name-defn (make-object-property))

;; this holds the number of local variable slots needed by every 'lambda'
;; form, so we can allocate them with the 'nlocals or
;; 'assert-nargs-ee/nlocals instructions. this is set by
;; allocate-registers-and-labels!, because it has all the register
;; information.
(define nlocals (make-object-property))

;; This function walks some CPS and allocates registers and labels for
;; it. It's certainly not optimal yet. It also sets the name-defn
;; property for continuations
(define (allocate-registers-and-labels! cps)
  (define (visit cps counter)
    ;; counter is the number of local variables we've already allocated.
    (record-case cps
      ((<call>) counter)

      ((<lambda> names body)
       ;; TO DO: record which variables will be closure variables.
       (let* ((after-names
               ;; assign register numbers to each argument, starting
               ;; with 0 and counting up.
               (fold (lambda (name counter)
                       (set! (register name) counter)
                       (1+ counter))
                     counter names))
              (total
               (visit body after-names)))
         ;; we reserve one more than whatever number of variables we
         ;; have because we might need an extra space to move variables
         ;; around. see generate-shuffle below. this doesn't really feel
         ;; elegant, but I don't have a better solution right now.
         (set! (nlocals cps) (+ total 1))))
      
      ((<letval> names vals body)
       ;; update the name-defn mapping
       (map (lambda (n c)
              (set! (name-defn n) c))
            names vals)

       ;; allocate the registers
       (let ((counter
              (fold
               (lambda (name counter)
                 (set! (register name) counter)
                 (1+ counter))
               counter names)))

         ;; and visit the body of the letval
         (visit body counter)))
      
      ;; an important scoping point: none of the arguments to any of the
      ;; <letcont>'s continuations are in scope for any of the other
      ;; continuations, or the body. therefore, we allocate registers
      ;; for them independently. (TO DO: if we have a bunch of
      ;; continuations that are going to call each other recursively, we
      ;; should try to set up our allocation to avoid unnecessary
      ;; moves.)
      ((<letcont> names conts body)
       ;; allocate labels for the continuations
       (map (lambda (n)
              (set! (label n) (next-label!)))
            names)
       ;; update the name-defn mapping
       (map (lambda (n c)
              (set! (name-defn n) c))
            names conts)
       ;; then allocate registers for all of the continuations and the
       ;; body. we need to return the maximum of the register numbers
       ;; used so that whatever procedure we're part of will allocate
       ;; the right number of local variable slots on the stack.
       (apply max (visit body counter)
              (map (lambda (c) (visit c counter)) conts)))
      
      ;; in a letrec, unlike a letcont, we do have to allocate registers
      ;; to hold the actual functions, because they could be used as
      ;; values instead of just as static jump targets. but they can
      ;; also reference each other, so we should allocate labels for
      ;; them too.
      ((<letrec> names funcs body)
       ;; allocate labels for the functions
       (map
        (lambda (name)
          (set! (label name) (next-label!)))
        names)

       ;; allocate registers *within* the functions
       (map (lambda (f) (visit f 0)) funcs)

       ;; and allocate registers for the functions and the body
       (let ((total
              (fold
               (lambda (name counter)
                 (set! (register name) counter)
                 (1+ counter))
               0 names)))
         (visit body counter)
         counter))
      
      ;; an if has no interesting content, so we don't need to do
      ;; anything here.
      ((<if> test consequent alternate)
       counter)))

  (visit cps 0))

;; show what registers and labels we've allocated where. use this at the
;; REPL: ,pp (with-alloc cps)
(define (with-alloc cps)
  (define (with-register s) ;; s must be a symbol
    (cons s (register s))) ;; (register s) will be #f if we haven't
                           ;; allocated s.

  
  (define (do-value v) ;; v is a cps-data object
    (cond ((var? v)
           (list 'var (var-value v)))
          ((toplevel-var? v)
           (list 'toplevel-var (toplevel-var-name v)))
          ((const? v)
           (list 'const (const-value v)))
          (else
           (error "Bad cps-data object" v))))
  
  (define (with-label s) ;; s must be the name of a continuation
    (if (eq? s 'return)
        s
        (cons s (label s))))

  (cond ((symbol? cps)
         (with-register cps))
        ((boolean? cps)
         ;; we get a boolean when with-alloc is called on the cont of a
         ;; call to a letcont continuation.
         cps)
        (else
         (record-case cps
           ((<call> proc cont args)
            (cons* (with-alloc proc)
                   (with-alloc cont)
                   (map with-alloc args)))
           ((<lambda> names body)
            `(lambda ,(map with-register names)
               ,(with-alloc body)))
           ((<letval> names vals body)
            `(letval ,(map with-register names)
                     ,(map do-value vals)
                     ,(with-alloc body)))
           ((<letcont> names conts body)
            `(letcont ,(map with-label names)
                      ,(map with-alloc conts)
                      ,(with-alloc body)))
           ((<primitive> name)
            `(primitive ,name))
           ((<if> test consequent alternate)
            `(if ,test ,consequent ,alternate))))))

(define (show-alloc! cps)
  (allocate-registers-and-labels! cps)
  (with-alloc cps))

;; this function should probably be in (ice-9 q)
(define (append-qs! q r)
  (set-cdr! (cdr q) (car r))
  (set-cdr! q (cdr r))
  q)

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

;; This is the main function. cps->rtl compiles a cps form into a list
;; of RTL code.
(define (cps->rtl cps)
  ;; generate-primitive-call: generate a call to primitive prim with the
  ;; given args, placing the result in register(s) dsts. This is its own
  ;; function because it is called twice in visit - once in the tail
  ;; case and once in the non-tail case.
  (define (generate-primitive-call dst prim args)
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
                    (var (name-defn var-value)))
               (if (toplevel-var? var)
                   (let ((var-name (toplevel-var-name var)))
                     ;; the scope is 'foo because we don't meaningfully
                     ;; distinguish scopes yet. we should really just
                     ;; cache the current module once per procedure.
                     `((cache-current-module! ,dst foo)
                       (cached-toplevel-ref ,dst foo ,var-name)))
                   `((box-ref ,dst ,(register var-value))))))
      ((set) (let* ((var-value (car args))
                    (var (name-defn var-value)))
               (if (toplevel-var? var)
                   (let ((var-name (toplevel-var-name var)))
                     `((cache-current-module! ,dst foo)
                       (cached-toplevel-set! ,(register (cadr args))
                                             foo ,var-name)))
                   `((box-set!
                      ,(register (car args))
                      ,(register (cadr args)))))))
      (else
       (let ((insn (hashq-ref *primitive-insn-table* prim))
             (arity (hashq-ref *primitive-arity-table* prim)))
         (if (and insn (= arity (length args)))
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
            (let ((return-reg
                   (+ 1 (apply max (map register args)))))
              `(,@(generate-primitive-call
                   return-reg (primitive-name proc) args)
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
            (let ((return-base (register
                                (car (lambda-names (name-defn cont))))))
              ;; return-base is the stack offset where we want to put
              ;; the return values of this function. there can't be
              ;; anything important on the stack past return-base,
              ;; because anything in scope would already have a reserved
              ;; spot on the stack before return-base, because the
              ;; allocator works that way.
              (if (primitive? proc)
                  `(,@(generate-primitive-call
                       return-base (primitive-name proc) args)
                    (br ,(label cont)))
                  `((call ,return-base ,(register proc)
                          ,(map register args))
                    ;; the RA and MVRA both branch to the continuation. we
                    ;; don't do error checking yet.
                    (br ,(label cont))    ;; MVRA
                    (br ,(label cont))))) ;; RA
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
       (($ <lambda> names body)
        ;; TO DO: save the names of the lambdas
        `((begin-program foo)
          (assert-nargs-ee/locals ,(length names) ,(nlocals cps))
          ,@(visit body)
          (end-program)))))

  (allocate-registers-and-labels! cps)
  (visit cps))

(define (cps->program cps)
  (assemble-program
   (cps->rtl cps)))
