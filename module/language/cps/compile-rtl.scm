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

;; this lets us find the values of names bound in 'let...' forms. right
;; now it only holds continuations, but there's no barrier to it holding
;; other things, because all of the CPS names are distinct symbols. we
;; don't have to worry about scoping, either. it might be better to get
;; rid of this and replace names with direct links to their values, but
;; that's a bigger project.
(define name-value (make-object-property))

;; this holds the number of local variable slots needed by every 'lambda'
;; form, so we can allocate them with the 'nlocals or
;; 'assert-nargs-ee/nlocals instructions. this is set by
;; allocate-registers-and-labels!, because it has all the register
;; information.
(define nlocals (make-object-property))

;; This function walks some CPS and allocates registers and labels for
;; it. It's certainly not optimal yet. It also sets the name-value
;; property for continuations
(define (allocate-registers-and-labels! cps)
  (define (visit cps counter)
    ;; counter is the number of local variables we've already allocated.
    (record-case cps
      ((<call>) counter)
                 
      ((<lambda> names body)
       ;; TO DO: record which variables will be closure variables.
       (let iter ((names names)
                  (counter counter))
         (if (null? names)
             (let ((total (visit body counter)))
               ;; we reserve one more than whatever number of variables
               ;; we have because we might need an extra space to move
               ;; variables around. see generate-shuffle below. this
               ;; doesn't really feel elegant, but I don't have a better
               ;; solution right now.
               (set! (nlocals cps) (+ total 1)))
             (begin
               (set! (register (car names)) counter)
               (iter (cdr names) (+ counter 1))))))
      
      ((<letval> names vals body)
       (let iter ((names names)
                  (counter counter))
         (if (null? names)
             (visit body counter)
             (begin
               (set! (register (car names)) counter)
               (iter (cdr names) (+ counter 1))))))
      
      ;; an important scoping point: none of the arguments to any of the
      ;; <letcont>'s continuations are in scope for any of the other
      ;; continuations, or the body. therefore, we allocate registers
      ;; for them independently. (TO DO: if we have a bunch of
      ;; continuations that are going to call each other recursively, we
      ;; should try to set up our allocation to avoid unnecessary
      ;; moves.)
      ((<letcont> names conts body)
       ;; first, allocate some labels
       (map (lambda (n)
              (set! (label n) (next-label!)))
            names)
       ;; then the name-value mapping
       (map (lambda (n c)
              (set! (name-value n) c))
            names conts)
       ;; then local variables. we need to return the maximum of the
       ;; register numbers used so that whatever procedure we're part of
       ;; will allocate the right number of local variable slots on the
       ;; stack.
       (apply max (visit body counter)
              (map (lambda (c) (visit c counter)) conts)))
      
      ;; in a letrec, unlike a letcont, we do have to allocate registers
      ;; to hold the actual functions, because they could be used as
      ;; values instead of just as static jump targets. but they can
      ;; also reference each other, so we should allocate labels for
      ;; them too.
      ((<letrec> names funcs body)
       (let alloc-funcs ((names names)
                         (counter counter))
         (if (not (null? names))
             (begin
               (set! (register (car names)) counter)
               (set! (label (car names)) (next-label!))
               (alloc-funcs (cdr names) (+ counter 1)))
             ;; the counter resets to zero for a new lambda because when it's
             ;; called, only its arguments will be on the stack -
             ;; everything else will be a closure variable.
             (let ((alloc-func (lambda (f) (visit f 0))))
               (map alloc-func funcs)
               (visit body counter)))))

      ;; for an if, we need labels for the consequent and alternate (so
      ;; we can branch to one or the other). the register allocations
      ;; for them can overlap, since only one will ever be used, but we
      ;; need to save enough space for whichever is bigger.
      ((<if> test consequent alternate)
       (set! (label consequent) (next-label!))
       (set! (label alternate) (next-label!))
       (max (visit consequent counter)
            (visit alternate counter)))))

  (visit cps 0))

;; show what registers and labels we've allocated where. use this at the
;; REPL: ,pp (with-alloc cps)
(define (with-alloc cps)
  ;; return a list that looks like the CPS, but with everyone annotated
  ;; with a register
  (define (with-reg s) ;; s must be a symbol
    (if (eq? s 'return)
        s
        (cons s (register s)))) ;; (register s) will be #f if we haven't
                                ;; allocated s.

  (define (with-label s)
    (if (eq? s 'return)
        s
        (cons s (label s))))

  (cond ((symbol? cps)
         (with-reg cps))
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
            `(lambda ,(map with-reg names)
               ,(with-alloc body)))
           ((<letval> names vals body)
            `(letval ,(map with-reg names)
                     ,vals ,(with-alloc body)))
           ((<letcont> names conts body)
            `(letcont ,(map with-label names)
                      ,(map with-alloc conts)
                      ,(with-alloc body)))
           ((<primitive> name)
            `(primitive ,name))
           ;; this is sort of an ugly way to show the labels of the
           ;; if-branches, but I don't have a better one right now.
           ((<if> test consequent alternate)
            `(if ,test
                 (label ,(label consequent))
                 ,(with-alloc consequent)
                 (label ,(label alternate))
                 ,(with-alloc alternate)))))))

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
              (tail-call ,num-args ,(+ num-args 1))))))
       ;; note that because of where this clause is placed, we will only
       ;; compile calls to primitives with non-return
       ;; continuations. this is because I don't know how to compile
       ;; primitive tail calls yet - it might be best to make them into
       ;; non-tail calls.
       (($ <call> ($ <primitive> prim) cont args)
        (let ((insn (hashq-ref *primitive-insn-table* prim))
              (arity (hashq-ref *primitive-arity-table* prim))
              (return-reg (register
                           (car (lambda-names (name-value cont))))))
          (if (and insn (= arity (length args)))
              `((,insn ,return-reg ,@(map register args))
                (br ,(label cont)))
              (error "malformed primitive call" cps))))
       (($ <call> proc cont args)
        (if (label cont) ;; a call whose continuation is bound in a
                         ;; letcont form
            (let ((return-base (register
                                (car (lambda-names (name-value cont))))))
              ;; return-base is the stack offset where we want to put
              ;; the return values of this function. there can't be
              ;; anything important on the stack past return-base,
              ;; because anything in scope would already have a reserved
              ;; spot on the stack before return-base, because the
              ;; allocator works that way.
              `((call ,return-base ,(register proc)
                      ,(map register args))
                ;; the RA and MVRA both branch to the continuation. we
                ;; don't do error checking yet.
                (br ,(label cont))    ;; MVRA
                (br ,(label cont)))) ;; RA
            (error "We don't know how to compile" cps)))
       ;; the second argument to if is either 0 or 1. if it is one, the
       ;; instruction acts like br-if-false.
       (($ <if> test consequent alternate)
        `((br-if-true ,(register test) 1 ,(label alternate))
          ,@(visit consequent)
          (label ,(label alternate))
          ,@(visit alternate)))
       (($ <letval> names vals body)
        `(,@(append-map!
             (lambda (name val)
               `((load-constant ,(register name) ,val)))
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
