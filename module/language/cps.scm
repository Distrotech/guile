(define-module (language cps)
  #:use-module (system base syntax) ;; for define-type
  #:use-module (srfi srfi-1)
  #:use-module (system vm rtl) ;; for assemble-program
  #:use-module (language integer-sets) ;; not really
  #:use-module (ice-9 match) ;; not really
  #:use-module (ice-9 q) ;; used in generate-shuffle
  #:export (<cps> cps?
            <letval> letval? make-letval letval-names letval-vals letval-body
            <letrec> letrec? make-letrec letrec-funcs letrec-body
            <letcont> letcont? make-letcont letcont-conts letcont-body
            <outer> outer? make-outer outer-names outer-body

            cps->rtl allocate-registers-and-labels! with-alloc cps->program
            generate-shuffle

            return-three call-arg compose identity))

;; this is based on Kennedy's intermediate language. the CPS
;; representation has several useful aspects:

;;  1) first, it's a runnable Scheme program (or close enough to
;;  Scheme). The CPS transformation applies to every Scheme program and
;;  preserves semantics.

;;  2) the let-based CPS is a representation of the dominator tree of
;;  the control flow graph of this program. in every <let___> block, the
;;  code in the body must be executed before the funcs or conts, and
;;  once control exits the body, it never goes back. basically, the let
;;  forms represent some subset of the control flow graph in two parts,
;;  and control only flows one direction between the parts.

;;  3) it represents all lexical non-lambda variables by arguments to
;;  continuations or functions. therefore, we don't need to worry about
;;  searching a lexical environment for them. this also means that we
;;  can use the argument lists of continuations (and functions!) to
;;  track the liveness of those variables.
(define-type <cps>
  ;; <letval> actually handles multiple constant values, because why
  ;; not?
  (<letval> names vals body)
  ;; Kennedy's paper calls this 'letfun', but 'letrec' is more standard
  ;; in Scheme
  (<letrec> names funcs body)
  ;; the important thing about continuations (as opposed to functions)
  ;; is that they can always be compiled as jumps. this is information
  ;; that was in the program itself, but would be lost if we compiled
  ;; everything to lambdas without distinguishing them in some
  ;; way. also, continuations can never be referenced by variables, so
  ;; we don't need to worry about packaging them up.
  (<letcont> names conts body)
  ;; the 'outer' form only appears as the outermost part of a CPS
  ;; expression. when we are compiling a procedure, it holds the names
  ;; of that procedure's arguments, to distinguish them from free
  ;; variables. every CPS form should be surrounded by an 'outer'.
  (<outer> names body)
  ;; right now we are missing the 'let' from Kennedy's paper. That is
  ;; used to compose record constructors and field accessors, but we are
  ;; not attempting to do that yet.
  )
;; the 'body' in all three regular CPS cases must be either another
;; 'let...' form or a call to a function or a continuation. The first
;; argument to any call is the continuation to be passed. There is a
;; special continuation called 'return which means that we are leaving
;; our function, if we are just compiling one top-level function.

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

;; a mapping from names to values. right now it only holds
;; continuations, but there's no barrier to it holding other things,
;; because all of the CPS names are distinct symbols. we don't have to
;; worry about scoping, either. it might be better to get rid of this
;; and replace names with direct links to their values, but that's a
;; bigger project
(define name-value (make-object-property))

;; and every function in a 'letrec', plus the 'outer' form, gets the
;; number of local variables it needs, so we can allocate them with the
;; 'nlocals or 'assert-nargs-ee/nlocals instructions. this is also set
;; by allocate-registers-and-labels!, because it has all the information
;; we need anyway.
(define nlocals (make-object-property))

;; This function walks some CPS and allocates registers and labels for
;; it. It's certainly not optimal yet. It also sets the name-value
;; property for continuations
(define (allocate-registers-and-labels! cps)
  (define (visit cps counter)
    ;; counter is the number of local variables we've already allocated.
    (if (pair? cps)
        ;; a pair is either a lambda expression or a call.
        (if (eq? (car cps) 'lambda)
            (let iter ((args (cadr cps))
                       (counter counter))
              (if (null? args)
                  (visit (caddr cps) counter)
                  (begin
                    (set! (register (car args)) counter)
                    (iter (cdr args) (+ counter 1)))))
            counter)
        ;; TO DO: if the car of the pair is 'lambda, visit the body of the
        ;; lambda-expression.
        (record-case cps
                     ((<letval> names vals body)
                      (let iter ((names names)
                                 (counter counter))
                        (if (null? names)
                            (visit body counter)
                            (begin
                              (set! (register (car names)) counter)
                              (iter (cdr names) (+ counter 1))))))

                     ;; an important scoping point: none of the
                     ;; arguments to any of the <letcont>'s
                     ;; continuations are in scope for any of the other
                     ;; continuations, or the body. therefore, we
                     ;; allocate registers for them
                     ;; independently. (TO DO: if we have a bunch of
                     ;; continuations that are going to call each other
                     ;; recursively, we should try to set up our
                     ;; allocation to avoid unnecessary moves.)
                     ((<letcont> names conts body)
                      ;; first, allocate some labels
                      (map (lambda (n)
                             (set! (label n)
                                   (string->symbol
                                    (string-append
                                     "l-" (number->string label-counter))))
                             (set! label-counter (+ label-counter 1)))
                           names)
                      ;; then the name-value mapping
                      (map (lambda (n c)
                             (set! (name-value n) c))
                           names conts)
                      ;; then local variables. we need to return the
                      ;; maximum of the register numbers used so that
                      ;; whatever procedure we're part of will allocate
                      ;; the right number of local variable slots on the
                      ;; stack.
                      (apply max (visit body counter)
                             (map (lambda (c) (visit c counter)) conts)))

                     ;; in a letrec, unlike a letcont, we do have to
                     ;; allocate registers to hold the actual functions,
                     ;; because they could be used as values instead of
                     ;; just as static jump targets. but they can also
                     ;; reference each other, so we 
                     ((<letrec> names funcs body)
                      (let alloc-funcs ((names names)
                                        (counter counter))
                        (if (not (null? names))
                            (begin
                              (set! (register (car names)) counter)
                              (alloc-funcs (cdr names) (+ counter 1)))
                            (let ((alloc-func (lambda (f) (visit f counter))))
                              (map alloc-func funcs)
                              (visit body counter))))))))
  (record-case cps
    ((<outer> names body)
     (let iter ((names names)
                (counter 0))
       (if (null? names)
           (let ((total (visit body counter)))
             ;; we reserve one more than whatever number of variables we
             ;; have because we might need some extra space to move
             ;; variables around. see the move-generator below. this
             ;; should really be fixed.
             (set! (nlocals cps) (+ total 1)))
           (begin
             (set! (register (car names)) counter)
             (iter (cdr names) (+ counter 1))))))))

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

  (cond ((pair? cps)
         (if (eq? (car cps) 'lambda)
             (cons 'lambda (map with-alloc (cdr cps)))
             (map with-alloc cps)))
        ((symbol? cps)
         (with-reg cps))
        (else
         (record-case cps
           ((<letval> names vals body)
            `(letval ,(map with-reg names)
                     ,vals ,body))
           ((<letcont> names conts body)
            `(letcont ,(map (lambda (name cont)
                              `((,name . ,(label name))
                                lambda ,(map with-alloc (cadr cont))
                                ,(with-alloc (caddr cont))))
                            names conts)
                      ,(with-alloc body)))
           ((<outer> names body)
            `(outer ,(map with-reg names)
                    ,(with-alloc body)))))))

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
    (if (pair? cps)
        ;; it's a call to a continuation with some arguments
        (cond
         ;; a call that returns is easy
         ((eq? (car cps) 'return)
          `((return ,(register (cadr cps)))))
         ;; more generally, a call whose continuation escapes from our
         ;; scope is easy - it must be a tail call, because it's never
         ;; coming back. (we only check for 'return right now because
         ;; that's the only escaping continuation so far). TO DO: check
         ;; whether (car cps) is a continuation or a real function, and
         ;; do something different if it's a continuation.
         ((eq? (cadr cps) 'return)
          (let ((num-args (length (cddr cps))))
            ;; the shuffle here includes the procedure that we're going
            ;; to call, because we don't want to accidentally overwrite
            ;; it. this is a bit ugly - maybe there should be a better
            ;; generate-shuffle procedure that knows that some registers
            ;; are "protected", meaning that their values have to exist
            ;; after the shuffle, but don't have to end up in any
            ;; specific target register.
            (let ((shuffle
                   (cons (cons (register (car cps))
                               (+ num-args 1))
                         (let iter ((args (cddr cps))
                                    (arg-num 0))
                             (if (null? args)
                                 '()
                                 (cons
                                  (cons (register (car args))
                                        arg-num)
                                  (iter (cdr args) (+ arg-num 1))))))))
              `(,@(apply generate-shuffle (+ num-args 2) shuffle)
                (tail-call ,num-args ,(+ num-args 1))))))
         ((label (cadr cps)) ;; a call whose continuation is bound in a
                             ;; letcont form
          (let ((return-base (register (caadr (name-value (cadr cps))))))
            ;; return-base is the stack offset where we want to put the
            ;; return values of this function. there can't be anything
            ;; important on the stack past return-base, because
            ;; anything in scope would already have a reserved spot on
            ;; the stack before return-base, because the allocator works
            ;; that way.
          `((call ,return-base ,(register (car cps))
                  ,(map register (cddr cps)))
            ;; the RA and MVRA both branch to the continuation. we don't
            ;; do error checking yet.
            (br ,(label (cadr cps)))    ;; MVRA
            (br ,(label (cadr cps)))))) ;; RA
         (else (error "We don't know how to compile" cps)))
        ;; it's a let expression
        (record-case cps
          ((<letval> names vals body)
           `(,@(append-map!
                (lambda (name val)
                  `((load-constant ,(register name) ,val)))
                names vals)
             ,@(visit body)))
          ((<letcont> names conts body)
           (apply append
                  (visit body)
                  (map (lambda (n c)
                         `((label ,(label n))
                           ,@(visit (caddr c))))
                       names conts))))))

  (allocate-registers-and-labels! cps)
  (record-case cps
    ((<outer> names body)
     `((begin-program foo) ;; TO DO: save the name of the program
       (assert-nargs-ee/locals ,(length names) ,(nlocals cps))
       ,@(visit body)
       (end-program)))))

(define (cps->program cps)
  (assemble-program
   (cps->rtl cps)))

;; Here are some test pieces of CPS:
;; (lambda () 3)
(define return-three
  (make-outer '()
    (make-letval '(val) '(3) '(return val))))

;; (lambda (x) (x))
(define call-arg
  (make-outer '(x)
    '(x return)))

;; (lambda (x y) (x (y)))
(define compose
  (make-outer '(x y)
    (make-letcont '(c1)
      (list '(lambda (r) (x return r)))
      '(y c1))))

;; (lambda (k x) (k x)) <= (lambda (x) x)
(define identity
  (make-outer '(x)
    '(return x)))


;; (lambda (k x) (* k 2 x)) <= (lambda (x) (* x 2))

;; (lambda (k x) (* (lambda (y) (+ k 3 y)) 2)) <= (lambda (x) (+ 3 (* x 2)))
