(define-module (language cps)
  #:use-module (system base syntax) ;; for define-type
  #:use-module (srfi srfi-1) ;; for append-map!
  #:use-module (system vm rtl) ;; for assemble-program
  #:use-module (language integer-sets) ;; not really
  #:use-module (ice-9 match) ;; not really
  #:export (<cps> cps?
            <letval> letval? make-letval letval-names letval-vals letval-body
            <letrec> letrec? make-letrec letrec-funcs letrec-body
            <letcont> letcont? make-letcont letcont-conts letcont-body
            <outer> outer? make-outer outer-names outer-body

            cps->rtl allocate-registers! with-regs cps->program

            return-three call-arg compose))

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

;; and every contination gets a label, so we can jump to it
(define label (make-object-property))

;; and every function in a 'letrec', plus the 'outer' form, gets the
;; number of local variables it needs, so we can allocate them with the
;; 'nlocals or 'assert-nargs-ee/nlocals instructions. this is also set
;; by allocate-registers!, because it has all the information we need
;; anyway.
(define nlocals (make-object-property))

;; This function walks some CPS and allocates registers for
;; it. Currently we never free a register before a function ends - bad,
;; but it was easy to implement.
(define (allocate-registers! cps)
  (define (visit cps counter)
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
                     ((<letcont> conts body)
                      (map (lambda (c) (visit c counter)) conts)
                      (visit body counter))

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
             (set! (nlocals cps) total))
           (begin
             (set! (register (car names)) counter)
             (iter (cdr names) (+ counter 1))))))))

;; show what registers we've allocated where. use this at the REPL:
;;   ,pp (with-regs cps)
(define (with-regs cps)
  ;; return a list that looks like the CPS, but with everyone annotated
  ;; with a register
  (define (with-reg s) ;; s must be a symbol
    (cons s (register s))) ;; (register s) will be #f if we haven't
  ;; allocated s.

  (cond ((pair? cps)
         (map with-regs cps))
        ((symbol? cps)
         (with-reg cps))
        (else
         (record-case cps
           ((<letval> names vals body)
            `(letval ,(map with-reg names)
                     ,vals ,body))
           ((<letcont> conts body)
            `(letcont ,(map (lambda (cont)
                              `(lambda ,(map with-reg (cadr cont)) . (cddr cont)))
                            conts)
                      ,body))
           ((<outer> names body)
            `(outer ,(map with-reg names)
                    ,(with-regs body)))))))

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
         ;; that's the only escaping continuation so far)
         ((and (eq? (cadr cps) 'return)
               (eq? (cddr cps) '()))
          `((tail-call 0 ,(register (car cps)))))
         (else (error "We don't know how to compile calls yet")))
        ;; it's a let expression
        (record-case cps
          ((<letval> names vals body)
           `(,@(append-map!
                (lambda (name val)
                  `((load-constant ,(register name) ,val)))
                names vals)
             ,@(visit body)))
          ((<letcont> conts body)
           (if (not (null? conts))
               (error "We don't know how to compile continuations yet")
               (visit body))))))

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
      (list '(lambda (r) (x 'return r)))
      '(y c1))))

;; (lambda (k x) (k x)) <= (lambda (x) x)

;; (lambda (k x) (x k)) <= (lambda (x) (x))

;; (lambda (k x) (* k 2 x)) <= (lambda (x) (* x 2))

;; (lambda (k x) (* (lambda (y) (+ k 3 y)) 2)) <= (lambda (x) (+ 3 (* x 2)))
