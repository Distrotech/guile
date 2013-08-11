;;; Continuation-passing style (CPS) intermediate language (IL)

;; Copyright (C) 2013 Free Software Foundation, Inc.

;;;; This library is free software; you can redistribute it and/or
;;;; modify it under the terms of the GNU Lesser General Public
;;;; License as published by the Free Software Foundation; either
;;;; version 3 of the License, or (at your option) any later version.
;;;;
;;;; This library is distributed in the hope that it will be useful,
;;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;;; Lesser General Public License for more details.
;;;;
;;;; You should have received a copy of the GNU Lesser General Public
;;;; License along with this library; if not, write to the Free Software
;;;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

;;; Commentary:
;;;
;;;
;;; Code:

(define-module (language cps compile-rtl)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (language cps)
  #:use-module (language cps arities)
  #:use-module (language cps closure-conversion)
  #:use-module (language cps slot-allocation)
  #:export (compile-rtl))

;; TODO: Source info, local var names.  Needs work in the linker and the
;; debugger.

(define (optimize exp opts)
  ;; Calls to source-to-source optimization passes go here.

  ;; Passes that are needed:
  ;; 
  ;;  * Contification: turn a $fun into a $cont if all calls to the $fun
  ;;    return to the same continuation.  This is a more rigorous
  ;;    variant of our old "fixpoint labels allocation" optimization.
  ;;
  ;;  * Test inlining, to inline some tests, turning:
  ;;
  ;;      (let ((tmp (eq? x y))) (if tmp (kt) (kf))
  ;;      => (if (eq? x y) (kt) (kf))
  ;;
  ;;  * Abort contification: turning abort primcalls into continuation
  ;;    calls, and eliding prompts if possible.
  ;;
  ;;  * Common subexpression elimination.  Desperately needed.  Requires
  ;;    effects analysis.
  ;;
  ;;  * Loop peeling.  Unrolls the first round through a loop if the
  ;;    loop has effects that CSE can work on.  Requires effects
  ;;    analysis.  When run before CSE, loop peeling is the equivalent
  ;;    of loop-invariant code motion (LICM).
  ;;
  ;;  * Generic simplification pass, to be run as needed.  Used to
  ;;    "clean up", both on the original raw input and after specific
  ;;    optimization passes.

  exp)

(define (visit-funs proc exp)
  (match exp
    (($ $continue _ exp)
     (visit-funs proc exp))

    (($ $fun meta self free body)
     (proc exp)
     (visit-funs proc body))

    (($ $letk conts body)
     (visit-funs proc body)
     (for-each (lambda (cont) (visit-funs proc cont)) conts))

    (($ $cont src sym ($ $kargs names syms body))
     (visit-funs proc body))

    (($ $cont src sym ($ $kentry arity body alternate))
     (visit-funs proc body)
     (when alternate
       (visit-funs proc alternate)))

    (_ (values))))

(define (fold-conts proc seed exp)
  (match exp
    (($ $letk conts body)
     (fold (lambda (exp seed)
             (fold-conts proc seed exp))
           (fold-conts proc seed body)
           conts))

    (($ $cont src k cont)
     (fold-conts proc (proc k src cont seed) cont))

    (($ $kargs names syms body)
     (fold-conts proc seed body))

    (_ seed)))

(define (emit-rtl-sequence exp slots nlocals)
  (define (intern-cont! k src cont table)
    (hashq-set! table k cont)
    table)

  (let* ((cont-table (fold-conts intern-cont! (make-hash-table) exp))
         (rtl '()))
    (define (slot sym)
      (lookup-slot sym slots))

    (define (constant sym)
      (lookup-constant-value sym slots))

    (define (emit asm)
      (set! rtl (cons asm rtl)))

    (define (emit-rtl label k exp next-label)
      (define (maybe-mov dst src)
        (unless (= dst src)
          (emit `(mov ,dst ,src))))

      (define (maybe-jump label)
        (unless (eq? label next-label)
          (emit `(br ,label))))

      (define (maybe-load-constant slot src)
        (call-with-values (lambda ()
                            (lookup-maybe-constant-value src slots))
          (lambda (has-const? val)
            (and has-const?
                 (begin
                   (emit `(load-constant ,slot ,val))
                   #t)))))

      (define (emit-tail)
        ;; There are only three kinds of expressions in tail position:
        ;; tail calls, multiple-value returns, and single-value returns.
        (match exp
          (($ $call proc args)
           (for-each (match-lambda
                      ((src . dst) (emit `(mov ,dst ,src))))
                     (lookup-parallel-moves label slots))
           (let ((tail-slots (cdr (iota (1+ (length args))))))
             (for-each maybe-load-constant tail-slots args))
           (emit `(tail-call ,(1+ (length args)))))
          (($ $values args)
           (let ((tail-slots (cdr (iota (1+ (length args))))))
             (for-each (match-lambda
                        ((src . dst) (emit `(mov ,dst ,src))))
                       (lookup-parallel-moves label slots))
             (for-each maybe-load-constant tail-slots args))
           (emit `(return/values ,(length args))))
          (($ $primcall 'return (arg))
           (emit `(return ,(slot arg))))))

      (define (emit-val sym)
        (let ((dst (slot sym)))
          (match exp
            (($ $var sym)
             (maybe-mov dst (slot sym)))
            (($ $void)
             (emit `(load-constant ,dst ,*unspecified*)))
            (($ $const exp)
             (when dst
               (emit `(load-constant ,dst ,exp))))
            (($ $fun meta self free body)
             (emit `(load-static-procedure ,dst ,self)))
            (($ $call proc args)
             (let ((proc-slot (lookup-call-proc-slot label slots))
                   (nargs (length args)))
               (or (maybe-load-constant proc-slot proc)
                   (maybe-mov proc-slot (slot proc)))
               (let lp ((n (1+ proc-slot)) (args args))
                 (match args
                   (()
                    (emit `(call ,proc-slot ,nargs))
                    (emit `(receive ,dst ,proc-slot ,nlocals)))
                   ((arg . args)
                    (or (maybe-load-constant n arg)
                        (maybe-mov n (slot arg)))
                    (lp (1+ n) args))))))
            (($ $primcall '+ (a b))
             (emit `(add ,dst ,(slot a) ,(slot b))))
            (($ $primcall 'current-module)
             (emit `(current-module ,dst)))
            (($ $primcall 'cached-toplevel-box (scope name bound?))
             (emit `(cached-toplevel-box ,dst ,(constant scope) ,(constant name)
                                         ,(constant bound?))))
            (($ $primcall 'cached-module-box (mod name public? bound?))
             (emit `(cached-module-box ,dst ,(constant mod) ,(constant name)
                                       ,(constant public?) ,(constant bound?))))
            (($ $primcall 'resolve (name bound?))
             (emit `(resolve ,dst ,(constant bound?) ,(slot name))))
            (($ $primcall name args)
             (emit `(,name ,dst ,@(map slot args))))
            (($ $values (arg))
             (or (maybe-load-constant (slot dst) arg)
                 (maybe-mov dst (slot arg))))
            (($ $prompt escape? tag handler)
             (emit `(prompt ,escape? ,tag ,handler))))
          (maybe-jump k)))

      (define (emit-vals syms)
        (match exp
          (($ $primcall name args)
           (emit `(primcall/vals ,name ,@args)))
          (($ $values args)
           (for-each (match-lambda
                      ((src . dst) (emit `(mov ,dst ,src))))
                     (lookup-parallel-moves label slots))
           (for-each maybe-load-constant (map slot syms) args)))
        (maybe-jump k))

      (define (emit-seq)
        (match exp
          (($ $primcall 'cache-current-module! (sym scope))
           (emit `(cache-current-module! ,(slot sym) ,(constant scope))))
          (($ $primcall name args)
           (emit `(primcall/seq ,name ,@args)))
          (($ $values ()) #f))
        (maybe-jump k))

      (define (emit-test kt kf)
        (define (unary op sym)
          (cond
           ((eq? kt next-label)
            (emit `(,op ,(slot sym) #t ,kf)))
           (else
            (emit `(,op ,(slot sym) #f ,kt))
            (maybe-jump kf))))
        (define (binary op a b)
          (cond
           ((eq? kt next-label)
            (emit `(,op ,(slot a) ,(slot b) #t ,kf)))
           (else
            (emit `(,op ,(slot a) ,(slot b) #f ,kt))
            (maybe-jump kf))))
        (match exp
          (($ $var sym) (unary 'br-if-true sym))
          (($ $primcall 'null? (a)) (unary 'br-if-null a))
          (($ $primcall 'nil? (a)) (unary 'br-if-nil a))
          (($ $primcall 'pair? (a)) (unary 'br-if-pair a))
          (($ $primcall 'struct? (a)) (unary 'br-if-struct a))
          (($ $primcall 'char? (a)) (unary 'br-if-char a))
          ;; Add TC7 tests here
          (($ $primcall 'eq? (a b)) (binary 'br-if-eq a b))
          (($ $primcall 'eq? (a b)) (binary 'br-if-eq a b))
          (($ $primcall 'eqv? (a b)) (binary 'br-if-eqv a b))
          (($ $primcall 'equal? (a b)) (binary 'br-if-equal a b))
          (($ $primcall '< (a b)) (binary 'br-if-< a b))
          (($ $primcall '<= (a b)) (binary 'br-if-<= a b))
          (($ $primcall '= (a b)) (binary 'br-if-= a b))
          (($ $primcall '>= (a b)) (binary 'br-if-<= b a))
          (($ $primcall '> (a b)) (binary 'br-if-< b a))))

      (define (emit-trunc nreq rest? k)
        (match exp
          (($ $call proc args)
           (let ((proc-slot (lookup-call-proc-slot label slots))
                 (nargs (length args)))
             (or (maybe-load-constant proc-slot proc)
                 (maybe-mov proc-slot (slot proc)))
             (let lp ((n (1+ proc-slot)) (args args))
               (match args
                 (()
                  (emit `(call ,proc-slot ,nargs))
                  (emit `(receive-values ,(1+ proc-slot) ,nreq))
                  (when rest?
                    (emit `(bind-rest ,(+ proc-slot 1 nreq))))
                  (for-each (match-lambda
                             ((src . dst) (emit `(mov ,dst ,src))))
                            (lookup-parallel-moves label slots))
                  (emit `(reset-frame ,nlocals)))
                 ((arg . args)
                  (or (maybe-load-constant n arg)
                      (maybe-mov n (slot arg)))
                  (lp (1+ n) args)))))))
        (maybe-jump k))

      (match (hashq-ref cont-table k)
        (#f (emit-tail))
        (($ $kargs (name) (sym)) (emit-val sym))
        (($ $kargs () ()) (emit-seq))
        (($ $kargs names syms) (emit-vals syms))
        (($ $kargs (name) (sym)) (emit-val sym))
        (($ $kif kt kf) (emit-test kt kf))
        (($ $ktrunc ($ $arity req () rest () #f) arity k)
         (emit-trunc (length req) (and rest #t) k))))

    (define (collect-exps k src cont tail)
      (define (find-exp term)
        (match term
          (($ $continue exp-k exp)
           (cons (list k src exp-k exp) tail))
          (($ $letk conts body)
           (find-exp body))))
      (match cont
        (($ $kargs names syms body)
         (find-exp body))
        (else tail)))

    (let lp ((exps (reverse (fold-conts collect-exps '() exp))))
      (match exps
        (() (reverse rtl))
        (((k src exp-k exp) . exps)
         (let ((next-label (match exps
                             (((k . _) . _) k)
                             (() #f))))
           (emit `(label ,k))
           (emit-rtl k exp-k exp next-label)
           (lp exps)))))))

(define (compile-fun f)
  (let ((rtl '()))
    (define (emit asm)
      (set! rtl (cons asm rtl)))

    (define (emit-fun-body self body)
      (call-with-values (lambda () (allocate-slots self body))
        (lambda (slots nlocals)
          (match body
            (($ $cont src k
                ($ $kentry ($ $arity req opt rest kw allow-other-keys?)
                   body
                   alternate))
             (let ((kw-indices (map (match-lambda
                                     ((key name sym)
                                      (cons key (lookup-slot sym slots))))
                                    kw)))
               (emit `(label ,k))
               (emit `(begin-kw-arity ,req ,opt ,rest
                                      ,kw-indices ,allow-other-keys?
                                      ,nlocals
                                      ,(match alternate
                                         (($ $cont _ k) k)
                                         (#f #f))))
               (for-each emit (emit-rtl-sequence body slots nlocals))
               (emit `(end-arity))
               (when alternate
                 (emit-fun-body self alternate))))))))

    (match f
      ;; FIXME: We shouldn't use SELF as a label.
      (($ $fun meta self free body)
       (emit `(begin-program ,self ,(or meta '())))
       (emit-fun-body self body)
       (emit `(end-program))
       (reverse rtl)))))

(define (compile-rtl exp env opts)
  (let* ((exp (fix-arities exp))
         (exp (optimize exp opts))
         (exp (convert-closures exp))
         (rtl '()))
    (visit-funs (lambda (fun)
                  (set! rtl (cons (compile-fun fun) rtl)))
                exp)
    (values (fold append '() rtl)
            env
            env)))
