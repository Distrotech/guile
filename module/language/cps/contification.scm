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
;;; Contification is a pass that turns $fun instances into $cont
;;; instances if all calls to the $fun return to the same continuation.
;;; This is a more rigorous variant of our old "fixpoint labels
;;; allocation" optimization.
;;;
;;; See Kennedy's "Compiling with Continuations, Continued", and Fluet
;;; and Weeks's "Contification using Dominators".
;;;
;;; Code:

(define-module (language cps contification)
  #:use-module (ice-9 match)
  #:use-module ((srfi srfi-1) #:select (partition))
  #:use-module (srfi srfi-26)
  #:use-module (language cps)
  #:use-module (language cps dfg)
  #:use-module (language cps primitives)
  #:use-module (language rtl)
  #:export (contify))

(define (contify fun)
  (let* ((dfg (compute-dfg fun))
         (cont-table (dfg-cont-table dfg))
         (call-substs '())
         (cont-substs '()))
    (define (subst-call! sym arities body-ks)
      (set! call-substs (acons sym (map cons arities body-ks) call-substs)))
    (define (subst-return! old-tail new-tail)
      (set! cont-substs (acons old-tail new-tail cont-substs)))
    (define (lookup-return-cont k)
      (or (assq-ref cont-substs k) k))

    (define (contify-call proc args)
      (and=> (assq-ref call-substs proc)
             (lambda (entries)
               (let lp ((entries entries))
                 (match entries
                   (() (error "invalid contification"))
                   (((($ $arity req () #f () #f) . k) . entries)
                    (if (= (length req) (length args))
                        (build-cps-term
                          ($continue k ($values args)))
                        (lp entries)))
                   ((_ . entries) (lp entries)))))))

    ;; If K is a continuation that binds one variable, and it has only
    ;; one predecessor, return that variable.
    (define (bound-symbol k)
      (match (lookup-cont k cont-table)
        (($ $kargs (_) (sym))
         (match (lookup-uses k dfg)
           ((_)
            ;; K has one predecessor, the one that defined SYM.
            sym)
           (_ #f)))
        (_ #f)))

    (define (contify-fun sym self arities tails bodies)
      ;; Are the given args compatible with any of the arities?
      (define (applicable? args)
        (or-map (match-lambda
                 (($ $arity req () #f () #f)
                  (= (length args) (length req)))
                 (_ #f))
                arities))

      ;; If the use of PROC in continuation USE is a call to PROC that
      ;; is compatible with one of the procedure's arities, return the
      ;; target continuation.  Otherwise return #f.
      (define (call-target use proc)
        (match (find-call (lookup-cont use cont-table))
          (($ $continue k ($ $call proc* args))
           (and (eq? proc proc*) (not (memq proc args)) (applicable? args)
                k))
          (_ #f)))

      (and
       (null? (lookup-uses self dfg))
       (match (lookup-uses sym dfg)
         ((use . uses)
          ;; Is the first use a contifiable call to SYM?
          (cond
           ((call-target use sym)
            => (lambda (k)
                 ;; Are all the other uses contifiable calls to SYM
                 ;; with the same target continuation?
                 (cond
                  ((and-map (lambda (use)
                              (eq? (call-target use sym) k))
                            uses)
                   ;; If so, contify: mark SYM for replacement in
                   ;; calls, and mark the tail continuations for
                   ;; replacement by K.
                   (subst-call! sym arities bodies)
                   (for-each (cut subst-return! <> k) tails)
                   k)
                  (else #f))))
           (else #f)))
         (_ #f))))

    ;; This is a first cut at a contification algorithm.  It contifies
    ;; non-recursive functions that only have positional arguments.
    (define (visit-fun term)
      (rewrite-cps-call term
        (($ $fun meta self free entries)
         ($fun meta self free ,(map visit-cont entries)))))
    (define (visit-cont cont)
      (rewrite-cps-cont cont
        (($ $cont sym src ($ $kargs names syms body))
         (sym src ($kargs names syms ,(visit-term body))))
        (($ $cont sym src ($ $kentry arity tail body))
         (sym src ($kentry ,arity ,tail ,(visit-cont body))))
        (($ $cont)
         ,cont)))
    (define (visit-term term)
      (match term
        (($ $letk conts body)
         ;; Visit the body first, so we visit depth-first.
         (let ((body (visit-term body)))
           (build-cps-term
             ($letk ,(map visit-cont conts) ,body))))
        (($ $letrec names syms funs body)
         (let ((nsf (map list names syms funs)))
           (define recursive?
             (match-lambda
              ((n s ($ $fun meta self free (($ $cont entry) ...)))
               (and-map (lambda (k)
                          (or-map (cut variable-used-in? <> k dfg) syms))
                        entry))))
           (call-with-values (lambda () (partition recursive? nsf))
             (lambda (rec nonrec)
               (let lp ((nonrec nonrec))
                 (match nonrec
                   (()
                    (if (null? rec)
                        (visit-term body)
                        ;; FIXME: Here contify mutually recursive sets
                        ;; of functions.
                        (rewrite-cps-term rec
                          (((name sym fun) ...)
                           ($letrec name sym (map visit-fun fun)
                                    ,(visit-term body))))))
                   (((name sym fun) . nonrec)
                    (match fun
                      (($ $fun meta self free
                          (($ $cont _ _ ($ $kentry arity
                                           ($ $cont tail-k _ ($ $ktail))
                                           (and body ($ $cont body-k))))
                           ...))
                       (if (contify-fun sym self arity tail-k body-k)
                           (visit-term
                            (build-cps-term
                              ($letk ,body
                                ,(lp nonrec))))
                           (let-gensyms (k)
                             (build-cps-term
                               ($letk ((k #f ($kargs (name) (sym)
                                               ,(lp nonrec))))
                                 ($continue k ,(visit-fun fun)))))))))))))))
        (($ $continue k exp)
         (let ((k (lookup-return-cont k)))
           (define (default)
             (rewrite-cps-term exp
               (($ $fun) ($continue k ,(visit-fun exp)))
               (_ ($continue k ,exp))))
           (match exp
             (($ $fun meta self free
                 (($ $cont _ _ ($ $kentry arity
                                  ($ $cont tail-k _ ($ $ktail))
                                  (and body ($ $cont body-k))))
                  ...))
              (if (and=> (bound-symbol k)
                         (lambda (sym)
                           (contify-fun sym self arity tail-k body-k)))
                  (visit-term (build-cps-term
                                ($letk ,body
                                  ,(match (lookup-cont k cont-table)
                                     (($ $kargs (_) (_) body)
                                      body)))))
                  (default)))
             (($ $call proc args)
              (or (contify-call proc args)
                  (default)))
             (_ (default)))))))

    (let ((fun (visit-fun fun)))
      (if (null? call-substs)
          fun
          ;; Iterate to fixed point.
          (contify fun)))))
