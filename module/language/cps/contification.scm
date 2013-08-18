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
  #:use-module ((srfi srfi-1) #:select (concatenate))
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

    (define (contify-fun term-k sym self arities tails bodies)
      (contify-funs term-k
                    (list sym) (list self) (list arities) (list tails)
                    (list bodies)))

    (define (contify-funs term-k syms selfs arities tails bodies)
      ;; Are the given args compatible with any of the arities?
      (define (applicable? proc args)
        (or-map (match-lambda
                 (($ $arity req () #f () #f)
                  (= (length args) (length req)))
                 (_ #f))
                (assq-ref (map cons syms arities) proc)))

      ;; If the use of PROC in continuation USE is a call to PROC that
      ;; is compatible with one of the procedure's arities, return the
      ;; target continuation.  Otherwise return #f.
      (define (call-target use proc)
        (match (find-call (lookup-cont use cont-table))
          (($ $continue k ($ $call proc* args))
           (and (eq? proc proc*) (not (memq proc args)) (applicable? proc args)
                k))
          (_ #f)))

      (and
       (and-map null? (map (cut lookup-uses <> dfg) selfs))
       (and=> (let visit-syms ((syms syms) (k #f))
                (match syms
                  (() k)
                  ((sym . syms)
                   (let visit-uses ((uses (lookup-uses sym dfg)) (k k))
                     (match uses
                       (() (visit-syms syms k))
                       ((use . uses)
                        (and=> (call-target use sym)
                               (lambda (k*)
                                 (cond
                                  ((or-map (cut memq k* <>) tails)
                                   (visit-uses uses k))
                                  ((not k) (visit-uses uses k*))
                                  ((eq? k k*) (visit-uses uses k))
                                  (else #f))))))))))
              (lambda (k)
                ;; We have a common continuation, so we contify: mark
                ;; all SYMs for replacement in calls, and mark the tail
                ;; continuations for replacement by K.
                (for-each (lambda (sym arities tails bodies)
                            (for-each (cut lift-definition! <> term-k dfg)
                                      bodies)
                            (subst-call! sym arities bodies)
                            (for-each (cut subst-return! <> k) tails))
                          syms arities tails bodies)
                k))))

    ;; This is a first cut at a contification algorithm.  It contifies
    ;; non-recursive functions that only have positional arguments.
    (define (visit-fun term)
      (rewrite-cps-call term
        (($ $fun meta self free entries)
         ($fun meta self free ,(map visit-cont entries)))))
    (define (visit-cont cont)
      (rewrite-cps-cont cont
        (($ $cont sym src ($ $kargs names syms body))
         (sym src ($kargs names syms ,(visit-term body sym))))
        (($ $cont sym src ($ $kentry arity tail body))
         (sym src ($kentry ,arity ,tail ,(visit-cont body))))
        (($ $cont)
         ,cont)))
    (define (visit-term term term-k)
      (match term
        (($ $letk conts body)
         ;; Visit the body first, so we visit depth-first.
         (let ((body (visit-term body term-k)))
           (build-cps-term
             ($letk ,(map visit-cont conts) ,body))))
        (($ $letrec names syms funs body)
         (define (split-components nsf)
           ;; FIXME: Compute strongly-connected components.  Currently
           ;; we just put non-recursive functions in their own
           ;; components, and lump everything else in the remaining
           ;; component.
           (define (recursive? k)
             (or-map (cut variable-used-in? <> k dfg) syms))
           (let lp ((nsf nsf) (rec '()))
             (match nsf
               (()
                (if (null? rec)
                    '()
                    (list rec)))
               (((and elt (n s ($ $fun meta self free (($ $cont entry) ...))))
                 . nsf)
                (if (or-map recursive? entry)
                    (lp nsf (cons elt rec))
                    (cons (list elt) (lp nsf rec)))))))
         (define (visit-components components)
           (match components
             (() (visit-term body term-k))
             ((((name sym fun) ...) . components)
              (match fun
                ((($ $fun meta self free
                     (($ $cont _ _ ($ $kentry arity
                                      ($ $cont tail-k _ ($ $ktail))
                                      (and body ($ $cont body-k))))
                      ...)) ...)
                 (if (contify-funs term-k sym self arity tail-k body-k)
                     (let ((body* (visit-components components)))
                       (build-cps-term
                         ($letk ,(map visit-cont (concatenate body))
                           ,body*)))
                     (let-gensyms (k)
                       (build-cps-term
                         ($letrec names syms (map visit-fun fun)
                                  ,(visit-components components))))))))))
         (visit-components (split-components (map list names syms funs))))
        (($ $continue k exp)
         (let ((k* (lookup-return-cont k)))
           (define (default)
             (rewrite-cps-term exp
               (($ $fun) ($continue k* ,(visit-fun exp)))
               (($ $primcall 'return (val))
                ,(if (eq? k k*)
                     (build-cps-term ($continue k* ,exp))
                     (build-cps-term ($continue k* ($values (val))))))
               (($ $primcall 'return-values vals)
                ,(if (eq? k k*)
                     (build-cps-term ($continue k* ,exp))
                     (build-cps-term ($continue k* ($values vals)))))
               (_ ($continue k* ,exp))))
           (match exp
             (($ $fun meta self free
                 (($ $cont _ _ ($ $kentry arity
                                  ($ $cont tail-k _ ($ $ktail))
                                  (and body ($ $cont body-k))))
                  ...))
              (if (and=> (bound-symbol k*)
                         (lambda (sym)
                           (contify-fun term-k sym self arity tail-k body-k)))
                  (visit-term (build-cps-term
                                ($letk ,body
                                  ,(match (lookup-cont k cont-table)
                                     (($ $kargs (_) (_) body)
                                      body))))
                              term-k)
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
