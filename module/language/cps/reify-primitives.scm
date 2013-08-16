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
;;; A pass to reify lone $prim's that were never folded into a
;;; $primcall, and $primcall's to primitives that don't have a
;;; corresponding VM op.
;;;
;;; Code:

(define-module (language cps reify-primitives)
  #:use-module (ice-9 match)
  #:use-module (ice-9 vlist)
  #:use-module ((srfi srfi-1) #:select (fold))
  #:use-module (language cps)
  #:use-module (language cps primitives)
  #:use-module (language rtl)
  #:export (reify-primitives))

;; FIXME: Some of these common utilities should be factored elsewhere,
;; perhaps (language cps).

(define (fold-conts proc seed term)
  (match term
    (($ $fun meta self free entries)
     (fold (lambda (exp seed)
             (fold-conts proc seed exp))
           seed
           entries))

    (($ $letrec names syms funs body)
     (fold-conts proc
                 (fold (lambda (exp seed)
                         (fold-conts proc seed exp))
                       seed
                       funs)
                 body))

    (($ $letk conts body)
     (fold-conts proc
                 (fold (lambda (exp seed)
                         (fold-conts proc seed exp))
                       seed
                       conts)
                 body))

    (($ $cont src sym ($ $kargs names syms body))
     (fold-conts proc (proc term seed) body))

    (($ $cont src sym ($ $kentry arity body))
     (fold-conts proc (proc term seed) body))

    (($ $cont)
     (proc term seed))

    (($ $continue k exp)
     (match exp
       (($ $fun) (fold-conts proc seed exp))
       (_ seed)))))

(define (lookup-cont table k)
  (cond
   ((vhash-assq k table) => cdr)
   (else (error "unknown cont" k))))

(define (build-cont-table term)
  (fold-conts (lambda (cont table)
                (match cont
                  (($ $cont src k cont)
                   (vhash-consq k cont table))))
              vlist-null
              term))

(define (module-box src module name public? bound? val-proc)
  (let-gensyms (module-sym name-sym public?-sym bound?-sym kbox box)
    (build-cps-term
      ($letconst (('module module-sym module)
                  ('name name-sym name)
                  ('public? public?-sym public?)
                  ('bound? bound?-sym bound?))
        ($letk ((kbox src ($kargs ('box) (box) ,(val-proc box))))
          ($continue kbox
            ($primcall 'cached-module-box
                       (module-sym name-sym public?-sym bound?-sym))))))))

(define (primitive-ref name k)
  (module-box #f '(guile) name #f #t
              (lambda (box)
                (build-cps-term
                  ($continue k ($primcall 'box-ref (box)))))))

(define (reify-primitives fun)
  (let ((conts (build-cont-table fun)))
    (define (visit-fun term)
      (rewrite-cps-call term
        (($ $fun meta self free entries)
         ($fun meta self free ,(map visit-cont entries)))))
    (define (visit-cont cont)
      (rewrite-cps-cont cont
        (($ $cont src sym ($ $kargs names syms body))
         (sym src ($kargs names syms ,(visit-term body))))
        (($ $cont src sym ($ $kentry arity body))
         (sym src ($kentry ,arity ,(visit-cont body))))
        (($ $cont)
         ,cont)))
    (define (visit-term term)
      (rewrite-cps-term term
        (($ $letk conts body)
         ($letk ,(map visit-cont conts) ,(visit-term body)))
        (($ $continue k exp)
         ,(match exp
            (($ $prim name)
             (match (lookup-cont conts k)
               (($ $kargs (_)) (primitive-ref name k))
               (_ (build-cps-term ($continue k ($void))))))
            (($ $fun)
             (build-cps-term ($continue k ,(visit-fun exp))))
            (($ $primcall name args)
             (cond
              ((or (prim-rtl-instruction name) (branching-primitive? name))
               ;; Assume arities are correct.
               term)
              (else
               (let-gensyms (k* v)
                 (build-cps-term
                   ($letk ((k* #f ($kargs (v) (v)
                                    ($continue k ($call v args)))))
                     ,(primitive-ref name k*)))))))
            (_ term)))))

    (visit-fun fun)))
