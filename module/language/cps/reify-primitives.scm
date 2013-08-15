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

(define (make-$let1k cont body)
  (make-$letk (list cont) body))

(define (make-$let1v src k name sym cont-body body)
  (make-$let1k (make-$cont src k (make-$kargs (list name) (list sym) cont-body))
               body))

(define (make-let src val-proc body-proc)
  (let ((k (gensym "k")) (sym (gensym "v")))
    (make-$let1v src k 'tmp sym (body-proc sym) (val-proc k))))

(define (make-$let1c src name sym val cont-body)
  (let ((k (gensym "kconst")))
    (make-$let1v src k name sym cont-body (make-$continue k (make-$const val)))))

(define (fold-conts proc seed term)
  (match term
    (($ $fun meta self free body)
     (fold-conts proc seed body))

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

    (($ $cont src sym ($ $kentry arity body alternate))
     (let ((seed (fold-conts proc (proc term seed) body)))
       (if alternate
           (fold-conts proc seed alternate)
           seed)))

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
  (let ((module-sym (gensym "module"))
        (name-sym (gensym "name"))
        (public?-sym (gensym "public?"))
        (bound?-sym (gensym "bound?")))
    (make-$let1c
     src 'module module-sym module
     (make-$let1c
      src 'name name-sym name
      (make-$let1c
       src 'public? public?-sym public?
       (make-$let1c
        src 'bound? bound?-sym bound?
        (make-let
         src
         (lambda (k)
           (make-$continue k (make-$primcall
                              'cached-module-box
                              (list module-sym name-sym public?-sym bound?-sym))))
         val-proc)))))))

(define (primitive-ref name k)
  (module-box #f '(guile) name #f #t
              (lambda (box)
                (make-$continue k (make-$primcall 'box-ref (list box))))))

(define (reify-primitives fun)
  (let ((conts (build-cont-table fun)))
    (define (visit-fun term)
      (match term
        (($ $fun meta self free body)
         (make-$fun meta self free (visit-entry body)))))
    (define (visit-entry term)
      (match term
        (($ $cont src sym ($ $kentry arity body alternate))
         (make-$cont src sym
                     (make-$kentry arity (visit-cont body)
                                   (and alternate
                                        (visit-entry alternate)))))))
    (define (visit-cont term)
      (match term
        (($ $cont src sym ($ $kargs names syms body))
         (make-$cont src sym (make-$kargs names syms (visit-term body))))
        (_ term)))
    (define (visit-term term)
      (match term
        (($ $letk conts body)
         (make-$letk (map visit-cont conts) (visit-term body)))
        (($ $continue k exp)
         (match exp
           (($ $prim name)
            (match (lookup-cont conts k)
              (($ $kargs (_)) (primitive-ref name k))
              (_ (make-$continue k (make-$void)))))
           (($ $fun)
            (make-$continue k (visit-fun exp)))
           (($ $primcall name args)
            (cond
             ((or (prim-rtl-instruction name) (branching-primitive? name))
              ;; Assume arities are correct.
              term)
             (else
              (make-let #f
                        (lambda (k)
                          (primitive-ref name k))
                        (lambda (v)
                          (make-$continue k (make-$call v args)))))))
           (_ term)))))

    (visit-fun fun)))
