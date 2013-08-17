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

(define-module (language cps arities)
  #:use-module (ice-9 match)
  #:use-module ((srfi srfi-1) #:select (fold))
  #:use-module (srfi srfi-26)
  #:use-module (language cps)
  #:use-module (language cps dfg)
  #:use-module (language cps primitives)
  #:export (fix-arities))

(define (fix-entry-arities entry)
  (let ((conts (build-local-cont-table entry))
        (ktail (match entry
                 (($ $cont _ _ ($ $kentry _ ($ $cont ktail _ ($ $ktail))))
                  ktail))))
    (define (visit-term term)
      (rewrite-cps-term term
        (($ $letk conts body)
         ($letk ,(map visit-cont conts) ,(visit-term body)))
        (($ $letrec names syms funs body)
         ($letrec names syms (map fix-arities funs) ,(visit-term body)))
        (($ $continue k exp)
         ,(visit-call k exp))))

    (define (adapt-call nvals k exp)
      (match nvals
        (0
         (rewrite-cps-term (lookup-cont k conts)
           (($ $ktail)
            ,(let-gensyms (kvoid kunspec unspec)
               (build-cps-term
                 ($letk* ((kunspec #f ($kargs (unspec) (unspec)
                                        ($continue k
                                          ($primcall 'return (unspec)))))
                          (kvoid #f ($kargs () ()
                                      ($continue kunspec ($values ())))))
                   ($continue kvoid ,exp)))))
           (($ $ktrunc ($ $arity () () #f () #f) kseq)
            ($continue kseq ,exp))
           (($ $kargs () () _)
            ($continue k ,exp))
           (_
            ,(let-gensyms (k*)
               (build-cps-term
                 ($letk ((k* #f ($kargs () () ($continue k ($void)))))
                   ($continue k* ,exp)))))))
        (1
         (let ((drop-result
                (lambda (kseq)
                  (let-gensyms (k* drop)
                    (build-cps-term
                      ($letk ((k* #f ($kargs ('drop) (drop)
                                       ($continue kseq ($values ())))))
                        ($continue k* ,exp)))))))
           (rewrite-cps-term (lookup-cont k conts)
             (($ $ktail)
              ,(rewrite-cps-term exp
                 (($var sym)
                  ($continue ktail ($primcall 'return (sym))))
                 (_
                  ,(let-gensyms (k* v)
                     (build-cps-term
                       ($letk ((k* #f ($kargs (v) (v)
                                        ($continue k
                                          ($primcall 'return (v))))))
                         ($continue k* ,exp)))))))
             (($ $ktrunc ($ $arity () () #f () #f) kseq)
              ,(drop-result kseq))
             (($ $kargs () () _)
              ,(drop-result k))
             (_
              ($continue k ,exp)))))))

    (define (visit-call k exp)
      (rewrite-cps-term exp
        ((or ($ $void)
             ($ $const)
             ($ $prim)
             ($ $var))
         ,(adapt-call 1 k exp))
        (($ $fun)
         ,(adapt-call 1 k (fix-arities exp)))
        (($ $call)
         ;; In general, calls have unknown return arity.  For that
         ;; reason every non-tail call has an implicit adaptor
         ;; continuation to adapt the return to the target
         ;; continuation, and we don't need to do any adapting here.
         ($continue k ,exp))
        (($ $primcall 'return (arg))
         ;; Primcalls to return are in tail position.
         ($continue ktail ,exp))
        (($ $primcall (? (lambda (name)
                           (and (not (prim-rtl-instruction name))
                                (not (branching-primitive? name))))))
         ($continue k ,exp))
        (($ $primcall name args)
         ,(match (prim-arity name)
            ((out . in)
             (if (= in (length args))
                 (adapt-call out k exp)
                 (let-gensyms (k* p*)
                   (build-cps-term
                     ($letk ((k* #f ($kargs ('prim) (p*)
                                      ($continue k ($call p* args)))))
                       ($continue k* ($prim name)))))))))
        (($ $values)
         ;; Values nodes are inserted by CPS optimization passes, so
         ;; we assume they are correct.
         ($continue k ,exp))
        (($ $prompt)
         ($continue k ,exp))))

    (define (visit-cont cont)
      (rewrite-cps-cont cont
        (($ $cont sym src ($ $kargs names syms body))
         (sym src ($kargs names syms ,(visit-term body))))
        (($ $cont)
         ,cont)))

    (rewrite-cps-cont entry
      (($ $cont sym src ($ $kentry arity tail body))
       (sym src ($kentry ,arity ,tail ,(visit-cont body)))))))

(define (fix-arities fun)
  (rewrite-cps-call fun
    (($ $fun meta self free entries)
     ($fun meta self free ,(map fix-entry-arities entries)))))

;;; Local Variables:
;;; eval: (put 'let-gensyms 'scheme-indent-function 1)
;;; eval: (put 'build-cps-term 'scheme-indent-function 0)
;;; eval: (put '$letk 'scheme-indent-function 1)
;;; eval: (put '$continue 'scheme-indent-function 1)
;;; eval: (put '$kargs 'scheme-indent-function 2)
;;; End:
