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
  #:use-module (language cps primitives)
  #:export (fix-arities))

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

(define (lookup-cont conts k)
  (and (not (eq? k 'ktail))
       (let lp ((conts conts))
         (match conts
           ((cont . conts)
            (match cont
              (($ $cont _ (? (cut eq? <> k))) cont)
              (else (lp conts))))))))

(define (fix-arities fun)
  (let ((conts (fold-conts cons '() fun)))
    (define (visit-term term)
      (rewrite-cps-term term
        (($ $letk conts body)
         ($letk ,(map visit-cont conts) ,(visit-term body)))
        (($ $letrec names syms funs body)
         ($letrec names syms (map visit-fun funs) ,(visit-term body)))
        (($ $continue k exp)
         ,(visit-call k exp))))

    (define (adapt-call nvals k exp)
      (let ((cont (lookup-cont conts k)))
        (match nvals
          (0
           (rewrite-cps-term cont
             (#f
              ,(let-gensyms (kvoid kunspec unspec)
                 (build-cps-term
                   ($letk* ((kunspec #f ($kargs (unspec) (unspec)
                                          ($continue k
                                            ($primcall 'return (unspec)))))
                            (kvoid #f ($kargs () ()
                                        ($continue kunspec ($values ())))))
                     ($continue kvoid ,exp)))))
             (($ $cont _ _ ($ $ktrunc ($ $arity () () #f () #f) kseq))
              ($continue kseq ,exp))
             (($ $cont _ _ ($ $kargs () () _))
              ($continue k ,exp))
             (($ $cont src k)
              ,(let-gensyms (k*)
                 (build-cps-term
                   ($letk ((k* src ($kargs () () ($continue k ($void)))))
                     ($continue k* ,exp)))))))
          (1
           (let ((drop-result
                  (lambda (src kseq)
                    (let-gensyms (k* drop)
                      (build-cps-term
                        ($letk ((k* src ($kargs ('drop) (drop)
                                          ($continue kseq ($values ())))))
                          ($continue k* ,exp)))))))
             (rewrite-cps-term cont
               (#f
                ,(rewrite-cps-term exp
                   (($var sym)
                    ($continue 'ktail ($primcall 'return (sym))))
                   (_
                    ,(let-gensyms (k* v)
                       (build-cps-term
                         ($letk ((k* #f ($kargs (v) (v)
                                          ($continue k
                                            ($primcall 'return (v))))))
                           ($continue k* ,exp)))))))
               (($ $cont src _ ($ $ktrunc ($ $arity () () #f () #f) kseq))
                ,(drop-result src kseq))
               (($ $cont src kseq ($ $kargs () () _))
                ,(drop-result src kseq))
               (($ $cont)
                ($continue k ,exp))))))))

    (define (visit-call k exp)
      (rewrite-cps-term exp
        ((or ($ $void)
             ($ $const)
             ($ $prim)
             ($ $var))
         ,(adapt-call 1 k exp))
        (($ $fun)
         ,(adapt-call 1 k (visit-fun exp)))
        (($ $call)
         ;; In general, calls have unknown return arity.  For that
         ;; reason every non-tail call has an implicit adaptor
         ;; continuation to adapt the return to the target
         ;; continuation, and we don't need to do any adapting here.
         ($continue k ,exp))
        (($ $primcall 'return (arg))
         ;; Primcalls to return are in tail position.
         ($continue 'ktail ,exp))
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

    (define (visit-fun fun)
      (rewrite-cps-call fun
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

    (visit-fun fun)))
