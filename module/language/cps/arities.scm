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
  #:use-module (system vm instruction)
  #:export (fix-arities))

(define (make-$let1k cont body)
  (make-$letk (list cont) body))

(define (make-$let1v src k name sym cont-body body)
  (make-$let1k (make-$cont src k (make-$kargs (list name) (list sym) cont-body))
               body))

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

(define (lookup-cont conts k)
  (and (not (eq? k 'ktail))
       (let lp ((conts conts))
         (match conts
           ((cont . conts)
            (match cont
              (($ $cont _ (? (cut eq? <> k))) cont)
              (else (lp conts))))))))

(define (compute-primcall-arity name args)
  (define (first-word-arity word)
    (case word
      ((U8_X24) 1)
      ((U8_U24) 1)
      ((U8_L24) 1)
      ((U8_U8_I16) 2)
      ((U8_U12_U12) 2)
      ((U8_U8_U8_U8) 3)))
  (define (tail-word-arity word)
    (case word
      ((U8_U24) 2)
      ((U8_L24) 2)
      ((U8_U8_I16) 3)
      ((U8_U12_U12) 3)
      ((U8_U8_U8_U8) 4)
      ((U32) 1)
      ((I32) 1)
      ((A32) 1)
      ((B32) 0)
      ((N32) 1)
      ((S32) 1)
      ((L32) 1)
      ((LO32) 1)
      ((X8_U24) 2)
      ((X8_U12_U12) 3)
      ((X8_L24) 2)
      ((B1_X7_L24) 2)
      ((B1_U7_L24) 3)
      ((B1_X31) 1)
      ((B1_X7_U24) 2)))
  (match args
    ((arg0 . args)
     (fold (lambda (arg arity)
             (+ (tail-word-arity arg) arity))
           (first-word-arity arg0)
           args))))

(define *rtl-instruction-aliases*
  '((+ . add)))

(define *macro-instruction-arities*
  '((cache-current-module! . (0 . 2))
    (cached-toplevel-box . (1 . 3))
    (cached-module-box . (1 . 4))))

(define *other-primcall-arities*
  '((eq? . (1 . 2))))

(define (compute-primcall-arities)
  (let ((table (make-hash-table)))
    (for-each
     (match-lambda
      ;; Put special cases here.
      ((name op '! . args)
       (hashq-set! table name
                   (cons 0 (compute-primcall-arity name args))))
      ((name op '<- . args)
       (hashq-set! table name
                   (cons 1 (1- (compute-primcall-arity name args))))))
     (rtl-instruction-list))
    (for-each (match-lambda
               ((name . opname)
                (hashq-set! table name (hashq-ref table opname))))
              *rtl-instruction-aliases*)
    (for-each (match-lambda
               ((name . arity)
                (hashq-set! table name arity)))
              *macro-instruction-arities*)
    (for-each (match-lambda
               ((name . arity)
                (hashq-set! table name arity)))
              *other-primcall-arities*)
    table))

(define *primcall-arities* (delay (compute-primcall-arities)))

(define (primcall-arity name)
  (or (hashq-ref (force *primcall-arities*) name)
      (error "Primcall of unknown arity" name)))

(define (fix-arities term)
  (let ((conts (fold-conts cons '() term)))
    (define (adapt nvals k proc)
      (let ((cont (lookup-cont conts k)))
        (match nvals
          (0
           (match cont
             (#f (proc k))
             (($ $cont _ _ ($ $ktrunc ($ $arity () () #f () #f) kseq))
              (proc kseq))
             (($ $cont _ _ ($ $kargs () () _))
              (proc k))
             (($ $cont src k)
              (let ((k* (gensym "kvoid")))
                (make-$letk
                 (list (make-$cont src k*
                                (make-$kargs '() '()
                                             (make-$continue k (make-$void)))))
                 (proc k*))))))
          (1
           (let ((drop-result
                  (lambda (src kseq)
                    (let ((k* (gensym "kdrop")))
                      (make-$let1v src k* 'drop (gensym "vdrop")
                                   (make-$continue kseq (make-$values '()))
                                   (proc k*))))))
             (match cont
               (#f
                (let ((k* (gensym "ktail"))
                      (v (gensym "v")))
                  (make-$let1v #f k* v v
                               (make-$continue k (make-$primcall 'return (list v)))
                               (proc k*))))
               (($ $cont src _ ($ $ktrunc ($ $arity () () #f () #f) kseq))
                (drop-result src kseq))
               (($ $cont src kseq ($ $kargs () () _))
                (drop-result src kseq))
               (($ $cont)
                (proc k))))))))

    (let lp ((term term))
      (match term
        (($ $letk conts body)
         (make-$letk (map lp conts) (lp body)))
        (($ $cont src sym ($ $kargs names syms body))
         (make-$cont src sym (make-$kargs names syms (lp body))))
        (($ $cont src sym ($ $kentry arity body alternate))
         (make-$cont src sym (make-$kentry arity (lp body)
                                           (and alternate (lp alternate)))))
        (($ $cont)
         term)
        (($ $fun meta self free body)
         (make-$fun meta self free (lp body)))
        (($ $letrec names syms funs body)
         (make-$letrec names syms (map lp funs) (lp body)))
        (($ $continue k exp)
         (match exp
           (($ $var sym)
            (if (eq? k 'ktail)
                (make-$continue k (make-$primcall 'return (list sym)))
                (adapt 1 k (lambda (k) (make-$continue k exp)))))
           ((or ($ $void)
                ($ $const)
                ($ $prim))
            (adapt 1 k (lambda (k) (make-$continue k exp))))
           (($ $fun)
            (adapt 1 k (lambda (k) (make-$continue k (lp exp)))))
           (($ $call)
            ;; In general, calls have unknown return arity.  For that
            ;; reason every non-tail call has an implicit adaptor
            ;; continuation to adapt the return to the target
            ;; continuation, and we don't need to do any adapting here.
            term)
           (($ $primcall 'return (arg))
            ;; Primcalls to return are in tail position.
            (make-$continue 'ktail exp))
           (($ $primcall name args)
            (match (primcall-arity name)
              ((out . in)
               (adapt
                out
                k
                (if (= in (length args))
                    (cut make-$continue <> exp)
                    (lambda (k)
                      (let ((k* (gensym "kprim"))
                            (p* (gensym "vprim")))
                        (make-$let1v #f k* 'prim p*
                                     (make-$continue k (make-$call p* args))
                                     (make-$continue k* (make-$prim name))))))))))
           (($ $values)
            ;; Values nodes are inserted by CPS optimization passes, so
            ;; we assume they are correct.
            term)
           (($ $prompt)
            term)))))))
