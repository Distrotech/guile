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

(define-module (language cps closure-conversion)
  #:use-module (ice-9 match)
  #:use-module ((srfi srfi-1) #:select (fold lset-union lset-difference))
  #:use-module (ice-9 receive)
  #:use-module (srfi srfi-26)
  #:use-module (language cps)
  #:export (convert-closures))

(define (union s1 s2)
  (lset-union eq? s1 s2))

(define (difference s1 s2)
  (lset-difference eq? s1 s2))

(define (make-$let1k cont body)
  (make-$letk (list cont) body))

(define (make-$let1v src k name sym cont-body body)
  (make-$let1k (make-$cont src k (make-$kargs (list name) (list sym) cont-body))
               body))

(define (make-$letk* conts body)
  (match conts
    (() body)
    ((cont . conts)
     (make-$let1k cont (make-$letk* conts body)))))

;; bound := sym ...
;; free := sym ...

(define (convert-free-var sym self bound k)
  "Convert one possibly free variable reference to a bound reference.

If @var{sym} is free (i.e., not present in @var{bound},), it is replaced
by a closure reference via a @code{free-ref} primcall, and @var{k} is
called with the new var.  Otherwise @var{sym} is bound, so @var{k} is
called with @var{sym}.

@var{k} should return two values: a term and a list of additional free
values in the term."
  (if (memq sym bound)
      (k sym)
      (let* ((k* (gensym "k"))
             (sym* (gensym "v")))
        (receive (exp free) (k sym*)
          (values (make-$let1v
                   #f k* sym* sym* exp
                   (make-$continue k* (make-$primcall 'free-ref (list self sym))))
                  (cons sym free))))))
  
(define (convert-free-vars syms self bound k)
  "Convert a number of possibly free references to bound references.
@var{k} is called with the bound references, and should return two
values: the term and a list of additional free variables in the term."
  (match syms
    (() (k '()))
    ((sym . syms)
     (convert-free-var sym self bound
                       (lambda (sym)
                         (convert-free-vars syms self bound
                                            (lambda (syms)
                                              (k (cons sym syms)))))))))
  
(define (init-closure src v free body)
  "Initialize the free variables in a closure bound to @var{sym}, and
continue with @var{body}."
  (fold (lambda (free body)
          (let ((k (gensym "k")))
            (make-$let1k
             (make-$cont src k (make-$kargs '() '() body))
             (make-$continue k (make-$primcall 'free-set! (list v free))))))
        body
        free))

;; Closure conversion.
(define (cc exp self bound)
  "Convert all free references in @var{exp} to bound references, and
convert functions to flat closures."
  (match exp
    (($ $letk conts body)
     (let lp ((conts conts) (conts* '()) (free '()))
       (match conts
         (()
          (receive (body free*) (cc body self bound)
            (values (make-$letk (reverse conts*) body)
                    (union free free*))))
         ((cont . conts)
          (receive (cont* free*) (cc cont self bound)
            (lp conts (cons cont* conts*) (union free free*)))))))

    (($ $cont src sym ($ $kargs names syms body))
     (receive (body free) (cc body self (append syms bound))
       (values (make-$cont src sym (make-$kargs names syms body))
               free)))

    (($ $cont src sym ($ $kentry arity body alternate))
     (receive (body free) (cc body self bound)
       (receive (alternate free*)
           (if alternate (cc alternate self bound) (values #f '()))
         (values (make-$cont src sym (make-$kentry arity body alternate))
                 (union free free*)))))

    (($ $cont)
     ;; Other kinds of continuations don't bind values and don't have
     ;; bodies.
     (values exp '()))

    ;; Remove letrec.
    (($ $letrec names syms funs body)
     (let ((bound (append bound syms)))
       (receive (body free) (cc body self bound)
         (let lp ((in (map list names syms funs))
                  (bindings (lambda (body) body))
                  (body body)
                  (free free))
           (match in
             (() (values (bindings body) free))
             (((name sym ($ $fun meta self () fun-body)) . in)
              (receive (fun-body fun-free) (cc fun-body self (list self))
                (lp in
                    (lambda (body)
                      (let ((k (gensym "k")))
                        (make-$let1v
                         #f k name sym (bindings body)
                         (make-$continue k (make-$fun meta self fun-free fun-body)))))
                    (init-closure #f sym fun-free body)
                    (union free (difference fun-free bound))))))))))

    (($ $continue k ($ $var sym))
     (convert-free-var sym self bound
                       (lambda (sym)
                         (values (make-$continue k (make-$var sym))
                                 '()))))

    (($ $continue k
        (or ($ $void)
            ($ $const)
            ($ $prim)))
     (values exp '()))

    (($ $continue k ($ $fun meta self () body))
     (receive (body free) (cc body self (list self))
       (match free
         (()
          (values (make-$continue k (make-$fun meta self free body))
                  free))
         (else
          (values
           (let ((kinit (gensym "kinit"))
                 (v (gensym "v")))
             (make-$let1v
              #f kinit v v
              (init-closure #f v free
                            (make-$continue k (make-$var v)))
              (make-$continue kinit (make-$fun meta self free body))))
           (difference free bound))))))

    (($ $continue k ($ $call proc args))
     (convert-free-vars (cons proc args) self bound
                        (match-lambda
                         ((proc . args)
                          (values (make-$continue k (make-$call proc args))
                                  '())))))

    (($ $continue k ($ $primcall name args))
     (convert-free-vars args self bound
                        (lambda (args)
                          (values (make-$continue k (make-$primcall name args))
                                  '()))))

    (($ $continue k ($ $values args))
     (convert-free-vars args self bound
                        (lambda (args)
                          (values (make-$continue k (make-$values args))
                                  '()))))

    (($ $continue k ($ $prompt escape? tag handler))
     (convert-free-var
      tag self bound
      (lambda (tag)
        (values (make-$continue k (make-$prompt escape? tag handler))
                '()))))

    (_ (error "what" exp))))

(define (convert-closures exp)
  "Convert free reference in @var{exp} to primcalls to @code{free-ref},
and allocate and initialize flat closures."
  (match exp
    (($ $fun meta self () body)
     (receive (body free) (cc body #f '())
       (unless (null? free)
         (error "Expected no free vars in toplevel thunk" exp))
       (make-$fun meta self '() body)))))
