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
  #:use-module ((srfi srfi-1) #:select (fold
                                        lset-union lset-difference
                                        list-index))
  #:use-module (ice-9 receive)
  #:use-module (srfi srfi-26)
  #:use-module (language cps)
  #:export (convert-closures))

(define (union s1 s2)
  (lset-union eq? s1 s2))

(define (difference s1 s2)
  (lset-difference eq? s1 s2))

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
      (let-gensyms (k* sym*)
        (receive (exp free) (k sym*)
          (values (build-cps-term
                    ($letk ((k* #f ($kargs (sym*) (sym*) ,exp)))
                      ($continue k* ($primcall 'free-ref (self sym)))))
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
  (fold (lambda (free idx body)
          (let-gensyms (k k* idxsym)
            (build-cps-term
              ($letk ((k src ($kargs () () ,body)))
                ($letk ((k* src ($kargs ('idx) (idxsym)
                                  ($continue k
                                    ($primcall 'free-set! (v idxsym free))))))
                  ($continue k* ($const idx)))))))
        body
        free
        (iota (length free))))

(define (cc* exps self bound)
  "Convert all free references in the list of expressions @var{exps} to
bound references, and convert functions to flat closures.  Returns two
values: the transformed list, and a cumulative set of free variables."
  (let lp ((exps exps) (exps* '()) (free '()))
    (match exps
      (() (values (reverse exps*) free))
      ((exp . exps)
       (receive (exp* free*) (cc exp self bound)
         (lp exps (cons exp* exps*) (union free free*)))))))

;; Closure conversion.
(define (cc exp self bound)
  "Convert all free references in @var{exp} to bound references, and
convert functions to flat closures."
  (match exp
    (($ $letk conts body)
     (receive (conts free) (cc* conts self bound)
       (receive (body free*) (cc body self bound)
         (values (make-$letk conts body)
                 (union free free*)))))

    (($ $cont src sym ($ $kargs names syms body))
     (receive (body free) (cc body self (append syms bound))
       (values (build-cps-cont (sym src ($kargs names syms ,body)))
               free)))

    (($ $cont src sym ($ $kentry arity body))
     (receive (body free) (cc body self bound)
       (values (build-cps-cont (sym src ($kentry ,arity ,body)))
               free)))

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
             (((name sym ($ $fun meta self () entries)) . in)
              (receive (entries fun-free) (cc* entries self (list self))
                (lp in
                    (lambda (body)
                      (let-gensyms (k)
                        (build-cps-term
                          ($letk ((k #f ($kargs (name) (sym) ,(bindings body))))
                            ($continue k ($fun meta self fun-free ,entries))))))
                    (init-closure #f sym fun-free body)
                    (union free (difference fun-free bound))))))))))

    (($ $continue k ($ $var sym))
     (convert-free-var sym self bound
                       (lambda (sym)
                         (values (build-cps-term ($continue k ($var sym)))
                                 '()))))

    (($ $continue k
        (or ($ $void)
            ($ $const)
            ($ $prim)))
     (values exp '()))

    (($ $continue k ($ $fun meta self () entries))
     (receive (entries free) (cc* entries self (list self))
       (match free
         (()
          (values (build-cps-term ($continue k ($fun meta self free ,entries)))
                  free))
         (else
          (values
           (let-gensyms (kinit v)
             (build-cps-term
               ($letk ((kinit #f ($kargs (v) (v)
                                   ,(init-closure #f v free
                                                  (build-cps-term
                                                    ($continue k ($var v)))))))
                 ($continue kinit ($fun meta self free ,entries)))))
           (difference free bound))))))

    (($ $continue k ($ $call proc args))
     (convert-free-vars (cons proc args) self bound
                        (match-lambda
                         ((proc . args)
                          (values (build-cps-term
                                    ($continue k ($call proc args)))
                                  '())))))

    (($ $continue k ($ $primcall name args))
     (convert-free-vars args self bound
                        (lambda (args)
                          (values (build-cps-term
                                    ($continue k ($primcall name args)))
                                  '()))))

    (($ $continue k ($ $values args))
     (convert-free-vars args self bound
                        (lambda (args)
                          (values (build-cps-term
                                    ($continue k ($values args)))
                                  '()))))

    (($ $continue k ($ $prompt escape? tag handler))
     (convert-free-var
      tag self bound
      (lambda (tag)
        (values (build-cps-term
                  ($continue k ($prompt escape? tag handler)))
                '()))))

    (_ (error "what" exp))))

;; Convert the slot arguments of 'free-ref' primcalls from symbols to
;; indices.
(define (convert-to-indices exp)
  (let lpfree ((exp exp) (free '()))
    (let lp ((exp exp))
      (match exp
        (($ $letk conts body)
         (make-$letk (map lp conts) (lp body)))
        (($ $cont src sym ($ $kargs names syms body))
         (build-cps-cont (sym src ($kargs names syms ,(lp body)))))
        (($ $cont src sym ($ $kentry arity body))
         (build-cps-cont (sym src ($kentry ,arity ,(lp body)))))
        ;; Other kinds of continuations don't
        ;; bind values and don't have bodies.
        (($ $cont) exp)
        (($ $continue k ($ $primcall 'free-ref (closure sym)))
         (let ((idx (or (list-index (cut eq? <> sym) free)
                        (error "free variable not found!" sym free exp))))
           (let-gensyms (idxsym)
             (build-cps-term
               ($letconst (('idx idxsym idx))
                 ($continue k ($primcall 'free-ref (closure idxsym))))))))
        (($ $continue k ($ $fun meta self free entries))
         (build-cps-term
           ($continue k ($fun meta self free
                              ,(map (cut lpfree <> free) entries)))))
        (($ $continue) exp)))))

(define (convert-closures exp)
  "Convert free reference in @var{exp} to primcalls to @code{free-ref},
and allocate and initialize flat closures."
  (match exp
    (($ $fun meta self () entries)
     (receive (entries free) (cc* entries #f '())
       (unless (null? free)
         (error "Expected no free vars in toplevel thunk" exp entries free))
       (make-$fun meta self '() (map convert-to-indices entries))))))
