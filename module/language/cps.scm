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
;;; This is the continuation-passing style (CPS) intermediate language
;;; (IL) for Guile.  It is a lower-level representation than Tree-IL, in
;;; that it assumes that some Tree-IL concepts have already been
;;; compiled away.  For example, CPS fixes the order of evaluation,
;;; requires that Scheme's <letrec> has already been lowered to <fix>,
;;; inlines default-value initializers into lambda-case expressions, and
;;; inlines prompt bodies.
;;;
;;; The utility of CPS is that it gives a name to everything: every
;;; intermediate value, and every control point (continuation).  As such
;;; it is more verbose than Tree-IL, but at the same time more simple as
;;; the number of concepts is reduced.
;;;
;;; There are two kinds of terms in CPS: terms that bind continuations,
;;; and terms that call continuations.  $letk binds a set of mutually
;;; recursive continuations, each one an instance of $cont.  A $cont
;;; declares the name and source of a continuation, and then contains as
;;; a subterm the particular continuation instance: $kif for test
;;; continuations, $kargs for continuations that bind values, etc.
;;;
;;; $continue nodes call continuations.  The expression contained in the
;;; $continue node determines the value or values that are passed to the
;;; target continuation: $const to pass a constant value, $values to
;;; pass multiple named values, etc.
;;;
;;; Code:

(define-module (language cps)
  #:use-module (ice-9 match)
  #:use-module ((srfi srfi-1) #:select (fold))
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-9 gnu)
  #:export (;; Continuations.
            $letk $cont $kif $ktrunc $kargs $kentry

            ;; Calls.
            $continue
            $var $void $const $prim
            $fun $arity $letrec
            $call $primcall $values $prompt

            ;; Constructors.
            make-$letk make-$cont
            make-$kif make-$ktrunc make-$kargs make-$kentry

            make-$fun make-$arity make-$letrec

            make-$continue
            make-$var make-$void make-$const make-$prim
            make-$call make-$primcall make-$values make-$prompt

            parse-cps
            unparse-cps

            ;; Building macros.
            let-gensyms
            build-cps-term
            build-cps-call
            build-cps-cont))

;; FIXME: Use SRFI-99, when Guile adds it.
(define-syntax define-record-type*
  (lambda (x)
    (define (id-append ctx . syms)
      (datum->syntax ctx (apply symbol-append (map syntax->datum syms))))
    (syntax-case x ()
      ((_ name field ...)
       (and (identifier? #'name) (and-map identifier? #'(field ...)))
       (with-syntax ((cons (id-append #'name #'make- #'name))
                     (pred (id-append #'name #'name #'?))
                     ((getter ...) (map (lambda (f)
                                          (id-append f #'name #'- f))
                                        #'(field ...))))
         #'(define-record-type name
             (cons field ...)
             pred
             (field getter)
             ...))))))

(define-syntax-rule (define-cps-type name field ...)
  (begin
    (define-record-type* name field ...)
    (set-record-type-printer! name print-cps)))

(define (print-cps exp port)
  (format port "#<cps ~S>" (unparse-cps exp)))

;; Helper.
(define-record-type* $arity req opt rest kw allow-other-keys?)

;; Continuations.
(define-cps-type $letk conts body)
(define-cps-type $cont src k cont)
(define-cps-type $kif kt kf)
(define-cps-type $ktrunc arity k)
(define-cps-type $kargs names syms body)
(define-cps-type $kentry arity cont)

;; Calls.
(define-cps-type $continue k exp)
(define-cps-type $var sym)
(define-cps-type $void)
(define-cps-type $const val)
(define-cps-type $prim name)
(define-cps-type $fun meta self free entries)
(define-cps-type $letrec names syms funs body)
(define-cps-type $call proc args)
(define-cps-type $primcall name args)
(define-cps-type $values args)
(define-cps-type $prompt escape? tag handler)

(define (parse-cps exp)
  (define (src exp)
    (let ((props (source-properties exp)))
      (and (pair? props) props)))
  (match exp
    ;; Continuations.
    (('let k (name sym val) body)
     (make-$letk (list (make-$cont (src exp) k
                                (make-$kargs (list name) (list sym)
                                             (parse-cps body))))
                 (parse-cps val)))
    (('letk (cont ...) body)
     (make-$letk (map parse-cps cont) (parse-cps body)))
    (('k sym body)
     (make-$cont (src exp) sym (parse-cps body)))
    (('kif kt kf)
     (make-$kif kt kf))
    (('ktrunc req rest k)
     (make-$ktrunc (make-$arity req '() rest '() #f) k))
    (('kargs names syms body)
     (make-$kargs names syms (parse-cps body)))
    (('kentry (req opt rest kw allow-other-keys?) body)
     (make-$kentry (make-$arity req opt rest kw allow-other-keys?)
                   (parse-cps body)))
    (('kseq body)
     (make-$kargs '() '() (parse-cps body)))

    ;; Calls.
    (('continue k exp)
     (make-$continue k (parse-cps exp)))
    (('var sym)
     (make-$var sym))
    (('void)
     (make-$void))
    (('const exp)
     (make-$const exp))
    (('prim name)
     (make-$prim name))
    (('fun meta self free entries)
     (make-$fun meta self free (map parse-cps entries)))
    (('letrec ((name sym fun) ...) body)
     (make-$letrec name sym (map parse-cps fun) (parse-cps body)))
    (('call proc arg ...)
     (make-$call proc arg))
    (('primcall name arg ...)
     (make-$primcall name arg))
    (('values arg ...)
     (make-$values arg))
    (('prompt escape? tag handler)
     (make-$prompt escape? tag handler))
    (_
     (error "unexpected cps" exp))))

(define (unparse-cps exp)
  (match exp
    ;; Continuations.
    (($ $letk (($ $cont src k ($ $kargs (name) (sym) body))) val)
     `(let ,k (,name ,sym ,(unparse-cps val))
           ,(unparse-cps body)))
    (($ $letk conts body)
     `(letk ,(map unparse-cps conts) ,(unparse-cps body)))
    (($ $cont src sym body)
     `(k ,sym ,(unparse-cps body)))
    (($ $kif kt kf)
     `(kif ,kt ,kf))
    (($ $ktrunc ($ $arity req () rest '() #f) k)
     `(ktrunc ,req ,rest ,k))
    (($ $kargs () () body)
     `(kseq ,(unparse-cps body)))
    (($ $kargs names syms body)
     `(kargs ,names ,syms ,(unparse-cps body)))
    (($ $kentry ($ $arity req opt rest kw allow-other-keys?) body)
     `(kentry (,req ,opt ,rest ,kw ,allow-other-keys?)
              ,(unparse-cps body)))

    ;; Calls.
    (($ $continue k exp)
     `(continue ,k ,(unparse-cps exp)))
    (($ $var sym)
     `(var ,sym))
    (($ $void)
     `(void))
    (($ $const val)
     `(const ,val))
    (($ $prim name)
     `(prim ,name))
    (($ $fun meta self free entries)
     `(fun ,meta ,self ,free ,(map unparse-cps entries)))
    (($ $letrec names syms funs body)
     `(letrec ,(map (lambda (name sym fun)
                      (list name sym (unparse-cps fun)))
                    names syms funs)
        ,(unparse-cps body)))
    (($ $call proc args)
     `(call ,proc ,@args))
    (($ $primcall name args)
     `(primcall ,name ,@args))
    (($ $values args)
     `(values ,@args))
    (($ $prompt escape? tag handler)
     `(prompt ,escape? ,tag ,handler))
    (_
     (error "unexpected cps" exp))))

;; FIXME: Figure out how to evaluate this automatically when Emacs
;; visits this buffer.
;;
;; (put 'let-gensyms 'scheme-indent-function 1)
;; (put 'build-cps-term 'scheme-indent-function 0)
;; (put 'build-cps-call 'scheme-indent-function 0)
;; (put 'build-cps-cont 'scheme-indent-function 0)
;; (put '$letk 'scheme-indent-function 1)
;; (put '$letk* 'scheme-indent-function 1)
;; (put '$letconst 'scheme-indent-function 1)
;; (put '$continue 'scheme-indent-function 1)
;; (put '$kargs 'scheme-indent-function 2)

(define-syntax let-gensyms
  (syntax-rules ()
    ((_ (sym ...) body body* ...)
     (let ((sym (gensym (symbol->string 'sym))) ...)
       body body* ...))))

(define-syntax build-arity
  (syntax-rules (unquote)
    ((_ (unquote exp)) exp)
    ((_ (req opt rest kw allow-other-keys?))
     (make-$arity req opt rest kw allow-other-keys?))))

(define-syntax build-cont-body
  (syntax-rules (unquote $kif $ktrunc $kargs $kentry)
    ((_ (unquote exp))
     exp)
    ((_ ($kif kt kf))
     (make-$kif kt kf))
    ((_ ($ktrunc req rest kargs))
     (make-$ktrunc (make-$arity req '() rest '() #f) kargs))
    ((_ ($kargs (name ...) (sym ...) body))
     (make-$kargs (list name ...) (list sym ...) (build-cps-term body)))
    ((_ ($kargs names syms body))
     (make-$kargs names syms (build-cps-term body)))
    ((_ ($kentry arity cont))
     (make-$kentry (build-arity arity) (build-cps-cont cont)))))

(define-syntax build-cps-cont
  (syntax-rules (unquote)
    ((_ (unquote exp)) exp)
    ((_ (k src cont)) (make-$cont src k (build-cont-body cont)))))

(define-syntax build-cps-call
  (syntax-rules (unquote
                 $var $void $const $prim $fun $call $primcall $values $prompt)
    ((_ (unquote exp)) exp)
    ((_ ($var sym)) (make-$var sym))
    ((_ ($void)) (make-$void))
    ((_ ($const val)) (make-$const val))
    ((_ ($prim name)) (make-$prim name))
    ((_ ($fun meta self free (unquote entries)))
     (make-$fun meta self free entries))
    ((_ ($fun meta self free (entry ...)))
     (make-$fun meta self free (list (build-cps-cont entry) ...)))
    ((_ ($call proc (arg ...))) (make-$call proc (list arg ...)))
    ((_ ($call proc args)) (make-$call proc args))
    ((_ ($primcall name (arg ...))) (make-$primcall name (list arg ...)))
    ((_ ($primcall name args)) (make-$primcall name args))
    ((_ ($values (arg ...))) (make-$values (list arg ...)))
    ((_ ($values args)) (make-$values args))
    ((_ ($prompt escape? tag handler)) (make-$prompt escape? tag handler))))

(define-syntax build-cps-term
  (syntax-rules (unquote $letk $letk* $letconst $letrec $continue)
    ((_ (unquote exp))
     exp)
    ((_ ($letk (unquote conts) body))
     (make-$letk conts (build-cps-term body)))
    ((_ ($letk (cont ...) body))
     (make-$letk (list (build-cps-cont cont) ...)
                 (build-cps-term body)))
    ((_ ($letk* () body))
     (build-cps-term body))
    ((_ ($letk* (cont conts ...) body))
     (build-cps-term ($letk (cont) ($letk* (conts ...) body))))
    ((_ ($letconst () body))
     (build-cps-term body))
    ((_ ($letconst ((name sym val) tail ...) body))
     (let-gensyms (kconst)
       (build-cps-term
         ($letk ((kconst #f ($kargs (name) (sym) ($letconst (tail ...) body))))
           ($continue kconst ($const val))))))
    ((_ ($letrec names gensyms funs body))
     (make-$letrec names gensyms funs (build-cps-term body)))
    ((_ ($continue k exp))
     (make-$continue k (build-cps-call exp)))))
