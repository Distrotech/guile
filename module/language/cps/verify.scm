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

(define-module (language cps verify)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-26)
  #:use-module (language cps)
  #:export (verify-cps))

(define (verify-cps exp)
  (define seen-gensyms (make-hash-table))
  (define (add sym env)
    (if (hashq-ref seen-gensyms sym)
        (error "duplicate gensym" sym)
        (begin
          (hashq-set! seen-gensyms sym #t)
          (cons sym env))))
  (define (add-env new env)
    (if (null? new)
        env
        (add-env (cdr new) (add (car new) env))))
  (define (check-var sym env)
    (cond
     ((not (hashq-ref seen-gensyms sym))
      (error "unbound lexical" sym))
     ((not (memq sym env))
      (error "displaced lexical" sym))))
  (define (check-src src)
    (if (and src (not (and (list? src) (and-map pair? src)
                           (and-map symbol? (map car src)))))
        (error "bad src")))

  (let visit ((exp exp)
              (k-env '())
              (v-env '()))
    (match exp
      ;; Continuations.
      (($ $letk (($ $cont src k cont) ...) body)
       (let ((k-env (add-env k k-env)))
         (for-each check-src src)
         (for-each (match-lambda
                    (($ $kif kt kf)
                     (check-var kt k-env)
                     (check-var kf k-env))
                    (($ $ktrunc ($ $arity req () rest () #f) k)
                     (unless (and (list? req) (and-map symbol? req))
                       (error "bad arity req" req))
                     (when rest
                       (unless (symbol? rest)
                         (error "bad arity rest" rest)))
                     (check-var k k-env))
                    (($ $kargs names syms body)
                     (unless (and (list? names) (and-map symbol? names))
                       (error "names should be list of symbols" names))
                     (unless (list? syms)
                       (error "syms should be list" names))
                     (visit body k-env (add-env syms v-env)))
                    ;; $kentry is only ever seen in $fun.
                    )
                   cont)
         (visit body k-env v-env)))

      ;; Calls.
      (($ $continue k exp)
       (check-var k k-env)
       (match exp
         (($ $var sym)
          (check-var sym v-env))
         (($ $void)
          #t)
         (($ $const val)
          #t)
         (($ $prim name)
          (unless (symbol? name) (error "name should be a symbol" exp)))
         (($ $fun meta self free entries)
          (when (and meta (not (and (list? meta) (and-map pair? meta))))
            (error "meta should be alist" meta))
          (unless (symbol? self)
            (error "self should be symbol" exp))
          (unless (and (list? free) (and-map symbol? list))
            (error "free should be list of symbols" exp))
          (unless (symbol? k)
            (error "entry should be symbol" k))
          (for-each
           (match-lambda
            (($ $cont src* k*
                ($ $kentry arity ($ $cont src k ($ $kargs names syms body))))
             (check-src src*)
             (check-src src)
             (match arity
               (($ $arity ((? symbol?) ...) ((? symbol?) ...) (or #f (? symbol?))
                   (((? keyword?)
                     (? symbol?)
                     (and (? symbol?) (? (cut memq <> syms))))
                    ...)
                   (or #f #t))
                #t)
               (else (error "bad arity" arity)))
             (unless (and (list? names) (and-map symbol? names))
               (error "letrec names not symbols" exp))
             (unless (and (list? syms) (and-map symbol? syms))
               (error "letrec syms not symbols" exp))
             (unless (match arity
                       (($ $arity req opt rest kw allow-other-keys?)
                        (= (length syms) 
                           (length names)
                           (+ (length req)
                              (length opt)
                              (if rest 1 0)
                              ;; FIXME: technically possible for kw syms to
                              ;; alias other syms
                              (length kw)))))
               (error "unexpected fun-case syms" exp))
             ;; The continuation environment is null, because we don't turn
             ;; captured continuations into closures.
             (visit body (add-env (list k* k) '())
                    (add-env (cons self syms) v-env))))
           entries))
         (($ $letrec names syms funs body)
          (unless (and (list? names) (and-map symbol? names))
            (error "letrec names not symbols" exp))
          (unless (and (list? syms) (and-map symbol? syms))
            (error "letrec syms not symbols" exp))
          (match funs
            ((($ $fun) ...) 'ok)
            (_ (error "letrec funs not lambdas" exp)))
          (unless (= (length syms) (length names) (length funs))
            (error "letrec syms, names, and funs not same length" exp))
          (let ((v-env (add-env syms v-env)))
            (for-each (cut visit <> k-env v-env) funs)
            (visit body k-env v-env)))(($ $call proc args)
          (check-var proc v-env)
          (for-each (cut check-var <> v-env) args))
         (($ $primcall name args)
          (for-each (cut check-var <> v-env) args))
         (($ $values args)
          (for-each (cut check-var <> v-env) args))
         (($ $prompt escape? tag handler)
          (unless (boolean? escape?) (error "escape? should be boolean" escape?))
          (check-var tag v-env)
          (check-var handler k-env))
         (_
          (error "unexpected expression" exp))))

      (_
       (error "unexpected cps" exp)))
    exp))
