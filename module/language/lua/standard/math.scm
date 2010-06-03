;;; Guile Lua --- math standard library

;;; Copyright (C) 2010 Free Software Foundation, Inc.
;;;
;;; This library is free software; you can redistribute it and/or
;;; modify it under the terms of the GNU Lesser General Public
;;; License as published by the Free Software Foundation; either
;;; version 3 of the License, or (at your option) any later version.
;;;
;;; This library is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;; Lesser General Public License for more details.
;;;
;;; You should have received a copy of the GNU Lesser General Public
;;; License along with this library; if not, write to the Free Software
;;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

;;; Code:

(define-module (language lua standard math)
  #:use-module (language lua runtime))

;; TODO: math.modf
;; TODO: math.deg,rad,frexp,random not tested

;; NOTE: as opposed to lua, math.sqrt accepts negative arguments, as
;; guile's numeric tower is capable of representing complex numbers

(define huge +inf.0)
(define *nan* (nan))
(define pi 3.14159265358979323846)
(define radians_per_degree (/ pi 180.0))

(letrec-syntax
    ((wrap-builtins
      (syntax-rules (rename rename2 variable-arity)
        ;; we must know the arity of the wrapped procedure because lua ignores superfluous arguments whereas it is an error in scheme

        ;; simple wrap with new name and 1 argument
        ((_ () (rename guile-name lua-name))
         (define (lua-name a . _)
           ((@ (guile) guile-name) a)))

        ((_ () (rename2 guile-name lua-name))
         (define (lua-name a b . _)
           ((@ (guile) guile-name) a b)))

        ;; simple wrap with 2 arguments
        ((_ () (2 name))
         (define (name a b . _)
           ((@ (guile) name) a b)))

        ;; simple wrap with variable arguments
        ((_ () (variable-arity name))
         (define (name . _)
           (apply (@ (guile) name) _)))

        ;; simple wrap with 1 argument
        ((_ () name)
         (define (name a . _)
           ((@ (guile) name) a)))

        ;; 1) take all input and pass it to subtransformers
        ((_ subform ...)
         (begin
           (wrap-builtins () subform)
           ...)))))
  (wrap-builtins
   abs
   acos
   asin
   atan
   (rename ceiling ceil)
   cos
   cosh
   exp
   (rename2 remainder modf)
   floor
   log
   log10
   sin
   sinh
   sqrt
   (variable-arity max)
   (variable-arity min)
   (rename expt pow)
   tan
   tanh))

(define (atan2 x y)
  (atan (/ x y)))

;; copy the global random state for this module so we don't mutate it
(define randomstate (copy-random-state *random-state*))

(define (randomseed seed . _)
  (set! randomstate (seed->random-state seed)))

(define* (random #:optional m n #:rest _)
  ;; this can be a little confusing because guile's random number
  ;; generator only allows [0, N) but we need [0,1), [1,m] and [m,n]
  (cond ((and (not m) (not n)) ((@ (guile) random) 1.0))
        ;; this is really [1,M)
        ((and m) (+ 1 ((@ (guile) random) m)))
        ((and m n) (+ m ((@ (guile) random) n)))
        (else (error #:RANDOM "should not happen"))))

(define (deg x)
  (/ x radians_per_degree))

(define (rad x)
  (* x radians_per_degree))

(define (ldexp x exp)
  (cond ((= exp 0) x)
        ((= exp *nan*) *nan*)
        ((= exp +inf.0) +inf.0)
        ((= exp -inf.0) -inf.0)
        (else (* x (expt 2 exp)))))

(define log2
  (let ((log2 (log 2)))
    (lambda (x)
      (/ (log x) log2))))

(define (frexp x)
  (if (zero? x)
      0.0
      (let* ((l2 (log2 x))
             (e (floor (log2 x)))
             (e (if (= l2 e)
                    (inexact->exact e)
                    (+ (inexact->exact e) 1)))
             (f (/ x (expt 2 e))))
        f)))
