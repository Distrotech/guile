;;; Guile Lua --- common lua functionality

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

(define-module (language lua common)

  #:use-module (ice-9 format)

  #:export (syntax-error or-eqv?))

(define (syntax-error src string . args)
  "Throw an error tagged with 'syntax-error, and print detailed source
code information when available. STRING and ARGS are given to FORMAT."
  (throw 'syntax-error #f (apply format #f string args)
         src #f #f '()))

;; I was using CASE, but this is more succinct
;; (or-eqv? 1 #f 1) => (or (eqv? 1 #f) (eqv? 1 1))
(define-syntax or-eqv?
  (syntax-rules ()
    ((_ test '(value ...))
     (or (eqv? test 'value) ...))
    ((_ test value ...)
     (or (eqv? test value) ...))))
