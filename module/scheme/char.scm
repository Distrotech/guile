;;; char.scm --- The R7RS char library

;;      Copyright (C) 2013 Free Software Foundation, Inc.
;;
;; This library is free software; you can redistribute it and/or
;; modify it under the terms of the GNU Lesser General Public
;; License as published by the Free Software Foundation; either
;; version 3 of the License, or (at your option) any later version.
;;
;; This library is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; Lesser General Public License for more details.
;;
;; You should have received a copy of the GNU Lesser General Public
;; License along with this library; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA


(define-library (scheme char)
  (export char-alphabetic?
          char-ci<?
          char-ci>=?
          char-downcase
          char-lower-case?
          char-upcase
          char-whitespace?
          string-ci<=?
          string-ci=?
          string-ci>?
          string-foldcase
          char-ci<=?
          char-ci=?
          char-ci>?
          char-foldcase
          char-numeric?
          char-upper-case?
          digit-value
          string-ci<?
          string-ci>=?
          string-downcase
          string-upcase)
  (import (scheme base)
          (rnrs unicode))
  (begin
    (define (digit-value c)
      (case c
        ((#\0) 0) ((#\1) 1) ((#\2) 2) ((#\3) 3) ((#\4) 4)
        ((#\5) 5) ((#\6) 6) ((#\7) 7) ((#\8) 8) ((#\9) 9)
        ;; XXX FIXME handle other unicode digit characters.
        (else #f)))))
