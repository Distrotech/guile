;;; Guile Lua --- table standard library

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

(define-module (language lua standard table)
  #:use-module (language lua common)
  #:use-module (language lua runtime)

  #:use-module (rnrs control)
  #:use-module ((srfi srfi-1) #:select (filter!))
  #:use-module (srfi srfi-8)
  #:use-module (srfi srfi-16)
  #:use-module ((srfi srfi-69) #:select (hash-table-size hash-table-keys))
)

;; TODO - insert, remove, sort

(define (add-field! table buffer i)
  (define string (rawget table i))
  (unless (string? string)
    (runtime-error "invalid value (~a) at index ~a in table for concat; expected string" string i))
  (display string buffer))

(define* (concat table #:optional (sep "") (i 1) (%last #f) #:rest _)
  (define buffer (open-output-string))
  (assert-table 1 "concat" table)
  (let* ((ht (table-slots table))
         (last (if (not %last) (table-length table) %last)))
    (let lp ((i i))
      (if (< i last)
          (begin
            (add-field! table buffer i)
            (display sep buffer)
            (lp (+ i 1)))
          (when (= i last)
            (add-field! table buffer i)))))
  (get-output-string buffer))

;; Arguments are named a1 and a2 because confusingly, the middle argument is optional
;; table.insert(table, [pos,] value)
(define (insert table . arguments)
  (assert-table 1 "insert" table)
  (receive
   (pos value)
   (apply
    (case-lambda
      ((value)
       (values (table-length table) value))
      ((pos value)
       (assert-number 1 "insert" pos)
       (let* ((length (table-length table))
              (e (if (> pos length) pos length)))
         (let lp ((i e))
           (when (> i pos)
             (rawset table i (rawget table (- i 1)))
             (lp (- i 1))))
       (values pos value)))
      (else
       (runtime-error "wrong number of arguments to 'insert'")))
    arguments)
   (rawset table pos value)))

(define (maxn table . _)
  (assert-table 1 "maxn" table)
  (let* ((result (sort! (filter! number? (hash-table-keys (table-slots table))) >)))
    (if (null? result)
        0
        (car result))))

(define* (remove table #:optional pos)
  (assert-table 1 "remove" table)
  (let* ((e (table-length table)))
    (unless pos (set! pos (table-length table)))
    (assert-number 2 "remove" pos)
    (if (eq? (table-length table) 0)
        0
        (let* ((result (rawget table pos)))
          (let lp ((pos pos))
            (if (< pos e)
                (begin
                  (rawset table pos (rawget table (+ pos 1)))
                  (lp (+ pos 1)))
                (rawset table pos #nil)))
          result))))

(define (sort . rest)
  (runtime-error "table.sort UNIMPLEMENTED"))