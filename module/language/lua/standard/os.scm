;;; Guile Lua --- os standard library

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

(define-module (language lua standard os)
  #:use-module (language lua runtime)

  #:use-module (srfi srfi-98))

(define (clock)
  (tms:clock (times)))

(define* (date #:optional (format "%c") time)
  (let* ((utc? (eq? (string-ref format 0) #\!))
         ;; skip !
         (format (if utc? (string-copy format 1) format))
         (stm ((if utc? gmtime localtime) (or time (current-time)))))
    (if time
        (begin
          (assert-number 2 "date" time)
          (if (string=? format "*t")
              (let* ((table (make-table)))
                (rawset table "sec" (tm:sec stm))
                (rawset table "min" (tm:min stm))
                (rawset table "hour" (tm:hour stm))
                (rawset table "month" (+ 1 (tm:mon stm)))
                (rawset table "year" (+ 1900 (tm:year stm)))
                (rawset table "wday" (+ 1 (tm:wday stm)))
                (rawset table "yday" (+ 1 (tm:yday stm)))
                (rawset table "isdst" (> (tm:isdst stm) 0))
                table)
              (strftime format stm)))
        (strftime format stm))))

(define (difftime t2 t1)
  (- t2 t1))

(define* (execute #:optional command)
  (if (not command)
      1
      (system command)))

(define* (exit #:optional (code 0))
  (primitive-exit code))

(define (getenv varname)
  (or (get-environment-variable varname) #nil))

(define rename rename-file)

(define (remove filename)
  (if (file-is-directory? filename)
      (rmdir filename)
      (delete-file filename)))

(define* (setlocale locale #:optional (category "all"))
  (assert-string 2 "setlocale" category)
  ((@ (guile) setlocale)
   locale
   (cond ((string=? category "all") LC_ALL)
         ((string=? category "collate") LC_COLLATE)
         ((string=? category "ctype") LC_CTYPE)
         ((string=? category "messages") LC_MESSAGES)
         ((string=? category "monetary") LC_MONETARY)
         ((string=? category "numeric") LC_NUMERIC)
         ((string=? category "time") LC_TIME))))

(define* (time #:optional table)
  (if table
      (begin
        (assert-table 1 "time" table)
        (let* ((sec (get-field table "sec" 0))
               (min (get-field table "min" 0))
               (hour (get-field table "hour" 12))
               (day (get-field table "day" -1))
               (month (- (get-field table "month" -1) 1))
               (year (- (get-field table "year" -1) 1900))
               (isdst (get-field table "isdst" 0))
               (result (make-vector 11 0)))
          (set-tm:sec result sec)
          (set-tm:min result min)
          (set-tm:hour result hour)
          (set-tm:mday result day)
          (set-tm:mon result month)
          (set-tm:year result year)
          (set-tm:isdst result isdst)
          (set-tm:zone result "")
          (car (mktime result)))
          )
      (current-time)))

(define tmpname mkstemp!)
