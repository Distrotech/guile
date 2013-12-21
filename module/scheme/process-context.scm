;;; process-context.scm --- The R7RS process-context library

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


(define-library (scheme process-context)
  (export command-line
          exit
          (rename primitive-_exit emergency-exit)
          (rename getenv get-environment-variable)
          get-environment-variables)
  (import (scheme base)
          (only (guile)
                string-index
                command-line
                exit
                primitive-_exit
                getenv
                environ))
  (begin
    (define (get-environment-variables)
      (map (lambda (s)
             (let ((i (string-index s #\=)))
               (cons (substring s 0 i)
                     (substring s (+ i 1)))))
           (environ)))))
