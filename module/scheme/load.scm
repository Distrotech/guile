;;; load.scm --- The R7RS load library

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


(define-library (scheme load)
  (export (rename r7rs-load load))
  (import (scheme base)
          (scheme case-lambda)
          (only (guile)
                load
                save-module-excursion
                set-current-module))
  (begin
    (define r7rs-load
      (case-lambda
        ((filename)
         (load filename))
        ((filename env)
         (save-module-excursion
          (lambda ()
            (set-current-module env)
            (load filename))))))))
