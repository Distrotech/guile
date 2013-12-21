;;; file.scm --- The R7RS file library

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


(define-library (scheme file)
  (export open-input-file open-output-file
          open-binary-input-file open-binary-output-file
          call-with-input-file call-with-output-file
          with-input-from-file with-output-to-file
          delete-file file-exists?)
  (import (scheme base)
          (only (guile)
                open-input-file open-output-file
                call-with-input-file call-with-output-file
                with-input-from-file with-output-to-file
                delete-file file-exists?))
  (begin
    (define (open-binary-input-file filename)
      (open-input-file filename #:binary #t))
    (define (open-binary-output-file filename)
      (open-output-file filename #:binary #t))))
