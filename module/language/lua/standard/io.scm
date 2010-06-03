;;; Guile Lua --- io standard library

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

(define-module (language lua standard io)
  #:use-module (language lua runtime)

  #:use-module (ice-9 popen)
  #:use-module (ice-9 rdelim)
  #:use-module (rnrs control))

;; io.file:read

;; metatable for file objects
(define file (make-table))

(rawset file '__index
        (lambda (self key)
          (rawget file key)))

(define stdin (current-input-port))
(define stdout (current-output-port))
(define stderr (current-error-port))

(define* (close #:optional (file stdout))
  (close-port file))

(rawset file 'close
        (lambda (self)
          (close self)))

;; lua doesn't actually have an optional flush argument, but this is more in line with everything else
(define* (flush #:optional (file stdout))
  (force-output file))

(rawset file 'flush
        (lambda (self)
          (flush self)))

(define* (input #:optional filename)
  (if filename
      (let* ((file (open filename)))
        (set! stdin file)
        file)
      stdin))

(define (line-iterator file auto-close?)
  (lambda ()
    (let* ((line (read-line file)))
      (if (eof-object? line)
          (begin
            (if auto-close?
                (close-port file))
            #nil)
          line))))

(define* (lines #:optional filename)
  (let* ((file (if filename (open filename) stdin)))
    (line-iterator file (and filename))))

(rawset file 'lines
   (lambda (self)
     (line-iterator self #f)))

(define* (open filename #:optional (mode "r"))
  (assert-string 1 "io.open" filename)
  (assert-string 2 "io.open" mode)
  (let* ((handle (open-file filename mode)))
    (register-userdata! handle file)
    handle))

(define* (output #:optional filename)
  (if filename
      (let* ((file (open filename "w")))
        (set! stdout file)
        file)
      stdout))

(define* (popen prog #:optional (mode "r"))
  (assert-string 2 "io.popen" mode)
  (open-pipe
   prog
   (if (string=? mode "w") OPEN_WRITE OPEN_READ)))

(define (default-read port)
  (if (eof-object? (peek-char port))
      #nil
      (read-line port)))

(rawset file 'read
   (lambda (self . formats)
     (if (null? formats)
         (default-read self)
         (apply
          values
          (map
           (lambda (self . formats)
             (unless (or (number? format) (string? format))
               (runtime-error "'file:read' expects a string or number as format argument, but got ~a" format))
             (if (number? format)
                 (if (eof-object? (peek-char self))
                     #nil
                     (let lp ((out (open-output-string))
                              (i format))
                       (if (= i 0)
                           (get-output-string out)
                           (let ((c (read-char self)))
                             (if (eof-object? self)
                                 (get-output-string out)
                                 (begin
                                   (write-char c out)
                                   (lp out (- i 1))))))))

                 (let* ((format-length (string-length format))
                        (c1 (if (> format-length 0) (string-ref format 0) #f))
                        (c2 (if (> format-length 1) (string-ref format 1) #f)))
                   (cond ((eq? c2 #\n) (runtime-error "'file:read' number reading is not yet supported"))
                         ((eq? c2 #\a)
                          (if (eof-object? (peek-char self))
                              #nil
                              (let lp ((out (open-output-string)))
                                (let ((c (read-char self)))
                                  (if (eof-object? c)
                                      (get-output-string out)
                                      (begin
                                        (write-char c out)
                                        (lp out)))))))
                         ((eq? c2 #\l)
                          (default-read self))
                         (else
                          (runtime-error "file:read does not understand format ~a" format))))))
          formats)))))

(rawset file 'seek
  (lambda* (self #:optional (whence "cur") (offset 0))
    (assert-string 1 "file:seek" whence)
    (assert-number 2 "file:seek" offset)
    (seek self offset
          (cond ((string=? whence "cur") SEEK_CUR)
                ((string=? whence "set") SEEK_SET)
                ((string=? whence "end") SEEK_END)
                (else (runtime-error "invalid 'whence' argument to 'file:seek'; expected \"cur\", \"set\", or \"end\""))))))

(rawset file 'setvbuf
   (lambda* (self mode #:optional size)
     (assert-string 1 "file:setvbuf" mode)
     (let* ((translated-mode
             (cond ((string=? mode "no") _IONBF)
                   ((string=? mode "line") _IOLBF)
                   ((string=? mode "full") _IOFBF))))
       (if size
           (setvbuf self mode)
           (setvbuf self mode size)))))

(rawset file 'write
  (lambda* (self . args)
    (for-each
      (lambda (arg)
        (unless (or (string? arg) (number? arg))
          (runtime-error "'file:write' expects string or number as argument but got '~a'" arg))
        (display arg self))
      args)))

(define (type obj)
  (if (port? obj)
      (if (port-closed? obj)
          "closed"
          "file")
      #nil))
