;;; base.scm --- The R7RS base library

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


(define-library (scheme base)
  (export + * - / = < > <= >=
          abs
          and
          append
          apply
          assoc
          assq
          assv
          begin
          boolean?
          bytevector
          bytevector-append
          bytevector-copy
          bytevector-copy!
          bytevector-length
          bytevector-u8-ref
          bytevector-u8-set!
          bytevector?
          caar
          cadr
          call-with-current-continuation
          call-with-port
          call-with-values
          call/cc
          car
          case
          cdar
          cddr
          cdr
          ceiling
          char->integer
          char-ready?
          char<=?
          char<?
          char=?
          char>=?
          char>?
          char?
          close-input-port
          close-output-port
          close-port
          complex?
          cond
          cond-expand
          cons
          current-error-port
          current-input-port
          current-output-port
          define
          define-record-type
          define-syntax
          define-values
          denominator
          do
          dynamic-wind
          else
          eof-object?
          equal?
          error
          error-object-message
          even?
          exact-integer-sqrt
          exact?
          features
          floor
          floor-remainder
          flush-output-port
          gcd
          get-output-string
          if
          include-ci
          inexact?
          input-port?
          integer?
          lcm
          let
          let*-values
          let-values
          letrec*
          list
          list->vector
          list-ref
          list-tail
          make-bytevector
          make-parameter
          make-vector
          max
          memq
          min
          negative?
          not
          number->string
          numerator
          open-input-bytevector
          open-output-bytevector
          or
          output-port?
          parameterize
          peek-u8
          positive?
          quasiquote
          quotient
          raise-continuable
          rationalize
          read-bytevector!
          ;;read-error?    XXX TODO
          ;;file-error?    XXX TODO
          read-string
          real?
          reverse
          set!
          set-cdr!
          string
          string->number
          string->utf8
          utf8->string
          string-append
          eof-object
          eq?
          eqv?
          (rename condition? error-object?)
          (rename condition-irritants error-object-irritants)
          (rename exact->inexact inexact)
          (rename inexact->exact exact)
          exact-integer?
          expt
          floor-quotient
          floor/
          for-each
          get-output-bytevector
          guard
          include
          input-port-open?
          integer->char
          lambda
          length
          let*
          let-syntax
          letrec
          letrec-syntax
          list->string
          list-copy
          list-set!
          list?
          make-list
          make-string
          map
          member
          memv
          modulo
          newline
          null?
          number?
          odd?
          open-input-string
          open-output-string
          output-port-open?
          pair?
          peek-char
          port?
          procedure?
          quote
          raise
          rational?
          read-bytevector
          read-char
          read-line
          read-u8
          remainder
          round
          set-car!
          square
          string->list
          string->symbol
          string->vector
          string-copy
          string-copy!
          string-for-each
          string-map
          string-set!
          string<?
          string>=?
          string?
          symbol->string
          symbol?
          syntax-rules
          truncate
          truncate-remainder
          ;; XXX FIXME when 'char-ready?' is fixed, this will need adjustment.
          (rename char-ready? u8-ready?)
          unquote
          vector
          vector->string
          vector-copy
          vector-fill!
          vector-length
          vector-ref
          vector?
          with-exception-handler
          write-char
          write-u8
          string-fill!
          string-length
          string-ref
          string<=?
          string=?
          string>?
          substring
          symbol=?
          syntax-error
          textual-port?
          truncate-quotient
          truncate/
          unless
          unquote-splicing
          values
          vector->list
          vector-append
          vector-copy!
          vector-for-each
          vector-map
          vector-set!
          when
          write-bytevector
          write-string
          zero?)

  (import (rename (guile)
                  (vector-fill! guile-vector-fill!)
                  (vector-copy guile-vector-copy))
          (only (rnrs base)
                vector-for-each
                vector-map)
          (rename (rnrs bytevectors)
                  (utf8->string guile-utf8->string)
                  (string->utf8 guile-string->utf8)
                  (bytevector-copy guile-bytevector-copy)
                  (bytevector-copy! guile-bytevector-copy!))
          (rnrs io ports)
          (rnrs exceptions)
          (rnrs conditions)
          (srfi srfi-6)
          (srfi srfi-9)
          (srfi srfi-11)
          (rename (ice-9 rdelim)
                  (read-string guile-read-string)))

  (begin
    (define (features)
      %cond-expand-features)     ; XXX also include per-module features?

    (define (boolean=? . bs)
      (unless (and-map boolean? bs)
        (error "boolean=?: passed non-boolean argument"))
      (apply eq? bs))

    (define (symbol=? . bs)
      (unless (and-map symbol? bs)
        (error "symbol=?: passed non-symbol argument"))
      (apply eq? bs))

    (define (square z)
      (* z z))

    (define* (vector-fill! v fill #:optional (start 0) (end (vector-length v)))
      (let loop ((i start))
        (when (< i end)
          (vector-set! v i fill)
          (loop (+ i 1)))))

    (define* (vector-copy from #:optional (start 0) (end (vector-length from)))
      (let* ((len (- end start))
             (to (make-vector len)))
        (vector-move-left! from start end to 0)))

    (define* (vector-copy! to at from #:optional (start 0) (end (vector-length from)))
      (if (> start at)
          (vector-move-left!  from start end to at)
          (vector-move-right! from start end to at)))

    (define (vector-append . vs)
      (let* ((total-len (apply + (map vector-length vs)))
             (result (make-vector total-len)))
        (let loop ((i 0) (vs vs))
          (when (not (null? vs))
            (let* ((v (car vs))
                   (len (vector-length v)))
              (vector-move-left! v 0 len result i)
              (loop (+ i len) (cdr vs)))))))

    (define* (vector->string v #:optional (start 0) (end (vector-length v)))
      (string-tabulate (lambda (i)
                         (vector-ref v (+ start i)))
                       (- end start)))

    (define* (string->vector s #:optional (start 0) (end (string-length s)))
      (let* ((len (- end start))
             (v (make-vector len)))
        (let loop ((from (- end 1))
                   (to (- len 1)))
          (when (>= to 0)
            (vector-set! v to (string-ref s from))
            (loop (- from 1) (- to 1))))))

    (define (bytevector . u8-list)
      (u8-list->bytevector u8-list))

    (define (bytevector-append . bvs)
      (let* ((total-len (apply + (map bytevector-length bvs)))
             (result (make-bytevector total-len)))
        (let loop ((i 0) (bvs bvs))
          (when (not (null? bvs))
            (let* ((bv (car bvs))
                   (len (bytevector-length bv)))
              (guile-bytevector-copy! bv 0 result i len)
              (loop (+ i len) (cdr bvs)))))))

    (define bytevector-copy
      (case-lambda
        ((bv)
         (guile-bytevector-copy bv))
        ((bv start)
         (let* ((len (- (bytevector-length bv) start))
                (result (make-bytevector len)))
           (guile-bytevector-copy! bv start result 0 len)
           result))
        ((bv start end)
         (let* ((len (- end start))
                (result (make-bytevector len)))
           (guile-bytevector-copy! bv start result 0 len)
           result))))

    (define bytevector-copy!
      (case-lambda
        ((to at from)
         (guile-bytevector-copy! from 0 to at
                                 (bytevector-length from)))
        ((to at from start)
         (guile-bytevector-copy! from start to at
                                 (- (bytevector-length from) start)))
        ((to at from start end)
         (guile-bytevector-copy! from start to at
                                 (- end start)))))

    (define utf8->string
      (case-lambda
        ((bv) (guile-utf8->string bv))
        ((bv start)
         (guile-utf8->string (bytevector-copy bv start)))
        ((bv start end)
         (guile-utf8->string (bytevector-copy bv start end)))))

    (define string->utf8
      (case-lambda
        ((s) (guile-string->utf8 s))
        ((s start)
         (guile-string->utf8 (substring s start)))
        ((s start end)
         (guile-string->utf8 (substring s start end)))))

    (define (open-input-bytevector bv)
      (open-bytevector-input-port bv))

    (define (open-output-bytevector)
      (call-with-values
          (lambda () (open-bytevector-output-port))
        (lambda (port proc)
          (%set-port-property! port 'get-output-bytevector proc)
          port)))

    (define (get-output-bytevector port)
      (let ((proc (%port-property port 'get-output-bytevector)))
        (unless proc
          (error "get-output-bytevector: port not created by open-output-bytevector"))
        (proc)))

    (define* (peek-u8 #:optional (port (current-input-port)))
      (lookahead-u8 port))

    (define* (read-u8 #:optional (port (current-input-port)))
      (get-u8 port))

    (define* (write-u8 byte #:optional (port (current-output-port)))
      (put-u8 port byte))

    (define* (read-bytevector k #:optional (port (current-input-port)))
      (get-bytevector-n port k))

    (define* (read-bytevector! bv
                               #:optional
                               (port (current-input-port))
                               (start 0)
                               (end (bytevector-length bv)))
      (get-bytevector-n! port bv start (- end start)))

    (define* (write-bytevector bv
                               #:optional
                               (port (current-output-port))
                               (start 0)
                               (end (bytevector-length bv)))
      (put-bytevector port bv start (- end start)))

    (define* (read-string k #:optional (port (current-input-port)))
      (unless (exact-integer? k)
        (error "read-string: expected exact integer, got" k))
      (if (zero? k)
          ""
          (let ((s (guile-read-string port k)))
            (if (string=? s "")
                (eof-object)
                s))))

    (define write-string
      (case-lambda
        ((s) (display s))
        ((s port)
         (display s port))
        ((s port start)
         (display (substring s start) port))
        ((s port start end)
         (display (substring s start end) port))))

    (define write-bytevector
      (case-lambda
        ((s) (display s))
        ((s port)
         (display s port))
        ((s port start)
         (display (substring s start) port))
        ((s port start end)
         (display (substring s start end) port))))

    (define (input-port-open? port)
      (unless (input-port? port)
        (error "input-port-open?: not an input port" port))
      (not (port-closed? port)))

    (define (output-port-open? port)
      (unless (output-port? port)
        (error "output-port-open?: not an output port" port))
      (not (port-closed? port)))))
