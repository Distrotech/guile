;;; Simple memcached server implementation

;; Copyright (C)  2012 Free Software Foundation, Inc.

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
;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA
;; 02110-1301 USA

(use-modules (rnrs bytevectors)
             (ice-9 eports)
             (ice-9 ethreads)
             (ice-9 match))

(define (make-default-socket family addr port)
  (let ((sock (socket PF_INET SOCK_STREAM 0)))
    (setsockopt sock SOL_SOCKET SO_REUSEADDR 1)
    (fcntl sock F_SETFD FD_CLOEXEC)
    (bind sock family addr port)
    sock))

(define (client-error eport msg . args)
  (put-utf8-string eport (apply format #f msg args))
  (put-utf8-string eport "\r\n")
  (drain-output eport)
  (close-eport eport)
  (suspend))

(define (read-line eport)
  (define (end-of-line? c)
    (or (eqv? c #\newline) (eqv? c #\return)))
  (call-with-values
      (lambda ()
        ;; Restrict to 512 chars to avoid denial of service attacks.
        (get-latin1-string-delimited eport end-of-line? #:max-chars 512))
    (lambda (str delim)
      (cond
       ((not delim)
        (client-error eport "Line too long: ~S" str))
       ((eof-object? delim)
        (client-error eport "EOF while reading line: ~S" str))
       (else
        (when (and (eqv? delim #\return)
                   (eqv? (lookahead-latin1-char eport) #\newline))
          (get-latin1-char eport))
        str)))))

(define (parse-int eport val)
  (let ((num (string->number val)))
    (unless (and num (integer? num) (exact? num) (>= num 0))
      (client-error eport "Expected a non-negative integer: ~s" val))
    num))

(define (make-item flags bv)
  (vector flags bv))
(define (item-flags item)
  (vector-ref item 0))
(define (item-bv item)
  (vector-ref item 1))

(define *commands* (make-hash-table))

(define-syntax-rule (define-command (name eport store . pat)
                      body body* ...)
  (begin
    (define (name eport store args)
      (match args
        (pat body body* ...)
        (else
         (client-error eport "Bad line: ~A ~S" 'name (string-join args " ")))))
    (hashq-set! *commands* 'name name)))

(define-command (get eport store key* ...)
  (let lp ((key* key*))
    (match key*
      ((key key* ...)
       (let ((item (hash-ref store key)))
         (when item
           (put-utf8-string eport "VALUE ")
           (put-utf8-string eport key)
           (put-utf8-char eport #\space)
           (put-utf8-string eport (number->string (item-flags item)))
           (put-utf8-char eport #\space)
           (put-utf8-string eport (number->string
                                   (bytevector-length (item-bv item))))
           (put-utf8-char eport #\return)
           (put-utf8-char eport #\newline)
           (put-bytevector eport (item-bv item))
           (put-utf8-string eport "\r\n"))
         (lp key*)))
      (()
       (put-utf8-string eport "END\r\n")))))

(define-command (set eport store key flags exptime bytes
                     . (and noreply (or ("noreply") ())))
  (let* ((flags (parse-int eport flags))
         (exptime (parse-int eport exptime))
         (bytes (parse-int eport bytes)))
    (let ((bv (get-bytevector-n eport bytes)))
      (unless (= (bytevector-length bv) bytes)
        (client-error eport "Tried to read ~A bytes, only read ~A"
                      bytes (bytevector-length bv)))
      (hash-set! store key (make-item flags bv))
      (when (eqv? (lookahead-latin1-char eport) #\return)
        (get-latin1-char eport))
      (when (eqv? (lookahead-latin1-char eport) #\newline)
        (get-latin1-char eport)))
    (put-utf8-string eport "STORED\r\n")))

(define (client-loop eport store)
  (let loop ()
    (let* ((args (string-split (read-line eport) #\space))
           (verb (string->symbol (car args)))
           (proc (hashq-ref *commands* verb)))
      (unless proc
        (client-error eport "Bad command: ~a" verb))
      (proc eport store (cdr args)))
    (drain-output eport)
    (if (eof-object? (lookahead-u8 eport))
        (close-eport eport)
        (loop))))

(define (socket-loop esocket store)
  (let loop ()
    (let ((client (accept-eport esocket)))
      ;; Disable Nagle's algorithm.  We buffer ourselves.
      (setsockopt (eport-fd client) IPPROTO_TCP TCP_NODELAY 0)
      (spawn (lambda () (client-loop client store)))
      (loop))))

(define* (run-memcached #:key
                        (host #f)
                        (family AF_INET)
                        (addr (if host
                                  (inet-pton family host)
                                  INADDR_LOOPBACK))
                        (port 11211)
                        (socket (make-default-socket family addr port)))
  (listen socket 128)
  (sigaction SIGPIPE SIG_IGN)
  (spawn
   (lambda ()
     (socket-loop (file-port->eport socket) (make-hash-table))))
  (run))

(run-memcached)
