;;; Web I/O: Non-blocking HTTP

;; Copyright (C) 2012 Free Software Foundation, Inc.

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

;;; Commentary:
;;;
;;; This is the non-blocking HTTP implementation of the (web server)
;;; interface.
;;;
;;; Code:

(define-module (web server ethreads)
  #:use-module ((srfi srfi-1) #:select (fold))
  #:use-module (srfi srfi-9)
  #:use-module (rnrs bytevectors)
  #:use-module ((web request) #:hide (read-request read-request-body))
  #:use-module ((ice-9 binary-ports) #:select (open-bytevector-output-port))
  #:use-module (web http)
  #:use-module (web response)
  #:use-module (web server)
  #:use-module (ice-9 eports)
  #:use-module (ice-9 ethreads))


(define (make-default-socket family addr port)
  (let ((sock (socket PF_INET SOCK_STREAM 0)))
    (setsockopt sock SOL_SOCKET SO_REUSEADDR 1)
    (fcntl sock F_SETFD FD_CLOEXEC)
    (bind sock family addr port)
    sock))

(define-record-type <server>
  (make-server econtext have-request-prompt)
  server?
  (econtext server-econtext)
  (have-request-prompt server-have-request-prompt))

;; -> server
(define* (open-server #:key
                      (host #f)
                      (family AF_INET)
                      (addr (if host
                                (inet-pton family host)
                                INADDR_LOOPBACK))
                      (port 8080)
                      (socket (make-default-socket family addr port)))
  ;; We use a large backlog by default.  If the server is suddenly hit
  ;; with a number of connections on a small backlog, clients won't
  ;; receive confirmation for their SYN, leading them to retry --
  ;; probably successfully, but with a large latency.
  (listen socket 1024)
  (sigaction SIGPIPE SIG_IGN)
  (let* ((ctx (make-econtext))
         (esocket (file-port->eport socket))
         (server (make-server ctx (make-prompt-tag "have-request"))))
    (spawn (lambda () (socket-loop server esocket)) ctx)
    server))

(define (bad-request msg . args)
  (throw 'bad-request msg args))

(define (read-http-line eport)
  ;; 10 and 13 are #\newline and #\return, respectively.
  (define (end-of-line? u8)
    (or (eqv? u8 10) (eqv? u8 13)))
  (call-with-values (lambda ()
                      (get-bytevector-delimited eport end-of-line?))
    (lambda (bv delim)
      (cond
       ((eof-object? delim)
        (bad-request "EOF while reading line: ~S" bv))
       (else
        (when (and (eqv? delim 13)
                   (eqv? (lookahead-u8 eport) 10))
          (get-u8 eport))
        (utf8->string bv))))))

(define (continuation-line? port)
  (let ((c (lookahead-u8 port)))
    (or (eqv? c (char->integer #\space))
        (eqv? c (char->integer #\tab)))))

;; Read a request from this port.
(define (read-request client)
  (call-with-values (lambda () (read-request-line client read-http-line))
    (lambda (method uri version)
      (build-request uri #:method method #:version version
                     #:headers (read-headers client
                                             read-http-line
                                             continuation-line?)
                     #:port client
                     #:validate-headers? #f))))

(define (read-request-body r)
  (let ((nbytes (request-content-length r)))
    (and nbytes
         (let ((bv (get-bytevector-n (request-port r) nbytes)))
           (if (= (bytevector-length bv) nbytes)
               bv
               (bad-request "EOF while reading request body: ~a bytes of ~a"
                            (bytevector-length bv) nbytes))))))

(define (call-with-output-bytevector proc)
  (call-with-values (lambda () (open-bytevector-output-port))
    (lambda (port get-bytevector)
      (proc port)
      (let ((bv (get-bytevector)))
        (close-port port)
        bv))))

(define (keep-alive? response)
  (let ((v (response-version response)))
    (and (or (< (response-code response) 400)
             (= (response-code response) 404))
         (case (car v)
           ((1)
            (case (cdr v)
              ((1) (not (memq 'close (response-connection response))))
              ((0) (memq 'keep-alive (response-connection response)))))
           (else #f)))))

(define cork!
  (cond
   ((defined? 'TCP_NODELAY)
    (lambda (fd cork?)
      ;; Always disable Nagle's algorithm, as we handle buffering
      ;; ourselves.  Don't bother disabling if cork? is #f.
      (when cork?
        (setsockopt fd IPPROTO_TCP TCP_NODELAY 0))))
   ((defined? 'TCP_CORK)
    ;; If we don't have TCP_NODELAY, the Linux-specific TCP_CORK will
    ;; do.
    (lambda (fd cork?)
      (setsockopt fd IPPROTO_TCP TCP_CORK (if cork? 1 0))))
   (else (lambda (fd cork?) #t))))

(define (client-loop client have-request)
  (with-throw-handler #t
    (lambda ()
      (let loop ()
        (call-with-values
            (lambda ()
              (catch #t
                (lambda ()
                  (let* ((request (read-request client))
                         (body (read-request-body request)))
                    (suspend
                     (lambda (ctx thread)
                       (have-request thread request body)))))
                (lambda (key . args)
                  (display "While reading request:\n" (current-error-port))
                  (print-exception (current-error-port) #f key args)
                  (values (build-response #:version '(1 . 0) #:code 400
                                          #:headers '((content-length . 0)))
                          #vu8()))))
          (lambda (response body)
            (cork! (eport-fd client) #t)
            (put-bytevector client
                            (call-with-output-bytevector
                             (lambda (port) (write-response response port))))
            (when body
              (put-bytevector client body))
            (drain-output client)
            (if (and (keep-alive? response)
                     (begin
                       (cork! (eport-fd client) #f)
                       (not (eof-object? (lookahead-u8 client)))))
                (loop)
                (close-eport client))))))
    (lambda (k . args)
      (catch #t
        (lambda () (close-eport client #:drain-output? #f))
        (lambda (k . args)
          (display "While closing eport:\n" (current-error-port))
          (print-exception (current-error-port) #f k args))))))

(define (socket-loop server esocket)
  (define (have-request client-thread request body)
    (abort-to-prompt (server-have-request-prompt server)
                     client-thread request body))
  (let loop ()
    (let ((client (accept-eport esocket)))
      (setsockopt (eport-fd client) SOL_SOCKET SO_SNDBUF (* 12 1024))
      (spawn (lambda () (client-loop client have-request)))
      (loop))))

;; -> (client request body | #f #f #f)
(define (server-read server)
  (call-with-prompt
   (server-have-request-prompt server)
   (lambda ()
     (run (server-econtext server)))
   (lambda (k client request body)
     (values client request body))))

;; -> 0 values
(define (server-write server client response body)
  (when (and body (not (bytevector? body)))
    (error "Expected a bytevector for body" body))
  (resume client (lambda () (values response body)) (server-econtext server))
  (values))

;; -> unspecified values
(define (close-server server)
  (destroy-econtext (server-econtext server)))

(define-server-impl ethreads
  open-server
  server-read
  server-write
  close-server)
