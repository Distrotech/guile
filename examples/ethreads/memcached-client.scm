;;; Simple memcached client implementation

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

(define (server-error eport msg . args)
  (apply format (current-error-port) msg args)
  (newline (current-error-port))
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
        (server-error eport "Line too long: ~S" str))
       ((eof-object? delim)
        (server-error eport "EOF while reading line: ~S" str))
       (else
        (when (and (eqv? delim #\return)
                   (eqv? (lookahead-latin1-char eport) #\newline))
          (get-latin1-char eport))
        str)))))

(define (parse-int eport val)
  (let ((num (string->number val)))
    (unless (and num (integer? num) (exact? num) (>= num 0))
      (server-error eport "Expected a non-negative integer: ~s" val))
    num))

(define (make-item flags bv)
  (vector flags bv))
(define (item-flags item)
  (vector-ref item 0))
(define (item-bv item)
  (vector-ref item 1))

(define (get eport . keys)
  (put-utf8-string eport "get ")
  (put-utf8-string eport (string-join keys " "))
  (put-utf8-string eport "\r\n")
  (drain-output eport)
  (let lp ((vals '()))
    (let ((line (read-line eport)))
      (match (string-split line #\space)
        (("VALUE" key flags length)
         (let* ((flags (parse-int eport flags))
                (length (parse-int eport length)))
           (unless (member key keys)
             (server-error eport "Unknown key: ~a" key))
           (when (assoc key vals)
             (server-error eport "Already have response for key: ~a" key))
           (let ((bv (get-bytevector-n eport length)))
             (unless (= (bytevector-length bv) length)
               (server-error eport "Expected ~A bytes, got ~A" length bv))
             (unless (eqv? (get-latin1-char eport) #\return)
               (server-error eport "Expected \\r"))
             (unless (eqv? (get-latin1-char eport) #\newline)
               (server-error eport "Expected \\n"))
             (lp (acons key (make-item flags bv) vals)))))
        (("END")
         (reverse vals))
        (_
         (server-error eport "Bad line: ~A" line))))))

(define* (set eport key flags exptime bytes #:key noreply?)
  (put-utf8-string eport "set ")
  (put-utf8-string eport key)
  (put-utf8-char eport #\space)
  (put-utf8-string eport (number->string flags))
  (put-utf8-char eport #\space)
  (put-utf8-string eport (number->string exptime))
  (put-utf8-char eport #\space)
  (put-utf8-string eport (number->string (bytevector-length bytes)))
  (when noreply?
    (put-utf8-string eport " noreply"))
  (put-utf8-string eport "\r\n")
  (put-bytevector eport bytes)
  (put-utf8-string eport "\r\n")
  (drain-output eport)
  (let ((line (read-line eport)))
    (match line
      ("STORED" #t)
      ("NOT_STORED" #t)
      (_
       (server-error eport "Unexpected response from server: ~A" line)))))

(define (connect addrinfo)
  (let ((eport (file-port->eport (socket (addrinfo:fam addrinfo)
                                         (addrinfo:socktype addrinfo)
                                         (addrinfo:protocol addrinfo)))))
    ;; Disable Nagle's algorithm.  We buffer ourselves.
    (setsockopt (eport-fd eport) IPPROTO_TCP TCP_NODELAY 0)
    (connect-eport eport (addrinfo:addr addrinfo))
    eport))

(define *active-clients* 0)

(define (client-loop addrinfo n num-connections)
  (set! *active-clients* (1+ *active-clients*))
  (let ((eport (connect addrinfo))
        (key (string-append "test-" (number->string n))))
    (let lp ((m 0))
      (when (< m num-connections)
        (let ((v (string->utf8 (number->string m))))
          (set eport key 0 0 v)
          (let* ((response (get eport key))
                 (item (assoc-ref response key)))
            (unless item
              (server-error eport "Not found: ~A" key))
            (unless (equal? (item-bv item) v)
              (server-error eport "Bad response: ~A (expected ~A)" (item-bv item) v))
            (lp (1+ m))))))
    (close-eport eport))
  (set! *active-clients* (1- *active-clients*))
  (when (zero? *active-clients*)
    (exit 0)))

(define (run-memcached-test num-clients num-connections)
  ;; The getaddrinfo call blocks, unfortunately.  Call it once before
  ;; spawning clients.
  (let ((addrinfo (car (getaddrinfo "localhost" (number->string 11211)))))
    (let lp ((n 0))
      (when (< n num-clients)
        (spawn
         (lambda ()
           (client-loop addrinfo n num-connections)))
        (lp (1+ n)))))
  (run))

(apply run-memcached-test (map string->number (cdr (program-arguments))))
