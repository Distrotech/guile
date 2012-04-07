;; Ethreads: cooperative, event-driven user-space threads.

;;;; Copyright (C) 2012 Free Software Foundation, Inc.
;;;; 
;;;; This library is free software; you can redistribute it and/or
;;;; modify it under the terms of the GNU Lesser General Public
;;;; License as published by the Free Software Foundation; either
;;;; version 3 of the License, or (at your option) any later version.
;;;; 
;;;; This library is distributed in the hope that it will be useful,
;;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;;; Lesser General Public License for more details.
;;;; 
;;;; You should have received a copy of the GNU Lesser General Public
;;;; License along with this library; if not, write to the Free Software
;;;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA
;;;; 

(define-module (ice-9 ethreads)
  #:use-module ((srfi srfi-1) #:select (append-reverse!))
  #:use-module (srfi srfi-9)
  #:use-module (ice-9 epoll)
  #:use-module (ice-9 eports)
  #:replace (sleep)
  #:export (;; Low-level interface: contexts and threads.
            make-econtext
            current-econtext
            ensure-current-econtext
            destroy-econtext

            create-ethread
            current-ethread
            kill-ethread
            ethread-state

            ;; High-level interface.
            run
            spawn
            suspend
            resume
            ;; sleep is #:replace'd; see above
            ))

(define-record-type <econtext>
  (%make-econtext epfd prompt-tag runnables sources sleepers)
  nio?
  (epfd econtext-epfd)
  (prompt-tag econtext-prompt-tag)
  ;; (thread ...)
  (runnables econtext-runnables set-econtext-runnables!)
  ;; fd -> ((total-events . min-expiry) #(events expiry thread) ...)
  (sources econtext-sources)
  ;; ((thread . expiry) ...)
  (sleepers econtext-sleepers set-econtext-sleepers!))

(define-record-type <ethread>
  (make-ethread state data)
  ethread?
  ;; One of: runnable, running, suspended, finished.
  (state ethread-state set-ethread-state!)
  ;; State-specific data.  For runnable, a thunk; for running, nothing;
  ;; for suspended, a continuation; for finished, a list of values.
  (data ethread-data set-ethread-data!))

(define (make-econtext)
  (%make-econtext (epoll-create) (make-prompt-tag "ethreads")
                  '() (make-hash-table) '()))

(define current-econtext (make-parameter #f))
(define (ensure-current-econtext)
  (let ((ctx (current-econtext)))
    (or ctx
        (begin
          (current-econtext (make-econtext))
          (ensure-current-econtext)))))

(define (make-source events expiry thread) (vector events expiry thread))
(define (source-events s) (vector-ref s 0))
(define (source-expiry s) (vector-ref s 1))
(define (source-thread s) (vector-ref s 2))

(define current-ethread (make-parameter #f))

(define (schedule-thread! ctx thread thunk)
  (when (eq? (ethread-state thread) 'suspended)
    (set-ethread-state! thread 'runnable)
    (set-ethread-data! thread thunk)
    (let ((runnables (econtext-runnables ctx)))
      (set-econtext-runnables! ctx (cons thread runnables)))))

(define internal-time-units-per-millisecond
  (/ internal-time-units-per-second 1000))

(define (poll-for-events ctx)
  ;; Run through the work list.  When it's empty, wait for I/O, and
  ;; start again.
  (define (schedule-threads fd revents seed)
    (let ((sources (hashv-ref (econtext-sources ctx) fd)))
      (for-each (lambda (source)
                  ;; FIXME: If we were waiting with a timeout, this
                  ;; thread might still be in "sleepers", and we should
                  ;; probably remove it.  Currently we don't do timed
                  ;; waits though, only sleeps.
                  (unless (zero? (logand revents
                                         (logior (source-events source) EPOLLERR)))
                    (resume (source-thread source) (lambda () revents) ctx)))
                (cdr sources))
      (cond
       ((zero? (logand revents EPOLLERR))
        (hashv-remove! (econtext-sources ctx) fd)
        (epoll-remove! (econtext-epfd ctx) fd))
       (else
        (set-cdr! sources '())
        ;; Reset active events and expiration time, respectively.
        (set-car! (car sources) #f)
        (set-cdr! (car sources) #f)))
      seed))
  (let* ((sleepers (econtext-sleepers ctx))
         (waketime (and (pair? sleepers) (cdar sleepers))))
    (epoll (econtext-epfd ctx)
           32                           ; maxevents
           (if waketime
               (let ((now (get-internal-real-time)))
                 (if (< waketime now)
                     0
                     (round/ (- waketime now)
                             internal-time-units-per-millisecond)))
               -1)
           #:folder schedule-threads)
    (let ((now (get-internal-real-time)))
      ;; We build a list and process it in reverse so that the sleepers
      ;; with the earliest wake-time run first.  If schedule-threads
      ;; already scheduled a thread -- i.e. its timeout ran out, *and*
      ;; it was woken up for an event -- then this resume will have no
      ;; effect because the thread was already runnable.
      (let wake-sleepers ((sleepers sleepers) (wakers '()))
        (if (and (pair? sleepers) (>= now (cdar sleepers)))
            (wake-sleepers (cdr sleepers) (cons (caar sleepers) wakers))
            (begin
              (set-econtext-sleepers! ctx sleepers)
              (for-each (lambda (thread)
                          (resume thread (lambda () 0) ctx))
                        wakers)))))))

(define (next-thread ctx)
  (let lp ()
    (let ((runnables (econtext-runnables ctx)))
      (cond
       ((pair? runnables)
        (let ((thread (car runnables)))
          (set-econtext-runnables! ctx (cdr runnables))
          thread))
       (else
        (poll-for-events ctx)
        (lp))))))

(define (run-ethread ctx thread)
  (when (eq? (ethread-state thread) 'runnable)
    (parameterize ((current-ethread thread))
      (call-with-prompt
       (econtext-prompt-tag ctx)
       (lambda ()
         (let ((thunk (ethread-data thread)))
           (set-ethread-state! thread 'running)
           (set-ethread-data! thread #f)
           (thunk)))
       (lambda (k after-suspend)
         (set-ethread-state! thread 'suspended)
         (set-ethread-data! thread k)
         (after-suspend ctx thread))))))

(define (destroy-econtext ctx)
  #;
  (for-each kill-ethread (list-copy (econtext-threads ctx)))
  (epoll-destroy (econtext-epfd ctx)))

(define (create-ethread ctx thunk)
  (let ((thread (make-ethread 'suspended #f)))
    (schedule-thread! ctx
                      thread
                      (lambda ()
                        (call-with-values thunk
                          (lambda results
                            (set-ethread-state! thread 'finished)
                            (set-ethread-data! thread results)))))
    thread))

(define (kill-ethread thread)
  (pk 'kill-thread thread))

;; The AFTER-SUSPEND thunk allows the user to suspend the current
;; thread, saving its state, and then perform some other nonlocal
;; control flow.
;;
(define* (suspend #:optional (after-suspend (lambda (ctx thread) #f)))
  ((abort-to-prompt (econtext-prompt-tag (current-econtext))
                    after-suspend)))

(define* (resume thread thunk #:optional (ctx (ensure-current-econtext)))
  (let* ((cont (ethread-data thread))
         (thunk (lambda () (cont thunk))))
    (schedule-thread! ctx thread thunk)))

(define* (run #:optional (ctx (ensure-current-econtext)))
  (parameterize ((current-econtext ctx)
                 (current-read-waiter wait-for-readable)
                 (current-write-waiter wait-for-writable))
    (let lp ()
      (run-ethread ctx (next-thread ctx))
      (lp))))

(define* (spawn thunk #:optional (ctx (ensure-current-econtext)))
  (create-ethread ctx thunk))

(define (wait-for-readable eport)
  (wait-for-events eport (logior EPOLLIN EPOLLRDHUP)))

(define (wait-for-writable eport)
  (wait-for-events eport EPOLLOUT))

(define (handle-events eport events revents)
  (unless (zero? (logand revents EPOLLERR))
    (error "error reading from fd")))

(define (wait-for-events eport events)
  (handle-events
   eport
   events
   (suspend
    (lambda (ctx thread)
      (let* ((fd (file-eport-fd eport))
             (sources (hashv-ref (econtext-sources ctx) fd)))
        (cond
         (sources
          (set-cdr! sources (cons (make-source events #f thread) (cdr sources)))
          (let ((active-events (caar sources)))
            (unless (and active-events
                         (= (logand events active-events) events))
              (set-car! (car sources) (logior events (or active-events 0)))
              (epoll-modify! (econtext-epfd ctx) fd
                             (logior (caar sources) EPOLLONESHOT)))))
         (else
          (hashv-set! (econtext-sources ctx)
                      fd (acons events #f
                                (list (make-source events #f thread))))
          (epoll-add! (econtext-epfd ctx) fd (logior events EPOLLONESHOT)))))))))

(define (add-sleeper! ctx thread seconds)
  (let ((waketime (+ (get-internal-real-time)
                     (inexact->exact
                      (round (* seconds internal-time-units-per-second))))))
    (let lp ((head '()) (tail (econtext-sleepers ctx)))
      (if (and (pair? tail) (> waketime (cdar tail)))
          (lp (cons (car tail) head) (cdr tail))
          (set-econtext-sleepers!
           ctx
           (append-reverse! head (acons thread waketime tail)))))))

(define (sleep seconds)
  (suspend
   (lambda (ctx thread)
     (add-sleeper! ctx thread seconds))))
