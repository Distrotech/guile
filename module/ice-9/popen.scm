;; popen emulation, for non-stdio based ports.

;;;; Copyright (C) 1998, 1999, 2000, 2001, 2003, 2006, 2010, 2011, 2012, 2013 Free Software Foundation, Inc.
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

(define-module (ice-9 popen)
  :use-module (ice-9 threads)
  :export (port/pid-table open-pipe* open-pipe close-pipe open-input-pipe
	   open-output-pipe open-input-output-pipe))

(eval-when (load eval compile)
  (load-extension (string-append "libguile-" (effective-version))
                  "scm_init_popen"))

(define (make-rw-port read-port write-port)
  (make-soft-port
   (vector
    (lambda (c) (write-char c write-port))
    (lambda (s) (display s write-port))
    (lambda () (force-output write-port))
    (lambda () (read-char read-port))
    (lambda () (close-port read-port) (close-port write-port)))
   "r+"))

;; a guardian to ensure the cleanup is done correctly when
;; an open pipe is gc'd or a close-port is used.
(define pipe-guardian (make-guardian))

;; a weak hash-table to store the process ids.
;; XXX use of this table is deprecated.  It is no longer used here, and
;; is populated for backward compatibility only (since it is exported).
(define port/pid-table (make-weak-key-hash-table 31))
(define port/pid-table-mutex (make-mutex))

(define (open-pipe* mode command . args)
  "Executes the program @var{command} with optional arguments
@var{args} (all strings) in a subprocess.
A port to the process (based on pipes) is created and returned.
@var{mode} specifies whether an input, an output or an input-output
port to the process is created: it should be the value of
@code{OPEN_READ}, @code{OPEN_WRITE} or @code{OPEN_BOTH}."
  (call-with-values (lambda ()
                      (apply open-process mode command args))
    (lambda (read-port write-port pid)
      (let ((port (or (and read-port write-port
                           (make-rw-port read-port write-port))
                      read-port
                      write-port
                      (%make-void-port mode)))
            (alist-entry (cons 'popen-pid pid)))

        ;; Store the alist-entry in the guardian instead of the port,
        ;; so that we can still call 'waitpid' even if 'close-port'
        ;; is called (which clears the port entry).
        (pipe-guardian alist-entry)
        (%set-port-alist! port (cons alist-entry (%port-alist port)))

        ;; XXX populate port/pid-table for backward compatibility.
        (with-mutex port/pid-table-mutex
          (hashq-set! port/pid-table port pid))

        port))))

(define (open-pipe command mode)
  "Executes the shell command @var{command} (a string) in a subprocess.
A port to the process (based on pipes) is created and returned.
@var{mode} specifies whether an input, an output or an input-output
port to the process is created: it should be the value of
@code{OPEN_READ}, @code{OPEN_WRITE} or @code{OPEN_BOTH}."
  (open-pipe* mode "/bin/sh" "-c" command))

(define (fetch-alist-entry port)
  (assq 'popen-pid (%port-alist port)))

(define (close-process port pid)
  (close-port port)
  (cdr (waitpid pid)))

(define (close-pipe p)
  "Closes the pipe created by @code{open-pipe}, then waits for the process
to terminate and returns its status value, @xref{Processes, waitpid}, for
information on how to interpret this value."
  (let* ((alist-entry (fetch-alist-entry p))
         (pid (cdr alist-entry)))
    ;; set the cdr to #f so that the reaper won't wait on this pid
    ;; again, and to detect repeated calls to 'close-pipe'.
    (set-cdr! alist-entry #f)
    (unless alist-entry
      (error "close-pipe: port not created by (ice-9 popen)"))
    (unless pid
      (error "close-pipe: pid has already been cleared"))
    (close-process p pid)))

(define (reap-pipes)
  (let loop ()
    (let ((alist-entry (pipe-guardian)))
      (when alist-entry
        (let ((pid (cdr alist-entry)))
          ;; maybe 'close-pipe' was already called.
          (when pid
            ;; clean up without reporting errors.  also avoids blocking
            ;; the process: if the child isn't ready to be collected,
            ;; puts it back into the guardian's live list so it can be
            ;; tried again the next time the cleanup runs.
            (catch 'system-error
              (lambda ()
                (let ((pid/status (waitpid pid WNOHANG)))
                  (if (zero? (car pid/status))
                      (pipe-guardian alist-entry)  ; not ready for collection
                      (set-cdr! alist-entry #f)))) ; avoid calling waitpid again
              (lambda args #f))))
        (loop)))))

(add-hook! after-gc-hook reap-pipes)

(define (open-input-pipe command)
  "Equivalent to @code{open-pipe} with mode @code{OPEN_READ}"
  (open-pipe command OPEN_READ))

(define (open-output-pipe command)
  "Equivalent to @code{open-pipe} with mode @code{OPEN_WRITE}"
  (open-pipe command OPEN_WRITE))

(define (open-input-output-pipe command)
  "Equivalent to @code{open-pipe} with mode @code{OPEN_BOTH}"
  (open-pipe command OPEN_BOTH))

