;; Non-Blocking I/O

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

(define-module (ice-9 nio)
  #:export (nio-read
            nio-write
            nio-accept))

(eval-when (eval load compile)
  (load-extension (string-append "libguile-" (effective-version))
                  "scm_init_nio"))

(define (nio-read fd bv pos count)
  "Read @var{count} bytes from @var{fd} into @var{bv}, and write them at
@var{pos}.  Return the number of bytes read, or -1 if no bytes could be
read without blocking.  A return value of 0 indicates EOF."
  (%nio-read fd bv pos count))

(define (nio-write fd bv pos count)
  "Write to @var{fd} the @var{count} bytes from @var{bv} starting at
@var{pos}.  Return the number of bytes written, which may be less than
@var{count} if a write would block."
  (%nio-write fd bv pos count))

(define (nio-accept fd)
  "Accept a new connection on the socket whose file descriptor is
@var{fd}.  Return a pair whose @emph{car} is a file descriptor of the
new client socket, unless the @code{accept} call would have blocked, in
which case return @code{#f}."
  (%nio-accept fd))
