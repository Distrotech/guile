;;; Guile Lua --- tokenizer

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

;; This is a simple lexer. It generally matches up Lua data types with
;; Scheme. Reserved words in Lua, like 'not', are returned as keywords,
;; like '#:not'. Operators are returned as keywords like #:==, or
;; characters like #\+ when they're only a character long. Identifiers
;; are returned as symbols
(define-module (language lua lexer)
  #:use-module (srfi srfi-8)
  #:use-module (srfi srfi-14)
  #:use-module (srfi srfi-39)
  #:use-module (language lua common)
  #:export (make-lexer))

(define stdout (current-output-port))

(define (source-info port)
  `((filename . ,(port-filename port))
    (line . ,(port-line port))
    (column . ,(port-column port))))

;; Character predicates

;; Lua only accepts ASCII characters as of 5.2, so we define our own
;; charsets here
(define (char-predicate string)
  (let ((char-set (string->char-set string)))
    (lambda (c)
      (and (not (eof-object? c)) (char-set-contains? char-set c)))))

(define is-digit? (char-predicate "0123456789"))
(define is-name-first? (char-predicate "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_"))
(define (is-name? c) (or (is-name-first? c) (is-digit? c)))
(define (is-newline? c) (and (char? c) (or (char=? c #\newline) (char=? c #\cr))))

(define *reserved-words*
  '(return function end if then elseif else true false nil or and
    do while repeat until local for break in not))

(define (possible-keyword token)
  "Convert a symbol to a keyword if it is a reserved word in Lua"
  (if (memq token *reserved-words*)
      (symbol->keyword token)
      token))

(define (make-lexer port)
  ;; Buffer management
  (define buffer (open-output-string))

  (define (drop-buffer)
    "Clear the buffer and drop the contents"
    (truncate-file buffer 0))

  (define (clear-buffer)
    "Clear the buffer and return a string of the contents"
    (let ((string (get-output-string buffer)))
      (drop-buffer)
      string))

  ;; Source code information
  (define saved-source-info #f)

  (define (save-source-info)
    "Save source code information for a particular location e.g. the beginning
of an identifier"
    (set! saved-source-info (source-info port)))

  (define (get-source-info)
    "Get source code information"
    (or saved-source-info
        (source-info port)))

  (define (save-and-next!)
    "Shorthand for (write-char (read-char))"
    (write-char (read-char)))

  (define (eat-comment)
    "Consume a comment"
    (let consume ((c (read-char)))
      (cond ((eof-object? c) #f)
            ((eqv? c #\newline) #f)
            (else (consume (read-char))))))

  (define (get-long-string-nesting-level)
    "Return the nesting level of a bracketed string, or -1 if it is not one"
    (define delimiter (read-char))
    (let* ((count
            (let loop ((count 0))
              (if (eqv? (peek-char) #\=)
                  (begin
                    (read-char)
                    (loop (+ count 1)))
                  count))))
      (if (eqv? (peek-char) delimiter) count -1)))

  (define (read-long-string string? nest)
    "Read a long string or comment"
    ;; Skip second bracket
    (read-char)
    ;; Discard initial newlines, which is what Lua does
    (while (is-newline? (peek-char))
      (read-char))
    ;; Read string contents
    (let loop ((c (peek-char)))
      (cond
        ;; Error out if end-of-file is encountered
        ((eof-object? c)
         (syntax-error (get-source-info)
                       (string-append "unfinished long "
                                      (if string? "string" "comment"))))
        ;; Check to see if we've reached the end
        ((char=? c #\])
         (let* ((nest2 (get-long-string-nesting-level)))
           (if (= nest nest2)
               (begin
                 (read-char) ;; drop ]
                 (if string?
                     (clear-buffer)
                     (drop-buffer)))
               ;; Compensate for eating up the nesting levels
               (begin
                 (save-and-next!)
                 (let lp ((n nest2))
                   (if (= n 0)
                       #f
                       (begin
                         (write-char #\=)
                         (lp (- n 1)))))
                 (write-char #\])
                 (loop (peek-char))))))
        ;; Save character and continue
        (else (save-and-next!)
              (loop (peek-char))))))

  ;; read a single or double quoted string, with escapes
  (define (read-string delimiter)
    (read-char) ;; consume delimiter
    (let loop ((c (peek-char)))
      (cond
        ;; string ends early
        ((or (eof-object? c) (eqv? c #\cr) (eqv? c #\newline))
         (syntax-error (get-source-info) "unfinished string ~S" c))
        ;; string escape
        ((char=? c #\\)
         ;; discard \ and read next character
         (let* ((escape (begin (read-char) (read-char))))
           (write-char
            (case escape
              ((#\a) #\alarm)
              ((#\b) #\backspace)
              ((#\f) #\page)
              ((#\n) #\newline)
              ((#\r) #\return)
              ((#\t) #\tab)
              ((#\v) #\vtab)
              ((#\x) (syntax-error (get-source-info)
                                   "hex escapes unsupported"))
              ((#\d) (syntax-error (get-source-info)
                                   "decimal escapes unsupported"))
              (else escape)))
           (loop (peek-char))))
        (else
         (if (eqv? c delimiter)
             (read-char) ;; terminate loop and discard delimiter
             (begin
               (save-and-next!)
               (loop (peek-char)))))))
    (clear-buffer))

  (define (read-number string)
    (save-source-info)
    (let* ((main (string-append
                  (or string "")
                  (begin
                    (while (or (is-digit? (peek-char)) (eqv? (peek-char) #\.))
                      (save-and-next!))
                    (clear-buffer))))
           (exponent
            (if (or (eqv? (peek-char) #\e) (eqv? (peek-char) #\E))
                (begin
                  (read-char)
                  (if (eqv? (peek-char) #\+)
                      (read-char)
                      (if (eqv? (peek-char) #\-)
                          (save-and-next!)))
                  (if (not (is-digit? (peek-char)))
                      (syntax-error (get-source-info)
                                    "expecting number after exponent sign"))
                  (while (is-digit? (peek-char))
                         (save-and-next!))
                  (clear-buffer))
                #f))
           (final (string->number main)))
      (if exponent
          (* final (expt 10 (string->number exponent)))
          final)))

  (define (lex)
    (parameterize ((current-input-port port)
                   (current-output-port buffer))
      (set! saved-source-info #f)
      (let loop ()
        (define c (peek-char))
        (case c
          ;; Skip spaces
          ((#\newline #\return #\space #\page #\tab #\vtab) (read-char) (loop))

          ;; Either a minus (-), or a long comment, which is a -
          ;; followed by a bracketed string
          ((#\-)
           (read-char)
           (if (eqv? (peek-char) #\-)
               ;; It's a comment
               (begin
                 (read-char)
                 ;; Long comment
                 (if (eqv? (peek-char) #\[)
                     (let* ((nest (get-long-string-nesting-level)))
                       (drop-buffer)
                       (if (not (negative? nest))
                           (begin
                             (read-long-string #f nest)
                             (drop-buffer)
                             (loop))
                           ;; If it's not actually a long comment, drop it
                           (begin (drop-buffer) (eat-comment) (loop))))
                     (begin (eat-comment) (loop))))
               ;; It's a regular minus
               #\-))

          ;; ~=
          ((#\~)
           (read-char)
           (if (eqv? (peek-char) #\=)
               (begin (read-char) #:~=)
               (syntax-error (get-source-info)
                             "expected = after ~ but got ~c" c)))

          ;; < or <=
          ((#\<)
           (read-char)
           (if (eqv? (peek-char) #\=) (begin (read-char) #:<=) #\<))

          ;; > or >=
          ((#\>)
           (read-char)
           (if (eqv? (peek-char) #\=) (begin (read-char) #:>=) #\>))

          ;; = or ==
          ((#\=)
           (read-char)
           (if (eqv? (peek-char) #\=)
               (begin (read-char) #:==)
               #:=))

          ;; . can mean one of: floating point number (.12345), table
          ;; field access (plain .), concatenation operator (..) or the
          ;; variable argument indicator (...)
          ((#\.)
           (read-char)
           (if (is-digit? (peek-char))
               (read-number ".")
               (if (eqv? (peek-char) #\.)
                   (begin
                     (read-char)
                     (if (eqv? (peek-char) #\.)
                         (begin (read-char) #:dots)
                         #:concat))
                   #\.)))

          ;; Double-quoted string
          ((#\") (read-string #\"))

          ;; Single-quoted string
          ((#\') (read-string #\'))

          ;; Bracketed string
          ((#\[)
           (save-source-info)
           (let* ((nest (get-long-string-nesting-level)))
             (if (eqv? nest -1)
                 #\[
                 (read-long-string #t nest))))

          ;; Characters that are allowed to fall through directly to the
          ;; parser
          ((#\; #\( #\) #\,
            #\+ #\/ #\*
            #\^ #\{ #\} #\] #\: #\#) (read-char))

          ;; Numbers
          ((#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
           (save-source-info)
           (save-and-next!)
           (read-number #f))

          (else
           (cond ((eof-object? c) c)
                 ;; Identifier or keyword
                 ((is-name-first? c)
                  (save-and-next!)
                  (save-source-info)
                  (while (is-name? (peek-char))
                    (save-and-next!))
                  (possible-keyword (string->symbol (clear-buffer))))
                 (else
                  (syntax-error (get-source-info)
                                "disallowed character ~c" c))))))))

  (values get-source-info lex))
