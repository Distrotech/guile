;;; Guile RTL disassembler

;;; Copyright (C) 2001, 2009, 2010, 2012, 2013 Free Software Foundation, Inc.
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

(define-module (system vm disassembler)
  #:use-module (system vm instruction)
  #:use-module (system vm elf)
  #:use-module (system vm program)
  #:use-module (system vm objcode)
  #:use-module (system foreign)
  #:use-module (rnrs bytevectors)
  #:use-module (ice-9 format)
  #:use-module (ice-9 vlist)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-4)
  #:export (disassemble-program))

(define-syntax-rule (u32-ref buf n)
  (bytevector-u32-native-ref buf (* n 4)))

(define-syntax-rule (s32-ref buf n)
  (bytevector-s32-native-ref buf (* n 4)))

(define-syntax visit-opcodes
  (lambda (x)
    (syntax-case x ()
      ((visit-opcodes macro arg ...)
       (with-syntax (((inst ...)
                      (map (lambda (x) (datum->syntax #'macro x))
                           (rtl-instruction-list))))
         #'(begin
             (macro arg ... . inst)
             ...))))))

(eval-when (expand compile load eval)
  (define (id-append ctx a b)
    (datum->syntax ctx (symbol-append (syntax->datum a) (syntax->datum b)))))

(define-syntax join-subformats
  (lambda (x)
    (syntax-case x ()
      ((_)
       #f)
      ((_ #f rest ...)
       #'(join-subformats rest ...))
      ((_ (fmt arg ...))
       (string? (syntax->datum #'fmt))
       #'(list fmt arg ...))
      ((_ (fmt arg ...) #f rest ...)
       (string? (syntax->datum #'fmt))
       #'(join-subformats (fmt arg ...) rest ...))
      ((_ (fmt arg ...) (fmt* arg* ...) rest ...)
       (and (string? (syntax->datum #'fmt)) (string? (syntax->datum #'fmt*)))
       (let ((fmt** (string-append (syntax->datum #'fmt)
                                   ", "
                                   (syntax->datum #'fmt*))))
         #`(join-subformats (#,fmt** arg ... arg* ...) rest ...))))))

(define (unpack-immediate n)
  (pointer->scm (make-pointer n)))

(define (unpack-s24 s)
  (if (zero? (logand s (ash 1 23)))
      s
      (- s (ash 1 24))))

(define (unpack-s32 s)
  (if (zero? (logand s (ash 1 31)))
      s
      (- s (ash 1 32))))

(define-syntax disassembler
  (lambda (x)
    (define (parse-first-word word type)
      (with-syntax ((word word))
        (case type
          ((U8_X24)
           #'(()
              #f))
          ((U8_U24)
           #'(((ash word -8))
              #f))
          ((U8_L24)
           ;; Fixme: translate back to label
           #'(((unpack-s24 (ash word -8)))
              #f))
          ((U8_R24)
           ;; FIXME: parse rest instructions correctly
           #'(((ash word -8))
              #f))
          ((U8_U8_I16)
           #'(((logand (ash word -8) #xff)
               (ash word -16))
              ("~S" (unpack-immediate (ash word -16)))))
          ((U8_U12_U12)
           #'(((logand (ash word -8) #xfff)
               (ash word -20))
              #f))
          ((U8_U8_U8_U8)
           #'(((logand (ash word -8) #xff)
               (logand (ash word -16) #xff)
               (ash word -24))
              #f))
          (else
           (error "bad kind" type)))))

    (define (parse-tail-word word type)
      (with-syntax ((word word))
        (case type
          ((U8_X24)
           #'(((logand word #ff))
              #f))
          ((U8_U24)
           #'(((logand word #xff)
               (ash word -8))
              #f))
          ((U8_L24)
           ;; Fixme: translate back to label
           #'(((logand word #xff)
               (unpack-s24 (ash word -8)))
              #f))
          ((U8_R24)
           ;; FIXME: parse rest instructions correctly
           #'(((logand word #xff)
               (ash word -8))
              #f))
          ((U8_U8_I16)
           ;; FIXME: immediates
           #'(((logand word #xff)
               (logand (ash word -8) #xff)
               (ash word -16))
              ("~A" (unpack-immediate (ash word -16)))))
          ((U8_U12_U12)
           #'(((logand word #xff)
               (logand (ash word -8) #xfff)
               (ash word -20))
              #f))
          ((U8_U8_U8_U8)
           #'(((logand word #xff)
               (logand (ash word -8) #xff)
               (logand (ash word -16) #xff)
               (ash word -24))
              #f))
          ((U32)
           #'((word)
              #f))
          ((I32)
           ;; FIXME: immediates
           #'((word)
              ("~A" (unpack-immediate word))))
          ((A32)
           ;; FIXME: long immediates
           #'((word)
              #f))
          ((B32)
           ;; FIXME: long immediates
           #'((word)
              #f))
          ((N32)
           ;; FIXME: non-immediate
           #'(((unpack-s32 word))
              #f))
          ((S32)
           ;; FIXME: indirect access
           #'(((unpack-s32 word))
              #f))
          ((L32)
           ;; FIXME: offset
           #'(((unpack-s32 word))
              #f))
          ((LO32)
           ;; FIXME: offset
           #'(((unpack-s32 word))
              #f))
          ((X8_U24)
           #'(((ash word -8))
              #f))
          ((X8_U12_U12)
           #'(((logand (ash word -8) #xfff)
               (ash word -20))
              #f))
          ((X8_R24)
           ;; FIXME: rest
           #'(((ash word -8))
              #f))
          ((X8_L24)
           ;; FIXME: label
           #'(((unpack-s24 (ash word -8)))
              #f))
          ((U1_X7_L24)
           ;; FIXME: label
           #'(((logand word #x1)
               (unpack-s24 (ash word -8)))
              #f))
          ((U1_U7_L24)
           ;; FIXME: label
           #'(((logand word #x1)
               (logand (ash word -1) #x7f)
               (unpack-s24 (ash word -8)))
              #f))
          (else
           (error "bad kind" type)))))

    (syntax-case x ()
      ((_ name opcode word0 word* ...)
       (let ((vars (generate-temporaries #'(word* ...))))
         (with-syntax (((word* ...) vars)
                       ((n ...) (map 1+ (iota (length #'(word* ...)))))
                       (((asm ...) note)
                        (parse-first-word #'first (syntax->datum #'word0)))
                       ((((asm* ...) note*) ...)
                        (map (lambda (word type)
                               (parse-tail-word word type))
                             vars
                             (syntax->datum #'(word* ...)))))
           #'(lambda (buf offset first)
               (let ((word* (u32-ref buf (+ offset n)))
                     ...)
                 (values (+ 1 (length '(word* ...)))
                         (list 'name asm ... asm* ... ...)
                         (join-subformats note note* ...))))))))))

(define (disasm-invalid buf offset first)
  (error "bad instruction" (logand first #xff) first buf offset))

(define disassemblers (make-vector 256 disasm-invalid))

(define-syntax define-disassembler
  (lambda (x)
    (syntax-case x ()
      ((_ name opcode arg ...)
       (with-syntax ((parse (id-append #'name #'parse- #'name)))
         #'(let ((parse (disassembler name opcode arg ...)))
             (vector-set! disassemblers opcode parse)))))))

(visit-opcodes define-disassembler)

;; -> len list
(define (disassemble-one buf offset)
  (let ((first (u32-ref buf offset)))
    ((vector-ref disassemblers (logand first #xff)) buf offset first)))

(define (find-elf-symbol elf text-offset)
  (and=>
   (elf-section-by-name elf ".symtab")
   (lambda (symtab)
     (let ((len (elf-symbol-table-len symtab))
           (strtab (elf-section elf (elf-section-link symtab))))
       ;; The symbols should be sorted, but maybe somehow that fails
       ;; (for example if multiple objects are relinked together).  So,
       ;; a modicum of tolerance.
       (define (bisect)
         #f)
       (define (linear-search)
         (let lp ((n 0))
           (and (< n len)
                (let ((sym (elf-symbol-table-ref elf symtab n strtab)))
                  (if (and (<= (elf-symbol-value sym) text-offset)
                           (< text-offset (+ (elf-symbol-value sym)
                                             (elf-symbol-size sym))))
                      sym
                      (lp (1+ n)))))))
       (or (bisect) (linear-search))))))

(define (print-info port addr info extra src)
  (format port "~4@S    ~32S~@[;; ~1{~@?~}~]~@[~61t at ~a~]\n"
          addr info extra src))

(define* (disassemble-program program #:optional (port (current-output-port)))
  (let* ((code (rtl-program-code program))
         (bv (find-mapped-elf-image code))
         (elf (parse-elf bv))
         (base (pointer-address (bytevector->pointer (elf-bytes elf))))
         (text-base (elf-section-offset
                     (or (elf-section-by-name elf ".rtl-text")
                         (error "ELF object has no text section")))))
    (cond
     ((find-elf-symbol elf (- code base text-base))
      => (lambda (sym)
           ;; The text-base, symbol value, and symbol size are in bytes,
           ;; but the disassembler operates on u32 units.
           (let ((start (/ (+ (elf-symbol-value sym) text-base) 4))
                 (size (/ (elf-symbol-size sym) 4)))
             (format port "Disassembly of ~A at #x~X:\n\n"
                     (elf-symbol-name sym) code)
             (let lp ((offset 0))
               (when (< offset size)
                 (call-with-values (lambda ()
                                     (disassemble-one bv (+ start offset)))
                   (lambda (len elt extra)
                     (print-info port offset elt extra #f)
                     (lp (+ offset len)))))))))
     (else
      (format port "Debugging information unavailable.~%")))
    (values)))
