;;; Guile RTL assembler

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

(define-module (system vm assembler)
  #:use-module (system base target)
  #:use-module (system vm instruction)
  #:use-module (system vm elf)
  #:use-module (system vm linker)
  #:use-module (system vm objcode)
  #:use-module (rnrs bytevectors)
  #:use-module (ice-9 vlist)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-4)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-11)
  #:export (make-assembler
            emit-text
            link-assembly
            assemble-program))

(define-syntax-rule (pack-u8-u24 x y)
  (logior x (ash y 8)))

(define-syntax-rule (pack-u8-s24 x y)
  (logior x (ash (cond
                  ((< 0 (- y) #x800000)
                   (+ y #x1000000))
                  ((<= 0 y #xffffff)
                   y)
                  (else (error "out of range" y)))
                 8)))

(define-syntax-rule (pack-u1-u7-u24 x y z)
  (logior x (ash y 1) (ash z 8)))

(define-syntax-rule (pack-u8-u12-u12 x y z)
  (logior x (ash y 8) (ash z 20)))

(define-syntax-rule (pack-u8-u8-u16 x y z)
  (logior x (ash y 8) (ash z 16)))

(define-syntax-rule (pack-u8-u8-u8-u8 x y z w)
  (logior x (ash y 8) (ash z 16) (ash w 24)))

(define-record-type <meta>
  (make-meta name low-pc high-pc)
  meta?
  (name meta-name)
  (low-pc meta-low-pc)
  (high-pc meta-high-pc set-meta-high-pc!))

(define-syntax *block-size* (identifier-syntax 32))

;; We'll use native endianness when writing bytecode.  If we're
;; targeting a foreign endianness, we byte-swap the bytevector as a
;; whole instead of conditionalizing each access.
;;
;; We write constants using the target endianness, though.
;;
(define-record-type <asm>
  (make-asm cur idx start prev written
            labels relocs
            word-size endianness
            constants inits
            string-table
            meta)
  asm?
  (cur asm-cur set-asm-cur!)
  (idx asm-idx set-asm-idx!)
  (start asm-start set-asm-start!)
  (prev asm-prev set-asm-prev!)
  (written asm-written set-asm-written!)
  (labels asm-labels set-asm-labels!)
  (relocs asm-relocs set-asm-relocs!)
  (word-size asm-word-size)
  (endianness asm-endianness)
  ;; Vhash of object -> label.  Order is important.
  (constants asm-constants set-asm-constants!)
  (inits asm-inits set-asm-inits!)
  (string-table asm-string-table set-asm-string-table!)
  (meta asm-meta set-asm-meta!))

(define-inlinable (fresh-block)
  (make-u32vector *block-size*))

(define* (make-assembler #:key (word-size (target-word-size))
                         (endianness (target-endianness)))
  (make-asm (fresh-block) 0 0 '() 0
            '() '()
            word-size endianness
            vlist-null '()
            (make-string-table)
            '()))

(define (intern-string! asm string)
  (call-with-values
      (lambda () (string-table-intern (asm-string-table asm) string))
    (lambda (table idx)
      (set-asm-string-table! asm table)
      idx)))

(define-inlinable (asm-pos asm)
  (+ (asm-idx asm) (asm-written asm)))

(define (allocate-new-block asm)
  (let ((new (fresh-block)))
    (set-asm-prev! asm (cons (asm-cur asm) (asm-prev asm)))
    (set-asm-written! asm (asm-pos asm))
    (set-asm-cur! asm new)
    (set-asm-idx! asm 0)))

(define-syntax-rule (u32-ref buf n)
  (bytevector-u32-native-ref buf (* n 4)))

(define-syntax-rule (u32-set! buf n val)
  (bytevector-u32-native-set! buf (* n 4) val))

(define-syntax-rule (s32-ref buf n)
  (bytevector-s32-native-ref buf (* n 4)))

(define-syntax-rule (s32-set! buf n val)
  (bytevector-s32-native-set! buf (* n 4) val))

(define-inlinable (emit asm u32)
  (u32-set! (asm-cur asm) (asm-idx asm) u32)
  (set-asm-idx! asm (1+ (asm-idx asm)))
  (if (= (asm-idx asm) *block-size*)
      (allocate-new-block asm)))

(define-inlinable (make-reloc type label base word)
  (list type label base word))

(define-inlinable (reset-asm-start! asm)
  (set-asm-start! asm (asm-pos asm)))

(define (emit-exported-label asm label)
  (set-asm-labels! asm (acons label (asm-start asm) (asm-labels asm))))

(define (record-label-reference asm label)
  (let* ((start (asm-start asm))
         (pos (asm-pos asm))
         (reloc (make-reloc 'x8-s24 label start (- pos start))))
    (set-asm-relocs! asm (cons reloc (asm-relocs asm)))))

(define* (record-far-label-reference asm label #:optional (offset 0))
  (let* ((start (- (asm-start asm) offset))
         (pos (asm-pos asm))
         (reloc (make-reloc 's32 label start (- pos start))))
    (set-asm-relocs! asm (cons reloc (asm-relocs asm)))))

(eval-when (expand compile load eval)
  (define (id-append ctx a b)
    (datum->syntax ctx (symbol-append (syntax->datum a) (syntax->datum b)))))

(define-syntax assembler
  (lambda (x)
    (define-syntax op-case
      (lambda (x)
        (syntax-case x ()
          ((_ asm name ((type arg ...) code ...) clause ...)
           #`(if (eq? name 'type)
                 (with-syntax (((arg ...) (generate-temporaries #'(arg ...))))
                   #'((arg ...)
                      code ...))
                 (op-case asm name clause ...)))
          ((_ asm name)
           #'(error "unmatched name" 'name)))))

    (define (pack-first-word asm opcode type)
      (with-syntax ((opcode opcode))
        (op-case
         asm type
         ((U8_X24)
          (emit asm opcode))
         ((U8_U24 arg)
          (emit asm (pack-u8-u24 opcode arg)))
         ((U8_L24 label)
          (record-label-reference asm label)
          (emit asm opcode))
         ((U8_R24 rest)
          (emit asm (pack-u8-u24 opcode (list rest)))
          (for-each (lambda (x) (emit asm x)) rest))
         ((U8_U8_I16 a imm)
          (emit asm (pack-u8-u8-u16 opcode a (object-address imm))))
         ((U8_U12_U12 a b)
          (emit asm (pack-u8-u12-u12 opcode a b)))
         ((U8_U8_U8_U8 a b c)
          (emit asm (pack-u8-u8-u8-u8 opcode a b c))))))

    (define (pack-tail-word asm type)
      (op-case
       asm type
       ((U8_U24 a b)
        (emit asm (pack-u8-u24 a b)))
       ((U8_L24 a label)
        (record-label-reference asm label)
        (emit asm a))
       ((U8_R24 rest)
        (emit asm (pack-u8-u24 a (length rest)))
        (for-each (lambda (x) (emit asm x)) rest))
       ((U8_U8_I16 a b imm)
        (emit asm (pack-u8-u8-u16 a b (object-address imm))))
       ((U8_U12_U12 a b)
        (emit asm (pack-u8-u12-u12 a b c)))
       ((U8_U8_U8_U8 a b c d)
        (emit asm (pack-u8-u8-u8-u8 a b c d)))
       ((U32 a)
        (emit asm a))
       ((I32 imm)
        (let ((val (object-address imm)))
          (unless (zero? (ash val -32))
            (error "FIXME: enable truncation of negative fixnums when cross-compiling"))
          (emit asm val)))
       ((A32 imm)
        (unless (= (asm-word-size asm) 8)
          (error "make-long-immediate unavailable for this target"))
        (emit asm (ash (object-address imm) -32))
        (emit asm (logand (object-address imm) (1- (ash 1 32)))))
       ((B32))
       ((N32 label)
        (record-far-label-reference asm label)
        (emit asm 0))
       ((S32 label)
        (record-far-label-reference asm label)
        (emit asm 0))
       ((L32 label)
        (record-far-label-reference asm label)
        (emit asm 0))
       ((LO32 label offset)
        (record-far-label-reference asm label
                                    (* offset (/ (asm-word-size asm) 4)))
        (emit asm 0))
       ((X8_U24 a)
        (emit asm (pack-u8-u24 0 a)))
       ((X8_U12_U12 a b)
        (emit asm (pack-u8-u12-u12 0 a b)))
       ((X8_R24 rest)
        (emit asm (pack-u8-u24 0 (length rest)))
        (for-each (lambda (x) (emit asm x)) rest))
       ((X8_L24 label)
        (record-label-reference asm label)
        (emit asm 0))
       ((B1_X7_L24 a label)
        (record-label-reference asm label)
        (emit asm (pack-u1-u7-u24 (if a 1 0) 0 0)))
       ((B1_U7_L24 a b label)
        (record-label-reference asm label)
        (emit asm (pack-u1-u7-u24 (if a 1 0) b 0)))))

    (syntax-case x ()
      ((_ name opcode word0 word* ...)
       (with-syntax ((((formal0 ...)
                       code0 ...)
                      (pack-first-word #'asm
                                       (syntax->datum #'opcode)
                                       (syntax->datum #'word0)))
                     ((((formal* ...)
                        code* ...) ...)
                      (map (lambda (word) (pack-tail-word #'asm word))
                           (syntax->datum #'(word* ...)))))
         #'(lambda (asm formal0 ... formal* ... ...)
             (unless (asm? asm) (error "not an asm"))
             code0 ...
             code* ... ...
             (reset-asm-start! asm)))))))

(define assemblers (make-hash-table))

(define-syntax define-assembler
  (lambda (x)
    (syntax-case x ()
      ((_ name opcode arg ...)
       (with-syntax ((emit (id-append #'name #'emit- #'name)))
         #'(define emit
             (let ((emit (assembler name opcode arg ...)))
               (hashq-set! assemblers 'name emit)
               emit)))))))

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

(visit-opcodes define-assembler)

(define-inlinable (immediate? x)
  (not (zero? (logand (object-address x) 6))))

(define-record-type <stringbuf>
  (make-stringbuf string)
  stringbuf?
  (string stringbuf-string))

(define-record-type <static-procedure>
  (make-static-procedure code)
  static-procedure?
  (code static-procedure-code))

;; Used for cells that cache the module that was current when a toplevel
;; closure was created, or for toplevel refs within a procedure.
(define-record-type <cache-cell>
  (make-cache-cell scope key)
  cache-cell?
  (scope cache-cell-scope)
  (key cache-cell-key))

(define (statically-allocatable? x)
  (or (pair? x) (vector? x) (string? x) (stringbuf? x) (static-procedure? x)))

(define (intern-constant asm obj)
  (define (recur obj)
    (intern-constant asm obj))
  (define (field dst n obj)
    (let ((src (recur obj)))
      (if src
          (list (if (statically-allocatable? obj)
                    `(make-non-immediate 0 ,src)
                    `(static-ref 0 ,src))
                `(static-set! 0 ,dst ,n))
          '())))
  (define (intern obj label)
    (cond
     ((pair? obj)
      (append (field label 0 (car obj))
              (field label 1 (cdr obj))))
     ((vector? obj)
      (let lp ((i 0) (inits '()))
        (if (< i (vector-length obj))
            (lp (1+ i)
                (append-reverse (field label (1+ i) (vector-ref obj i))
                                inits))
            (reverse inits))))
     ((stringbuf? obj) '())
     ((static-procedure? obj)
      `((make-non-immediate 0 ,label)
        (link-procedure! 0 ,(static-procedure-code obj))))
     ((cache-cell? obj) '())
     ((symbol? obj)
      `((make-non-immediate 0 ,(recur (symbol->string obj)))
        (string->symbol 0 0)
        (static-set! 0 ,label 0)))
     ((string? obj)
      `((make-non-immediate 0 ,(recur (make-stringbuf obj)))
        (static-set! 0 ,label 1)))
     ((keyword? obj)
      `((static-ref 0 ,(recur (keyword->symbol obj)))
        (symbol->keyword 0 0)
        (static-set! 0 ,label 0)))
     ((number? obj)
      `((make-non-immediate 0 ,(recur (number->string obj)))
        (string->number 0 0)
        (static-set! 0 ,label 0)))
     (else
      (error "don't know how to intern" obj))))
  (cond
   ((immediate? obj) #f)
   ((vhash-assoc obj (asm-constants asm)) => cdr)
   (else
    ;; Note that calling intern may mutate asm-constants and
    ;; asm-constant-inits.
    (let* ((label (gensym "constant"))
           (inits (intern obj label)))
      (set-asm-constants! asm (vhash-cons obj label (asm-constants asm)))
      (set-asm-inits! asm (append-reverse inits (asm-inits asm)))
      label))))

;; Returns a label.
(define (emit-non-immediate asm obj)
  (when (immediate? obj)
    (error "expected a non-immediate" obj))
  (intern-constant asm obj))

;; Returns a label.  Resolutions of the same key within the same scope
;; share a cell.
(define (emit-cache-cell asm scope key)
  (intern-constant asm (make-cache-cell scope key)))

;; Return the label of the cell that holds the module for a scope.
(define (emit-module-cache-cell asm scope)
  (emit-cache-cell asm scope #t))

(define-syntax define-macro-assembler
  (lambda (x)
    (syntax-case x ()
      ((_ (name arg ...) body body* ...)
       (with-syntax ((emit (id-append #'name #'emit- #'name)))
         #'(define emit
             (let ((emit (lambda (arg ...) body body* ...)))
               (hashq-set! assemblers 'name emit)
               emit)))))))

(define-macro-assembler (load-constant asm dst obj)
  (cond
   ((immediate? obj)
    (let ((bits (object-address obj)))
      (cond
       ((and (< dst 256) (zero? (ash bits -16)))
        (emit-make-short-immediate asm dst obj))
       ((zero? (ash bits -32))
        (emit-make-long-immediate asm dst obj))
       (else
        (emit-make-long-long-immediate asm dst obj)))))
   ((statically-allocatable? obj)
    (emit-make-non-immediate asm dst (emit-non-immediate asm obj)))
   (else
    (emit-static-ref asm dst (emit-non-immediate asm obj)))))

(define-macro-assembler (load-static-procedure asm dst label)
  (let ((loc (intern-constant asm (make-static-procedure label))))
    (emit-make-non-immediate asm dst loc)))

(define-macro-assembler (begin-program asm label)
  (emit-label asm label)
  (let ((meta (make-meta label (asm-start asm) #f)))
    (set-asm-meta! asm (cons meta (asm-meta asm)))))

(define-macro-assembler (end-program asm)
  (set-meta-high-pc! (car (asm-meta asm)) (asm-start asm)))

(define-macro-assembler (label asm sym)
  (set-asm-labels! asm (acons sym (asm-start asm) (asm-labels asm))))

(define-macro-assembler (cache-current-module! asm tmp scope)
  (let ((mod-label (emit-module-cache-cell asm scope)))
    (emit-current-module asm tmp)
    (emit-static-set! asm tmp mod-label 0)))

(define-macro-assembler (cached-toplevel-ref asm dst scope sym)
  (let ((sym-label (emit-non-immediate asm sym))
        (mod-label (emit-module-cache-cell asm scope))
        (cell-label (emit-cache-cell asm scope sym)))
    (emit-toplevel-ref asm dst cell-label mod-label sym-label)))

(define-macro-assembler (cached-toplevel-set! asm src scope sym)
  (let ((sym-label (emit-non-immediate asm sym))
        (mod-label (emit-module-cache-cell asm scope))
        (cell-label (emit-cache-cell asm scope sym)))
    (emit-toplevel-set! asm src cell-label mod-label sym-label)))

(define-macro-assembler (cached-module-ref asm dst module-name public? sym)
  (let* ((sym-label (emit-non-immediate asm sym))
         (key (cons public? module-name))
         (mod-name-label (intern-constant asm key))
         (cell-label (emit-cache-cell asm key sym)))
    (emit-module-ref asm dst cell-label mod-name-label sym-label)))

(define-macro-assembler (cached-module-set! asm src module-name public? sym)
  (let* ((sym-label (emit-non-immediate asm sym))
         (key (cons public? module-name))
         (mod-name-label (emit-non-immediate asm key))
         (cell-label (emit-cache-cell asm key sym)))
    (emit-module-set! asm src cell-label mod-name-label sym-label)))

(define (emit-text asm instructions)
  (for-each (lambda (inst)
              (apply (or (hashq-ref assemblers (car inst))
                         (error 'bad-instruction inst))
                     asm
                     (cdr inst)))
            instructions))

(define (process-relocs buf relocs labels)
  (fold
   (lambda (reloc tail)
     (let ((abs (assq-ref labels (cadr reloc)))
           (dst (+ (caddr reloc) (cadddr reloc))))
       (case (car reloc)
         ((s32)
          (if abs
              (let ((rel (- abs (caddr reloc))))
                (s32-set! buf dst rel)
                tail)
              (cons (make-linker-reloc
                     'rel32/4 (* dst 4) (cadddr reloc) (cadr reloc))
                    tail)))
         ((x8-s24)
          (unless abs
            (error "unbound near relocation" reloc))
          (let ((rel (- abs (caddr reloc)))
                (u32 (u32-ref buf dst)))
            (u32-set! buf dst (pack-u8-s24 (logand u32 #xff) rel))
            tail))
         (else (error "what" reloc)))))
   '()
   relocs))

(define (process-labels labels)
  (map (lambda (pair)
         (make-linker-symbol (car pair) (* (cdr pair) 4)))
       labels))

(define (swap-bytes! buf)
  (unless (zero? (modulo (bytevector-length buf) 4))
    (error "unexpected length"))
  (let ((byte-len (bytevector-length buf)))
    (let lp ((pos 0))
      (unless (= pos byte-len)
        (bytevector-u32-set!
         buf pos
         (bytevector-u32-ref buf pos (endianness big))
         (endianness little))
        (lp (+ pos 4))))))

(define (make-object asm name bv relocs labels . kwargs)
  (let ((name-idx (intern-string! asm (symbol->string name))))
    (make-linker-object (apply make-elf-section
                               #:name name-idx
                               #:size (bytevector-length bv)
                               kwargs)
                        bv relocs
                        (cons (make-linker-symbol name 0) labels))))

(define (link-text-object asm)
  (let ((buf (make-u32vector (asm-pos asm))))
    (let lp ((pos 0) (prev (reverse (asm-prev asm))))
      (if (null? prev)
          (let ((byte-size (* (asm-idx asm) 4)))
            (bytevector-copy! (asm-cur asm) 0 buf pos byte-size)
            (unless (eq? (asm-endianness asm) (native-endianness))
              (swap-bytes! buf))
            (make-object asm '.rtl-text
                         buf
                         (process-relocs buf (asm-relocs asm)
                                         (asm-labels asm))
                         (process-labels (asm-labels asm))))
          (let ((len (* *block-size* 4)))
            (bytevector-copy! (car prev) 0 buf pos len)
            (lp (+ pos len) (cdr prev)))))))

(define (link-dynamic-section asm text ro rw rw-init)
  (define-syntax-rule (emit-dynamic-section word-size %set-uword! reloc-type)
    (let* ((endianness (asm-endianness asm))
           (bv (make-bytevector (* word-size (if rw (if rw-init 12 10) 6)) 0))
           (set-uword!
            (lambda (i uword)
              (%set-uword! bv (* i word-size) uword endianness)))
           (relocs '())
           (set-label!
            (lambda (i label)
              (set! relocs (cons (make-linker-reloc 'reloc-type
                                                    (* i word-size) 0 label)
                                 relocs))
              (%set-uword! bv (* i word-size) 0 endianness))))
      (set-uword! 0 DT_GUILE_RTL_VERSION)
      (set-uword! 1 #x02020000)
      (set-uword! 2 DT_GUILE_ENTRY)
      (set-label! 3 '.rtl-text)
      (cond
       (rw
        ;; Add roots to GC.
        (set-uword! 4 DT_GUILE_GC_ROOT)
        (set-label! 5 '.data)
        (set-uword! 6 DT_GUILE_GC_ROOT_SZ)
        (set-uword! 7 (bytevector-length (linker-object-bv rw)))
        (cond
         (rw-init
          (set-uword! 8 DT_INIT)        ; constants
          (set-label! 9 rw-init)
          (set-uword! 10 DT_NULL)
          (set-uword! 11 0))
         (else
          (set-uword! 8 DT_NULL)
          (set-uword! 9 0))))
       (else
        (set-uword! 4 DT_NULL)
        (set-uword! 5 0)))
      (make-object asm '.dynamic bv relocs '()
                   #:type SHT_DYNAMIC #:flags SHF_ALLOC)))
  (case (asm-word-size asm)
    ((4) (emit-dynamic-section 4 bytevector-u32-set! abs32/1))
    ((8) (emit-dynamic-section 8 bytevector-u64-set! abs64/1))
    (else (error "bad word size" asm))))

(define (link-shstrtab asm)
  (intern-string! asm ".shstrtab")
  (make-object asm '.shstrtab
               (link-string-table (asm-string-table asm))
               '() '()
               #:type SHT_STRTAB #:flags 0))

(define (write-immediate asm buf pos x)
  (let ((val (object-address x))
        (endianness (asm-endianness asm)))
    (case (asm-word-size asm)
      ((4) (bytevector-u32-set! buf pos val endianness))
      ((8) (bytevector-u64-set! buf pos val endianness))
      (else (error "bad word size" asm)))))

(define (emit-init-constants asm)
  (let ((inits (asm-inits asm)))
    (and (not (null? inits))
         (let ((label (gensym "init-constants")))
           (emit-text asm
                      `((begin-program ,label)
                        (assert-nargs-ee/locals 0 1)
                        ,@(reverse inits)
                        (load-constant 0 ,*unspecified*)
                        (return 0)
                        (end-program)))
           label))))

(define (link-data asm data name)
  (define (align address alignment)
    (+ address
       (modulo (- alignment (modulo address alignment)) alignment)))

  (define tc7-vector 13)
  (define tc7-narrow-stringbuf 39)
  (define tc7-wide-stringbuf (+ 39 #x400))
  (define tc7-ro-string (+ 21 #x200))
  (define tc7-rtl-program 69)

  (let ((word-size (asm-word-size asm))
        (endianness (asm-endianness asm)))
    (define (byte-length x)
      (cond
       ((stringbuf? x)
        (let ((x (stringbuf-string x)))
          (+ (* 2 word-size)
             (case (string-bytes-per-char x)
               ((1) (1+ (string-length x)))
               ((4) (* (1+ (string-length x)) 4))
               (else (error "bad string bytes per char" x))))))
       ((static-procedure? x)
        (* 2 word-size))
       ((string? x)
        (* 4 word-size))
       ((pair? x)
        (* 2 word-size))
       ((vector? x)
        (* (1+ (vector-length x)) word-size))
       (else
        word-size)))

    (define (write-constant-reference buf pos x)
      ;; The asm-inits will fix up any reference to a non-immediate.
      (write-immediate asm buf pos (if (immediate? x) x #f)))

    (define (write buf pos obj)
      (cond
       ((stringbuf? obj)
        (let* ((x (stringbuf-string obj))
               (len (string-length x))
               (tag (if (= (string-bytes-per-char x) 1)
                        tc7-narrow-stringbuf
                        tc7-wide-stringbuf)))
          (case word-size
            ((4)
             (bytevector-u32-set! buf pos tag endianness)
             (bytevector-u32-set! buf (+ pos 4) len endianness))
            ((8)
             (bytevector-u64-set! buf pos tag endianness)
             (bytevector-u64-set! buf (+ pos 8) len endianness))
            (else
             (error "bad word size" asm)))
          (let ((pos (+ pos (* word-size 2))))
            (case (string-bytes-per-char x)
              ((1)
               (let lp ((i 0))
                 (if (< i len)
                     (let ((u8 (char->integer (string-ref x i))))
                       (bytevector-u8-set! buf (+ pos i) u8)
                       (lp (1+ i)))
                     (bytevector-u8-set! buf (+ pos i) 0))))
              ((4)
               (let lp ((i 0))
                 (if (< i len)
                     (let ((u32 (char->integer (string-ref x i))))
                       (bytevector-u32-set! buf (+ pos (* i 4)) u32 endianness)
                       (lp (1+ i)))
                     (bytevector-u32-set! buf (+ pos (* i 4)) 0 endianness))))
              (else (error "bad string bytes per char" x))))))

       ((static-procedure? obj)
        (case word-size
          ((4)
           (bytevector-u32-set! buf pos tc7-rtl-program endianness)
           (bytevector-u32-set! buf (+ pos 4) 0 endianness))
          ((8)
           (bytevector-u64-set! buf pos tc7-rtl-program endianness)
           (bytevector-u64-set! buf (+ pos 8) 0 endianness))
          (else (error "bad word size"))))

       ((cache-cell? obj)
        (write-immediate asm buf pos #f))

       ((string? obj)
        (let ((tag (logior tc7-ro-string (ash (string-length obj) 8))))
          (case word-size
            ((4)
             (bytevector-u32-set! buf pos tc7-ro-string endianness)
             (write-immediate asm buf (+ pos 4) #f) ; stringbuf
             (bytevector-u32-set! buf (+ pos 8) 0 endianness)
             (bytevector-u32-set! buf (+ pos 12) (string-length obj) endianness))
            ((8)
             (bytevector-u64-set! buf pos tc7-ro-string endianness)
             (write-immediate asm buf (+ pos 8) #f) ; stringbuf
             (bytevector-u64-set! buf (+ pos 16) 0 endianness)
             (bytevector-u64-set! buf (+ pos 24) (string-length obj) endianness))
            (else (error "bad word size")))))

       ((pair? obj)
        (write-constant-reference buf pos (car obj))
        (write-constant-reference buf (+ pos word-size) (cdr obj)))

       ((vector? obj)
        (let* ((len (vector-length obj))
               (tag (logior tc7-vector (ash len 8))))
          (case word-size
            ((4) (bytevector-u32-set! buf pos tag endianness))
            ((8) (bytevector-u64-set! buf pos tag endianness))
            (else (error "bad word size")))
          (let lp ((i 0))
            (when (< i (vector-length obj))
              (let ((pos (+ pos word-size (* i word-size)))
                    (elt (vector-ref obj i)))
                (write-constant-reference buf pos elt)
                (lp (1+ i)))))))

       ((symbol? obj)
        (write-immediate asm buf pos #f))

       ((keyword? obj)
        (write-immediate asm buf pos #f))

       ((number? obj)
        (write-immediate asm buf pos #f))

       (else
        (error "unrecognized object" obj))))

    (cond
     ((vlist-null? data) #f)
     (else
      (let* ((byte-len (vhash-fold (lambda (k v len)
                                     (+ (byte-length k) (align len 8)))
                                   0 data))
             (buf (make-bytevector byte-len 0)))
        (let lp ((i 0) (pos 0) (labels '()))
          (if (< i (vlist-length data))
              (let* ((pair (vlist-ref data i))
                     (obj (car pair))
                     (obj-label (cdr pair)))
                (write buf pos obj)
                (lp (1+ i)
                    (align (+ (byte-length obj) pos) 8)
                    (cons (make-linker-symbol obj-label pos) labels)))
              (make-object asm name buf '() labels))))))))

;; Hummm
;; 
(define (link-constants asm)
  ;; Possibly three sections: one containing shareable read-only data,
  ;; one containing data that might be written to, and one text section
  ;; to initialize the pointers in the rwdata.
  ;;
  (define (shareable? x)
    (cond
     ((stringbuf? x) #t)
     ((pair? x)
      (and (immediate? (car x)) (immediate? (cdr x))))
     ((vector? x)
      (let lp ((i 0))
        (or (= i (vector-length x))
            (and (immediate? (vector-ref x i))
                 (lp (1+ i))))))
     (else #f)))
  (let* ((constants (asm-constants asm))
         (len (vlist-length constants)))
    (let lp ((i 0)
             (ro vlist-null)
             (rw vlist-null))
      (if (= i len)
          (values (link-data asm ro '.rodata)
                  (link-data asm rw '.data)
                  (emit-init-constants asm))
          (let ((pair (vlist-ref constants i)))
            (if (shareable? (car pair))
                (lp (1+ i) (vhash-consq (car pair) (cdr pair) ro) rw)
                (lp (1+ i) ro (vhash-consq (car pair) (cdr pair) rw))))))))

(define (link-symtab text-section asm)
  (let* ((endianness (asm-endianness asm))
         (word-size (asm-word-size asm))
         (size (elf-symbol-len word-size))
         (meta (reverse (asm-meta asm)))
         (n (length meta))
         (strtab (make-string-table))
         (bv (make-bytevector (* n size) 0)))
    (define (intern-string! name)
      (call-with-values
          (lambda () (string-table-intern strtab (symbol->string name)))
        (lambda (table idx)
          (set! strtab table)
          idx)))
    (for-each
     (lambda (meta n)
       (let ((name (intern-string! (meta-name meta))))
         (write-elf-symbol bv (* n size) endianness word-size
                           (make-elf-symbol
                            #:name name
                            ;; Symbol value and size are measured in
                            ;; bytes, not u32s.
                            #:value (* 4 (meta-low-pc meta))
                            #:size (* 4 (- (meta-high-pc meta)
                                           (meta-low-pc meta)))
                            #:type STT_FUNC
                            #:visibility STV_HIDDEN
                            #:shndx (elf-section-index text-section)))))
     meta (iota n))
    (let ((strtab (make-object asm '.strtab
                               (link-string-table strtab)
                               '() '()
                               #:type SHT_STRTAB #:flags 0)))
      (values (make-object asm '.symtab
                           bv
                           '() '()
                           #:type SHT_SYMTAB #:flags 0 #:entsize size
                           #:link (elf-section-index
                                   (linker-object-section strtab)))
              strtab))))

(define (link-objects asm)
  (let*-values (((ro rw rw-init) (link-constants asm))
                ;; Link text object after constants, so that the
                ;; constants initializer gets included.
                ((text) (link-text-object asm))
                ((dt) (link-dynamic-section asm text ro rw rw-init))
                ((symtab strtab) (link-symtab (linker-object-section text) asm))
                ;; This needs to be linked last, because linking other
                ;; sections adds entries to the string table.
                ((shstrtab) (link-shstrtab asm)))
    (filter identity (list text ro rw dt symtab strtab shstrtab))))

(define (link-assembly asm)
  (link-elf (link-objects asm)))

(define (assemble-program instructions)
  (let ((asm (make-assembler)))
    (emit-text asm instructions)
    (load-thunk-from-memory
     (link-elf (link-objects asm) #:page-aligned? #f))))
