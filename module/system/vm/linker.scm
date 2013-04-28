;;; Guile ELF linker

;; Copyright (C)  2011, 2012, 2013 Free Software Foundation, Inc.

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

;;; Commentary:
;;;
;;; A linker combines several linker objects into an executable or a
;;; loadable library.
;;;
;;; There are several common formats for libraries out there.  Since
;;; Guile includes its own linker and loader, we are free to choose any
;;; format, or make up our own.
;;;
;;; There are essentially two requirements for a linker format:
;;; libraries should be able to be loaded with the minimal amount of
;;; work; and they should support introspection in some way, in order to
;;; enable good debugging.
;;;
;;; These requirements are somewhat at odds, as loading should not have
;;; to stumble over features related to introspection.  It so happens
;;; that a lot of smart people have thought about this situation, and
;;; the ELF format embodies the outcome of their thinking.  Guile uses
;;; ELF as its format, regardless of the platform's native library
;;; format.  It's not inconceivable that Guile could interoperate with
;;; the native dynamic loader at some point, but it's not a near-term
;;; goal.
;;;
;;; Guile's linker takes a list of objects, sorts them according to
;;; similarity from the perspective of the loader, then writes them out
;;; into one big bytevector in ELF format.
;;;
;;; It is often the case that different parts of a library need to refer
;;; to each other.  For example, program text may need to refer to a
;;; constant from writable memory.  When the linker places sections
;;; (linker objects) into specific locations in the linked bytevector,
;;; it needs to fix up those references.  This process is called
;;; /relocation/.  References needing relocations are recorded in
;;; "linker-reloc" objects, and collected in a list in each
;;; "linker-object".  The actual definitions of the references are
;;; stored in "linker-symbol" objects, also collected in a list in each
;;; "linker-object".
;;;
;;; By default, the ELF files created by the linker include some padding
;;; so that different parts of the file can be loaded in with different
;;; permissions.  For example, some parts of the file are read-only and
;;; thus can be shared between processes.  Some parts of the file don't
;;; need to be loaded at all.  However this padding can be too much for
;;; interactive compilation, when the code is never written out to disk;
;;; in that case, pass #:page-aligned? #f to `link-elf'.
;;;
;;; Code:

(define-module (system vm linker)
  #:use-module (rnrs bytevectors)
  #:use-module (system foreign)
  #:use-module (system base target)
  #:use-module ((srfi srfi-1) #:select (append-map))
  #:use-module (srfi srfi-9)
  #:use-module (ice-9 receive)
  #:use-module (ice-9 vlist)
  #:use-module (ice-9 match)
  #:use-module (system vm elf)
  #:export (make-linker-reloc
            make-linker-symbol

            make-linker-object
            linker-object?
            linker-object-section
            linker-object-bv
            linker-object-relocs
            (linker-object-symbols* . linker-object-symbols)

            make-string-table
            string-table-intern
            link-string-table

            link-elf))

;; A relocation records a reference to a symbol.  When the symbol is
;; resolved to an address, the reloc location will be updated to point
;; to the address.
;;
;; Two types.  Abs32/1 and Abs64/1 are absolute offsets in bytes.
;; Rel32/4 is a relative signed offset in 32-bit units.  Either can have
;; an arbitrary addend as well.
;;
(define-record-type <linker-reloc>
  (make-linker-reloc type loc addend symbol)
  linker-reloc?
  (type linker-reloc-type) ;; rel32/4, abs32/1, abs64/1
  (loc linker-reloc-loc)
  (addend linker-reloc-addend)
  (symbol linker-reloc-symbol))

;; A symbol is an association between a name and an address.  The
;; address is always in regard to some particular address space.  When
;; objects come into the linker, their symbols live in the object
;; address space.  When the objects are allocated into ELF segments, the
;; symbols will be relocated into memory address space, corresponding to
;; the position the ELF will be loaded at.
;;
(define-record-type <linker-symbol>
  (make-linker-symbol name address)
  linker-symbol?
  (name linker-symbol-name)
  (address linker-symbol-address))

(define-record-type <linker-object>
  (%make-linker-object section bv relocs symbols)
  linker-object?
  (section linker-object-section)
  (bv linker-object-bv)
  (relocs linker-object-relocs)
  (symbols linker-object-symbols))

;; Hide a symbol to the beginning of the section in the symbols.
(define (make-linker-object section bv relocs symbols)
  (%make-linker-object section bv relocs
                       (cons (make-linker-symbol (gensym "*section*") 0)
                             symbols)))
(define (linker-object-section-symbol object)
  (car (linker-object-symbols object)))
(define (linker-object-symbols* object)
  (cdr (linker-object-symbols object)))

(define (make-string-table)
  '(("" 0 #vu8())))

(define (string-table-length table)
  (let ((last (car table)))
    ;; The + 1 is for the trailing NUL byte.
    (+ (cadr last) (bytevector-length (caddr last)) 1)))

(define (string-table-intern table str)
  (cond
   ((assoc str table)
    => (lambda (ent)
         (values table (cadr ent))))
   (else
    (let* ((next (string-table-length table)))
      (values (cons (list str next (string->utf8 str))
                    table)
              next)))))

(define (link-string-table table)
  (let ((out (make-bytevector (string-table-length table) 0)))
    (for-each
     (lambda (ent)
       (let ((bytes (caddr ent)))
         (bytevector-copy! bytes 0 out (cadr ent) (bytevector-length bytes))))
     table)
    out))

(define (segment-kind section)
  (let ((flags (elf-section-flags section)))
    (cons (cond
           ((= (elf-section-type section) SHT_DYNAMIC) PT_DYNAMIC)
           ;; Sections without SHF_ALLOC don't go in segments.
           ((zero? flags) #f)
           (else PT_LOAD))
          (logior (if (zero? (logand SHF_ALLOC flags))
                      0
                      PF_R)
                  (if (zero? (logand SHF_EXECINSTR flags))
                      0
                      PF_X)
                  (if (zero? (logand SHF_WRITE flags))
                      0
                      PF_W)))))

(define (count-segments objects)
  (length
   (fold1 (lambda (object kinds)
            (let ((kind (segment-kind (linker-object-section object))))
              (if (and (car kind) (not (member kind kinds)))
                  (cons kind kinds)
                  kinds)))
          objects
          ;; We know there will be at least one segment, containing at
          ;; least the header and segment table.
          (list (cons PT_LOAD PF_R)))))

(define (group-by-cars ls)
  (let lp ((in ls) (k #f) (group #f) (out '()))
    (cond
     ((null? in)
      (reverse!
       (if group
           (cons (cons k (reverse! group)) out)
           out)))
     ((and group (equal? k (caar in)))
      (lp (cdr in) k (cons (cdar in) group) out))
     (else
      (lp (cdr in) (caar in) (list (cdar in))
          (if group
              (cons (cons k (reverse! group)) out)
              out))))))

(define (collate-objects-into-segments objects)
  (group-by-cars
   (stable-sort!
    (map (lambda (o)
           (cons (segment-kind (linker-object-section o)) o))
         objects)
    (lambda (x y)
      (let* ((x-kind (car x)) (y-kind (car y))
             (x-type (car x-kind)) (y-type (car y-kind))
             (x-flags (cdr x-kind)) (y-flags (cdr y-kind))
             (x-section (linker-object-section (cdr x)))
             (y-section (linker-object-section (cdr y))))
        (cond
         ((not (equal? x-kind y-kind))
          (cond
           ((and x-type y-type)
            (cond
             ((not (equal? x-flags y-flags))
              (< x-flags y-flags))
             (else
              (< x-type y-type))))
           (else
            (not y-type))))
         ((not (equal? (elf-section-type x-section)
                       (elf-section-type y-section)))
          (cond
           ((equal? (elf-section-type x-section) SHT_NOBITS) #t)
           ((equal? (elf-section-type y-section) SHT_NOBITS) #f)
           (else (< (elf-section-type x-section)
                    (elf-section-type y-section)))))
         (else
          ;; Leave them in the initial order.  This allows us to ensure
          ;; that the ELF header is written first.
          #f)))))))

(define (align address alignment)
  (if (zero? alignment)
      address
      (+ address
         (modulo (- alignment (modulo address alignment)) alignment))))

(define (fold1 proc ls s0)
  (let lp ((ls ls) (s0 s0))
    (if (null? ls)
        s0
        (lp (cdr ls) (proc (car ls) s0)))))

(define (fold3 proc ls s0 s1 s2)
  (let lp ((ls ls) (s0 s0) (s1 s1) (s2 s2))
    (if (null? ls)
        (values s0 s1 s2)
        (receive (s0 s1 s2) (proc (car ls) s0 s1 s2)
          (lp (cdr ls) s0 s1 s2)))))

(define (relocate-section-header sec addr)
  (make-elf-section #:index (elf-section-index sec)
                    #:name (elf-section-name sec)
                    #:type (elf-section-type sec)
                    #:flags (elf-section-flags sec)
                    #:addr addr
                    #:offset addr
                    #:size (elf-section-size sec)
                    #:link (elf-section-link sec)
                    #:info (elf-section-info sec)
                    #:addralign (elf-section-addralign sec)
                    #:entsize (elf-section-entsize sec)))

(define *page-size* 4096)

;; Adds object symbols to global table, relocating them from object
;; address space to memory address space.
(define (add-symbols symbols offset symtab)
  (fold1 (lambda (symbol symtab)
           (let ((name (linker-symbol-name symbol))
                 (addr (linker-symbol-address symbol)))
             (when (vhash-assq name symtab)
               (error "duplicate symbol" name))
             (vhash-consq name (make-linker-symbol name (+ addr offset)) symtab)))
         symbols
         symtab))

(define (alloc-objects write-segment-header!
                       phidx type flags objects addr symtab alignment)
  (let* ((alignment (fold1 (lambda (o alignment)
                             (lcm (elf-section-addralign
                                   (linker-object-section o))
                                  alignment))
                           objects
                           alignment))
         (addr (align addr alignment)))
    (receive (objects endaddr symtab)
        (fold3 (lambda (o out addr symtab)
                 (let* ((section (linker-object-section o))
                        (addr (align addr (elf-section-addralign section))))
                   (values
                    (cons (make-linker-object
                           (relocate-section-header section addr)
                           (linker-object-bv o)
                           (linker-object-relocs o)
                           (linker-object-symbols o))
                          out)
                    (+ addr (elf-section-size section))
                    (add-symbols (linker-object-symbols o) addr symtab))))
               objects
               '() addr symtab)
      (when type
        (write-segment-header!
         (make-elf-segment #:index phidx #:type type
                           #:offset addr #:vaddr addr
                           #:filesz (- endaddr addr) #:memsz (- endaddr addr)
                           #:flags flags #:align alignment)))
      (values endaddr
              (reverse objects)
              symtab))))

(define (process-reloc reloc bv file-offset mem-offset symtab endianness)
  (let ((ent (vhash-assq (linker-reloc-symbol reloc) symtab)))
    (unless ent
      (error "Undefined symbol" (linker-reloc-symbol reloc)))
    (let* ((file-loc (+ (linker-reloc-loc reloc) file-offset))
           (mem-loc (+ (linker-reloc-loc reloc) mem-offset))
           (addr (linker-symbol-address (cdr ent))))
      (case (linker-reloc-type reloc)
        ((rel32/4)
         (let ((diff (- addr mem-loc)))
           (unless (zero? (modulo diff 4))
             (error "Bad offset" reloc symbol mem-offset))
           (bytevector-s32-set! bv file-loc
                                (+ (/ diff 4) (linker-reloc-addend reloc))
                                endianness)))
        ((abs32/1)
         (bytevector-u32-set! bv file-loc addr endianness))
        ((abs64/1)
         (bytevector-u64-set! bv file-loc addr endianness))
        (else
         (error "bad reloc type" reloc))))))

(define (write-linker-object bv o symtab endianness)
  (let* ((section (linker-object-section o))
         (offset (elf-section-offset section))
         (addr (elf-section-addr section))
         (len (elf-section-size section))
         (bytes (linker-object-bv o))
         (relocs (linker-object-relocs o)))
    (if (not (= (elf-section-type section) SHT_NOBITS))
        (begin
          (if (not (= len (bytevector-length bytes)))
              (error "unexpected length" section bytes))
          (bytevector-copy! bytes 0 bv offset len)
          (for-each (lambda (reloc)
                      (process-reloc reloc bv offset addr symtab endianness))
                    relocs)))))

(define (find-shstrndx objects)
  (or-map (lambda (object)
            (let* ((section (linker-object-section object))
                   (bv (linker-object-bv object))
                   (name (elf-section-name section)))
              (and (= (elf-section-type section) SHT_STRTAB)
                   (equal? (false-if-exception (string-table-ref bv name))
                           ".shstrtab")
                   (elf-section-index section))))
          objects))

(define (add-elf-objects objects endianness word-size)
  (define phoff (elf-header-len word-size))
  (define phentsize (elf-program-header-len word-size))
  (define shentsize (elf-section-header-len word-size))
  (define shnum (+ (length objects) 3))
  (define reloc-kind
    (case word-size
      ((4) 'abs32/1)
      ((8) 'abs64/1)
      (else (error "bad word size" word-size))))

  ;; ELF requires that the first entry in the section table be of type
  ;; SHT_NULL.
  ;;
  (define (make-null-section)
    (make-linker-object (make-elf-section #:index 0 #:type SHT_NULL
                                          #:flags 0 #:addralign 0)
                        #vu8() '() '()))

  ;; The ELF header and the segment table.
  ;;
  (define (make-header phnum index shoff-label)
    (let* ((header (make-elf #:byte-order endianness #:word-size word-size
                             #:phoff phoff #:phnum phnum #:phentsize phentsize
                             #:shoff 0 #:shnum shnum #:shentsize phentsize
                             #:shstrndx (or (find-shstrndx objects) SHN_UNDEF)))
           (shoff-reloc (make-linker-reloc reloc-kind
                                           (elf-header-shoff-offset word-size)
                                           0
                                           shoff-label))
           (size (+ phoff (* phnum phentsize)))
           (bv (make-bytevector size 0)))
      (write-elf-header bv header)
      ;; Leave the segment table uninitialized; it will be filled in
      ;; later by calls to the write-segment-header! closure.
      (make-linker-object (make-elf-section #:index index #:type SHT_PROGBITS
                                            #:flags SHF_ALLOC #:size size)
                          bv
                          (list shoff-reloc)
                          '())))

  ;; The section table.
  ;;
  (define (make-footer objects shoff-label)
    (let* ((size (* shentsize shnum))
           (bv (make-bytevector size 0))
           (section-table (make-elf-section #:index (length objects)
                                            #:type SHT_PROGBITS
                                            #:flags 0
                                            #:size size)))
      (define (write-and-reloc section-label section relocs)
        (let ((offset (* shentsize (elf-section-index section))))
          (write-elf-section-header bv offset endianness word-size section)
          (if (= (elf-section-type section) SHT_NULL)
              relocs
              (cons* (make-linker-reloc
                      reloc-kind
                      (+ offset (elf-section-header-addr-offset word-size))
                      0
                      section-label)
                     (make-linker-reloc
                      reloc-kind
                      (+ offset (elf-section-header-offset-offset word-size))
                      0
                      section-label)
                     relocs))))
      (let ((relocs (fold1 (lambda (object relocs)
                             (write-and-reloc
                              (linker-symbol-name
                               (linker-object-section-symbol object))
                              (linker-object-section object)
                              relocs))
                           objects
                           (write-and-reloc shoff-label section-table '()))))
        (%make-linker-object section-table bv relocs
                             (list (make-linker-symbol shoff-label 0))))))

  (let* ((null-section (make-null-section))
         (objects (cons null-section objects))

         (shoff (gensym "*section-table*"))
         (header (make-header (count-segments objects) (length objects) shoff))
         (objects (cons header objects))

         (footer (make-footer objects shoff))
         (objects (cons footer objects)))

    ;; The header includes the segment table, which needs offsets and
    ;; sizes of the segments.  Normally we would use relocs to rewrite
    ;; these values, but there is no reloc type that would allow us to
    ;; compute size.  Such a reloc would need to take the difference
    ;; between two symbols, and it's probably a bad idea architecturally
    ;; to create one.
    ;;
    ;; So instead we return a closure to patch up the segment table.
    ;; Normally we'd shy away from such destructive interfaces, but it's
    ;; OK as we create the header section ourselves.
    ;;
    (define (write-segment-header! segment)
      (let ((bv (linker-object-bv header))
            (offset (+ phoff (* (elf-segment-index segment) phentsize))))
        (write-elf-program-header bv offset endianness word-size segment)))

    (values write-segment-header! objects)))

;; objects ::= list of <linker-object>
;;
;; => 3 values:
;;   file size
;;   objects with allocated memory address and file offset
;;   symbol table
;;
(define (allocate-elf objects page-aligned? endianness word-size)
  (receive (write-segment-header! objects)
      (add-elf-objects objects endianness word-size)
    (let lp ((seglists (collate-objects-into-segments objects))
             (objects '())
             (phidx 0)
             (addr 0)
             (symtab vlist-null)
             (prev-flags 0))
      (match seglists
        ((((type . flags) objs-in ...) seglists ...)
         (receive (addr objs-out symtab)
             (alloc-objects write-segment-header!
                            phidx type flags objs-in addr symtab
                            (if (and page-aligned?
                                     (not (= flags prev-flags))
                                     ;; Allow sections that are not in
                                     ;; loadable segments to share pages
                                     ;; with PF_R segments.
                                     (not (and (not type) (= PF_R prev-flags))))
                                *page-size*
                                8))
           (lp seglists
               (fold1 cons objs-out objects)
               (if type (1+ phidx) phidx)
               addr
               symtab
               flags)))
        (()
         (values addr
                 (reverse objects)
                 symtab))))))

;; Given a list of linker objects, collate the objects into segments,
;; allocate the segments, allocate the ELF bytevector, and write the
;; segments into the bytevector, relocating as we go.
;;
(define* (link-elf objects #:key
                   (page-aligned? #t)
                   (endianness (target-endianness))
                   (word-size (target-word-size)))
  (receive (size objects symtab)
      (allocate-elf objects page-aligned? endianness word-size)
    (let ((bv (make-bytevector size 0)))
      (for-each
       (lambda (object)
         (write-linker-object bv object symtab endianness))
       objects)
      bv)))
