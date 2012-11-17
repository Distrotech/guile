(define-module (language cps primitives)
  #:export (*primitive-insn-table*
            *primitive-arity-table*))

;; right now the primitives tables only hold one primitive. this is just
;; a stub so I can test the compiler on it.

(define (fill-table-from-alist! table alist)
  (for-each
   (lambda (entry) (hashq-set! table
                          (car entry)
                          (cdr entry)))
   alist))

(define *primitive-insn-list*
  '((+ . add)))

(define *primitive-arity-list*
  '((+ . 2)))

(define *primitive-insn-table* (make-hash-table))
(define *primitive-arity-table* (make-hash-table))

(fill-table-from-alist! *primitive-insn-table*
                        *primitive-insn-list*)

(fill-table-from-alist! *primitive-arity-table*
                        *primitive-arity-list*)
