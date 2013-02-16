(define-module (language cps primitives)
  #:export (*primitive-insn-table*
            *primitive-in-arity-table*
            *primitive-out-arity-table*))

;; the "primitives" in this file are the operations which are supported
;; by VM opcodes. Each primitive has more than one name - there is its
;; name in the (guile) module, its name in a <primitive> record (which
;; is always the same as its name in (guile), for simplicity) and its
;; name as a VM instruction, which may be different from the first two.

;; this list holds information about the primitive VM operations. The
;; current fields are (Scheme name, VM name, in-arity). We don't handle
;; folds, reductions, or variable-arity instructions yet.
(define *primitive-insn-data*
  '((string-length string-length 1)
    (string-ref string-ref 2)
    (string->number string->number 1)
    (string->symbol string->symbol 1)
    (symbol->keyword symbol->keyword 1)
    (cons cons 2)
    (car car 1)
    (cdr cdr 1)
    (+ add 2)
    (1+ add1 1)
    (- sub 2)
    (1- sub1 1)
    (* mul 2)
    (/ div 2)
    ;; quo isn't here because I don't know which of our many types of
    ;; division it's supposed to be. same for rem and mod.
    (ash ash 2)
    (logand logand 2)
    (logior logior 2)
    (logxor logxor 2)
    (vector-length vector-length 1)
    (vector-ref vector-ref 2)
    (struct-vtable struct-vtable 1)
    (struct-ref struct-ref 2)
    (class-of class-of 1)))

;; this table maps our names for primitives (which are the Scheme names)
;; to the corresponding VM instructions. It also does double duty as the
;; list of Scheme names that can be turned into primitive instructions -
;; if a procedure is in (guile) and is a key in this hash table, then it
;; must represent a primitive operation.

(define *primitive-insn-table* (make-hash-table))

;; We assume that each instruction takes its destination first and the
;; remaining arguments in order. We don't handle folds or reductions
;; right now.

;; this table holds the number of inputs each primitive function takes
(define *primitive-in-arity-table* (make-hash-table))

;; and this one holds the number of outputs. this will always be 1 right
;; now, but there are cases where that won't be true - for instance,
;; divmod.
(define *primitive-out-arity-table* (make-hash-table))

(define (fill-insn-tables!)
  (for-each
   (lambda (entry)
     (hashq-set! *primitive-insn-table*
                 (car entry) (cadr entry))
     (hashq-set! *primitive-in-arity-table*
                 (car entry) (caddr entry))
     (hashq-set! *primitive-out-arity-table*
                 (car entry) 1))
   *primitive-insn-data*))

(fill-insn-tables!)
