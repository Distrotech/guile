(define-module (language cps primitives)
  #:export (*primitive-insn-table*
            *primitive-in-arity-table*
            *primitive-out-arity-table*
            *primitive-props-table*))

(define *primitive-insn-data*
  ;; fields:
  ;; (Scheme name, VM name, in arity, out arity, props ...)

  ;; "Scheme name" is what will appear in CPS <primitive> records, and
  ;; also the corresponding procedure's name in the (guile) module if it
  ;; has one. "out arity" must be 0 or 1. "in arity" is the minimum in
  ;; arity. if the primitive accepts more than that, it should have the
  ;; "variable" property.
  '((string-length string-length 1 1)
    (string-ref string-ref 2 1)
    (string->number string->number 1 1)
    (string->symbol string->symbol 1 1)
    (symbol->keyword symbol->keyword 1 1)
    (cons cons 2 1)
    (car car 1 1)
    (cdr cdr 1 1)
    (+ add 2 1)
    (1+ add1 1 1)
    (- sub 2 1)
    (1- sub1 1 1)
    (* mul 2 1)
    (/ div 2 1)
    ;; quo isn't here because I don't know which of our many types of
    ;; division it's supposed to be. same for rem and mod.
    (ash ash 2 1)
    (logand logand 2 1)
    (logior logior 2 1)
    (logxor logxor 2 1)
    (vector-length vector-length 1 1)
    (vector-ref vector-ref 2 1)
    (struct-vtable struct-vtable 1 1)
    (struct-ref struct-ref 2 1)
    (class-of class-of 1 1)
    (fix-closure fix-closure 1 0 variable)))

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

;; and this one holds the number of outputs.
(define *primitive-out-arity-table* (make-hash-table))

;; this is for miscellaneous properties
(define *primitive-props-table* (make-hash-table))

(define (fill-insn-tables!)
  (for-each
   (lambda (entry)
     (hashq-set! *primitive-insn-table*
                 (car entry) (cadr entry))
     (hashq-set! *primitive-in-arity-table*
                 (car entry) (caddr entry))
     (hashq-set! *primitive-out-arity-table*
                 (car entry) (cadddr entry))
     (hashq-set! *primitive-props-table*
                 (car entry) (cddddr entry)))
   *primitive-insn-data*))

(fill-insn-tables!)
