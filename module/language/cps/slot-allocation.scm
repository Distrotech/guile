;;; Continuation-passing style (CPS) intermediate language (IL)

;; Copyright (C) 2013 Free Software Foundation, Inc.

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
;;;
;;; Code:

(define-module (language cps slot-allocation)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-9)
  #:use-module (srfi srfi-26)
  #:use-module (language cps)
  #:use-module (language cps dfg)
  #:export (allocate-slots
            lookup-allocation
            lookup-slot
            lookup-constant-value
            lookup-maybe-constant-value
            lookup-call-proc-slot
            lookup-parallel-moves
            $allocation))

;; Continuations can bind variables.  The $allocation structure
;; represents the slot in which a variable is stored.
;;
;; Not all variables have slots allocated.  Variables that are constant
;; and that are only used by primcalls that can accept constants
;; directly are not allocated to slots, and their SLOT value is false.
;; Likewise constants that are only used by calls are not allocated into
;; slots, to avoid needless copying.  If a variable is constant, its
;; constant value is set to the CONST slot and HAS-CONST? is set to a
;; true value.
;;
;; DEF holds the label of the continuation that defines the variable,
;; and DEAD is a list of continuations at which the variable becomes
;; dead.
(define-record-type $allocation
  (make-allocation def slot dead has-const? const)
  allocation?
  (def allocation-def)
  (slot allocation-slot)
  (dead allocation-dead set-allocation-dead!)
  (has-const? allocation-has-const?)
  (const allocation-const))

;; Currently calls are allocated in the caller frame, above all locals
;; that are live at the time of the call.  Therefore there is no
;; parallel move problem.  We could be more clever here.
(define-record-type $call-allocation
  (make-call-allocation proc-slot)
  call-allocation?
  (proc-slot call-allocation-proc-slot))

;; Tail calls, multiple-value returns, and jumps to continuations with
;; multiple arguments are forms of parallel assignment.  A
;; $parallel-move represents a specific solution to the parallel
;; assignment problem, with an ordered list of (SRC . DST) moves.  This
;; may involve a temporary variable.
(define-record-type $parallel-move
  (make-parallel-move order)
  parallel-move?
  ;; ((src . dst) ...)
  (order parallel-move-order))

(define (find-first-zero n)
  ;; Naive implementation.
  (let lp ((slot 0))
    (if (logbit? slot n)
        (lp (1+ slot))
        slot)))

(define (find-first-trailing-zero n count)
  (let lp ((slot count))
    (if (or (zero? slot) (logbit? (1- slot) n))
        slot
        (lp (1- slot)))))

(define (lookup-allocation sym allocation)
  (let ((res (hashq-ref allocation sym)))
    (unless res
      (error "Variable not defined" sym))
    res))

(define (lookup-slot sym allocation)
  (match (lookup-allocation sym allocation)
    (($ $allocation def slot dead has-const? const) slot)))

(define (lookup-constant-value sym allocation)
  (match (lookup-allocation sym allocation)
    (($ $allocation def slot dead #t const) const)
    (else
     (error "Variable does not have constant value" sym))))

(define (lookup-maybe-constant-value sym allocation)
  (match (lookup-allocation sym allocation)
    (($ $allocation def slot dead has-const? const)
     (values has-const? const))))

(define (lookup-call-proc-slot sym allocation)
  (match (lookup-allocation sym allocation)
    (($ $call-allocation proc-slot) proc-slot)
    (else
     (error "Continuation not a call" sym))))

(define (lookup-parallel-moves sym moves-table)
  (match (hashq-ref moves-table sym)
    (($ $parallel-move moves) moves)
    (else
     (error "Continuation has no parallel moves" sym))))

(define (solve-parallel-move src dst tmp)
  "Solve the parallel move problem between src and dst slot lists, which
are comparable with eqv?.  A tmp slot may be used."

  ;; This algorithm is taken from: "Tilting at windmills with Coq:
  ;; formal verification of a compilation algorithm for parallel moves"
  ;; by Laurence Rideau, Bernard Paul Serpette, and Xavier Leroy
  ;; <http://gallium.inria.fr/~xleroy/publi/parallel-move.pdf>

  (define (split-move moves reg)
    (let loop ((revhead '()) (tail moves))
      (match tail
        (((and s+d (s . d)) . rest)
         (if (eqv? s reg)
             (cons d (append-reverse revhead rest))
             (loop (cons s+d revhead) rest)))
        (_ #f))))

  (define (replace-last-source reg moves)
    (match moves
      ((moves ... (s . d))
       (append moves (list (cons reg d))))))

  (let loop ((to-move (map cons src dst))
             (being-moved '())
             (moved '())
             (last-source #f))
    ;; 'last-source' should always be equivalent to:
    ;; (and (pair? being-moved) (car (last being-moved)))
    (match being-moved
      (() (match to-move
            (() (reverse moved))
            (((and s+d (s . d)) . t1)
             (if (or (eqv? s d) ; idempotent
                     (not s))   ; src is a constant and can be loaded directly
                 (loop t1 '() moved #f)
                 (loop t1 (list s+d) moved s)))))
      (((and s+d (s . d)) . b)
       (match (split-move to-move d)
         ((r . t1) (loop t1 (acons d r being-moved) moved last-source))
         (#f (match b
               (() (loop to-move '() (cons s+d moved) #f))
               (_ (if (eqv? d last-source)
                      (loop to-move
                            (replace-last-source tmp b)
                            (cons s+d (acons d tmp moved))
                            tmp)
                      (loop to-move b (cons s+d moved) last-source))))))))))

;; allocation := $allocation | $call-allocation | $parallel-move
;; sym, term -> (hash-table of sym -> allocation)
(define (allocate-slots self exp)
  (define (empty-live-set)
    (cons #b0 '()))

  (define (add-live-variable sym slot live-set)
    (cons (logior (car live-set) (ash 1 slot))
          (acons sym slot (cdr live-set))))

  (define (remove-live-variable sym slot live-set)
    (cons (logand (car live-set) (lognot (ash 1 slot)))
          (acons sym #f (cdr live-set))))

  (define (fold-live-set proc seed live-set)
    (let lp ((bits (car live-set)) (entries (cdr live-set)) (seed seed))
      (if (zero? bits)
          seed
          (match entries
            (((sym . slot) . entries)
             (if (and slot (logbit? slot bits))
                 (lp (logand bits (lognot (ash 1 slot)))
                     entries
                     (proc sym slot seed))
                 (lp bits entries seed)))))))

  (define (compute-slot live-set hint)
    (if (and hint (not (logbit? hint (car live-set))))
        hint
        (find-first-zero (car live-set))))

  (define (compute-call-proc-slot live-set nlocals)
    (+ 3 (find-first-trailing-zero (car live-set) nlocals)))

  (let ((dfg (compute-local-dfg self exp))
        (nlocals 0)
        (nargs (match exp
                 (($ $cont _ _ 
                     ($ $kentry _ _ ($ $cont _ _ ($ $kargs names syms))))
                  (length syms))))
        (visited (make-hash-table))
        (allocation (make-hash-table))
        (moves-table (make-hash-table)))
    (define (allocate! sym k hint live-set)
      (match (hashq-ref allocation sym)
        (($ $allocation def slot dead has-const)
         ;; Parallel move already allocated this one.
         (if slot
             (add-live-variable sym slot live-set)
             live-set))
        (_
         (call-with-values (lambda () (find-constant-value sym dfg))
           (lambda (has-const? const)
             (cond
              ((and has-const? (not (constant-needs-allocation? sym const dfg)))
               (hashq-set! allocation sym
                           (make-allocation k #f '() has-const? const))
               live-set)
              (else
               (let ((slot (compute-slot live-set hint)))
                 (when (>= slot nlocals)
                   (set! nlocals (+ slot 1)))
                 (hashq-set! allocation sym
                             (make-allocation k slot '() has-const? const))
                 (add-live-variable sym slot live-set)))))))))

    (define (dead sym k live-set)
      (match (lookup-allocation sym allocation)
        ((and allocation ($ $allocation def slot dead has-const? const))
         (set-allocation-dead! allocation (cons k dead))
         (remove-live-variable sym slot live-set))))

    (define (allocate-frame! k nargs live-set)
      (let ((proc-slot (compute-call-proc-slot live-set nlocals)))
        (set! nlocals (max nlocals (+ proc-slot 1 nargs)))
        (hashq-set! allocation k (make-call-allocation proc-slot))
        live-set))

    (define (parallel-move! src-k src-slots pre-live-set post-live-set dst-slots)
      (let* ((tmp-slot (find-first-zero (logior (car pre-live-set)
                                                (car post-live-set))))
             (moves (solve-parallel-move src-slots dst-slots tmp-slot)))
        (when (and (>= tmp-slot nlocals) (assv tmp-slot moves))
          (set! nlocals (+ tmp-slot 1)))
        (hashq-set! moves-table src-k (make-parallel-move moves))
        post-live-set))

    (let visit ((exp exp)
                (exp-k #f)
                (live-set (empty-live-set)))

      (define (use sym live-set)
        (if (and (lookup-slot sym allocation) (dead-after-use? sym exp-k dfg))
            (dead sym exp-k live-set)
            live-set))

      (define (maybe-kill-definition sym live-set)
        (if (and (lookup-slot sym allocation) (dead-after-def? sym dfg))
            (dead sym exp-k live-set)
            live-set))

      (define (kill-conditionally-dead live-set)
        (if (branch? exp-k dfg)
            (let ((branches (find-other-branches exp-k dfg)))
              (fold-live-set
               (lambda (sym slot live-set)
                 (if (and (> slot nargs)
                          (dead-after-branch? sym exp-k branches dfg))
                     (dead sym exp-k live-set)
                     live-set))
               live-set
               live-set))
            live-set))

      (match exp
        (($ $letk conts body)
         (let ((live-set (visit body exp-k live-set)))
           (for-each (cut visit <> exp-k live-set) conts))
         live-set)

        (($ $cont k src cont)
         (hashq-set! visited k #t)
         (visit cont k live-set))

        (($ $kentry arity tail body)
         (visit body exp-k (allocate! self exp-k 0 live-set)))

        (($ $kargs names syms body)
         (visit body exp-k
                (kill-conditionally-dead
                 (fold maybe-kill-definition
                       (fold (cut allocate! <> exp-k #f <>) live-set syms)
                       syms))))

        (($ $continue k ($ $var sym))
         (use sym live-set))

        (($ $continue k ($ $call proc args))
         (match (lookup-cont k (dfg-cont-table dfg))
           (($ $ktail)
            (let ((tail-nlocals (1+ (length args))))
              (set! nlocals (max nlocals tail-nlocals))
              (parallel-move! exp-k
                              (map (cut lookup-slot <> allocation)
                                   (cons proc args))
                              live-set (fold use live-set (cons proc args))
                              (iota tail-nlocals))))
           (($ $ktrunc arity kargs)
            (let* ((live-set
                    (fold use
                          (use proc
                               (allocate-frame! exp-k (length args) live-set))
                          args))
                   (proc-slot (lookup-call-proc-slot exp-k allocation))
                   (dst-syms (lookup-bound-syms kargs dfg))
                   (nvals (length dst-syms))
                   (src-slots (map (cut + proc-slot 1 <>) (iota nvals)))
                   (live-set* (fold (cut allocate! <> kargs <> <>)
                                    live-set dst-syms src-slots))
                   (dst-slots (map (cut lookup-slot <> allocation)
                                   dst-syms)))
              (parallel-move! exp-k src-slots live-set live-set* dst-slots)))
           (else
            (fold use
                  (use proc (allocate-frame! exp-k (length args) live-set))
                  args))))

        (($ $continue k ($ $primcall name args))
         (fold use live-set args))

        (($ $continue k ($ $values args))
         (let ((live-set* (fold use live-set args)))
           (define (compute-dst-slots)
             (match (lookup-cont k (dfg-cont-table dfg))
               (($ $ktail)
                (let ((tail-nlocals (1+ (length args))))
                  (set! nlocals (max nlocals tail-nlocals))
                  (cdr (iota tail-nlocals))))
               (_
                (let* ((src-slots (map (cut lookup-slot <> allocation) args))
                       (dst-syms (lookup-bound-syms k dfg))
                       (dst-live-set (fold (cut allocate! <> k <> <>)
                                           live-set* dst-syms src-slots)))
                  (map (cut lookup-slot <> allocation) dst-syms)))))

           (parallel-move! exp-k
                           (map (cut lookup-slot <> allocation) args)
                           live-set live-set*
                           (compute-dst-slots))))

        (($ $continue k ($ $prompt escape? tag handler))
         (use tag live-set))

        (_ live-set)))

    (values moves-table allocation nlocals)))
