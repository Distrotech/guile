(define-module (language cps util)
  #:use-module (ice-9 q)
  #:use-module (srfi srfi-1)
  #:export (append-qs! int-range maybe-append generate-shuffle))

;; The functions in this file are not directly related to CPS or
;; compilation; they're here because the CPS compiler needs them and
;; they haven't found a better place in the module structure yet.

;; this function should probably be in (ice-9 q)
(define (append-qs! q r)
  (set-cdr! (cdr q) (car r))
  (set-cdr! q (cdr r))
  q)

;; and this is some sort of general utility
(define (int-range start end)
  (if (< start end)
      (cons start (int-range (+ start 1) end))
      '()))

;; this is a totally generic utility
(define (maybe-append . args)
  (cond ((null? args) '())
        ((eq? (car args) #f)
         (apply maybe-append (cdr args)))
        (else
         (append (car args)
                 (apply maybe-append (cdr args))))))

;; this function returns a list of `mov' instructions that accomplish a
;; shuffle in the stack. each tail argument is a pair (from . to) that
;; indicates how a value should move. the first argument is the number
;; of an extra slot that it can use as swap space if it wants to.  NOTE:
;; if the VM had a `swap' instruction, we wouldn't need an extra
;; spot. maybe we should add one.
(define (generate-shuffle swap . args)
  ;; a "move chain" is ((x1 . x2) (x2 . x3) ...). we return a list of
  ;; the swap chains we find in our args, as (ice-9 q) queues.
  (define (make-move-chains chains rest)
    ;; chains is a list of queues of elements, each of which is a move
    ;; chain, and rest is a list of whatever moves have yet to be
    ;; chained.
    (if (null? rest)
        chains
        (let* ((next (car rest))
               (front-match (find (lambda (x) (eq? (car (q-front x)) (cdr next)))
                                  chains))
               (end-match (find (lambda (x) (eq? (cdr (q-rear x)) (car next)))
                                chains)))
          ;; it is possible to get a front-match and an end-match at the
          ;; same time in two different ways. if our set of moves
          ;; includes a cycle, then we expect that at some point, the
          ;; front-match and end-match will be eq?. we need to serialize
          ;; our cycles anyway, so we just pick the front-match
          ;; arbitrarily. however, if we have a front-match and an
          ;; end-match that are not eq?, then it means we have found a
          ;; link between two of our chains, and we need to stitch them
          ;; together.
          (cond
           ((and front-match end-match (not (eq? front-match end-match)))
            ;; stitch two chains together
            (enq! end-match next)
            (append-qs! end-match front-match)
            (make-move-chains (delq front-match chains) (cdr rest)))
           (front-match ;; push next onto the beginning of a chain
            (q-push! front-match next)
            (make-move-chains chains (cdr rest)))
           (end-match ;; push next onto the end of a chain
            (enq! end-match next)
            (make-move-chains chains (cdr rest)))
           (else ;; make a new chain
            (let ((new-chain (make-q)))
              (enq! new-chain next)
              (make-move-chains (cons new-chain chains) (cdr rest))))))))

  ;; given a single move chain, generate a series of moves to implement
  ;; it, using the given swap register
  (define (moves-for-chain swap chain)
    (if (eq? (car (q-front chain))
             (cdr (q-rear chain)))
        ;; a cyclic chain!
        `((mov ,swap ,(car (q-front chain)))
          ;; we remove the first element of the chain, making it acyclic
          ,@(moves-for-acyclic-list (cdar chain))
          (mov ,(cdr (q-front chain)) ,swap))
        (moves-for-acyclic-list (car chain))))

  (define (moves-for-acyclic-list lst)
    ;; this is named -list instead of -chain because it accepts a list
    ;; holding a move chain, instead of a queue like the other -chain
    ;; functions.
    (let iter ((moves (reverse lst)))
      (if (null? moves)
          '()
          (cons `(mov ,(cdar moves) ,(caar moves))
                (iter (cdr moves))))))

  ;; step one: eliminate identity shuffles
  (let* ((no-ids (remove (lambda (x) (eq? (car x) (cdr x))) args))
         ;; step two: make move chains
         (chains (make-move-chains '() no-ids))) 
    ;; step three: generate a series of moves for each chain, using the
    ;; swap space.
    (apply append (map (lambda (x) (moves-for-chain swap x)) chains))))
