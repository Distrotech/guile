(define-module (language cps closure-conversion)
  #:use-module (language cps)
  #:use-module (system base syntax)
  #:export (closure-convert))

;; This module does closure conversion on CPS, returning new CPS with no
;; closures. I'm not particularly happy about it, because I don't think
;; it's clear that closure conversion should happen here. Other options
;; are a) doing closure conversion in the Tree-IL->CPS conversion and b)
;; not doing closure conversion as an explicit step, and just generating
;; code that accesses closures.

;; The reason to make it explicit is that then common subexpression
;; elimination will also be able to pull out references to the same
;; variable, and hopefully let us access the closure vector less.

;; On the other hand, we could do some sort of intermediate thing with a
;; new letval type that represents a closure variable. Or alternatively,
;; a letval type representing the whole closure array? That seems
;; unnecessary.

;; what if we just don't do closure conversion? then referencing closure
;; variables becomes

;; (free-ref x loc)

(define (closure-convert cps free-vals)
  ;; given a list of free variables, allocate closure slots to
  ;; them. return an alist mapping variables to closure slots.
  (define (alloc-closure-vals vals)
    (map cons vals
         (iota (length vals))))

  (define (with-closure-ref gen-k val env)
    ;; call gen-k with a name that can be used to access val in a
    ;; closure context.
    (let ((num (assq-ref env val)))
      (if num
          (let ((num-n (gensym "idx-"))
                (con (gensym "con-"))
                (name (gensym "val-")))
            (make-letval
             (list num-n)
             (list (make-const num))
             (make-letcont
              (list con)
              (list (make-lambda
                     (list name)
                     #f
                     (gen-k name)))
              (make-call
               (make-primitive 'closure-ref)
               con
               (list num-n)))))
          ;; if we didn't find a number, then this is a local variable,
          ;; not a closure variable, so we just access it normally.
          (gen-k val))))

  ;; like with-closure-ref, but vals is a list of value names
  (define (with-closure-refs gen-k vals env)
    (let iter ((names '())
               (vals vals))
      (if (null? vals)
          (apply gen-k (reverse names))
          (with-closure-ref
           (lambda (name)
             (iter (cons name names) (cdr vals)))
           (car vals)
           env))))

  ;; closure-env maps variables to their closure locations. if a
  ;; variable isn't in the environment, it's not a closure variable.
  (define (visit cps env)
    (record-case cps
      ((<letval> names vals body)
       (let iter ((old-vals vals)
                  (new-vals '()))
         (cond
          ((null? old-vals)
           (make-letval
            names
            (reverse new-vals)
            (visit body env)))
          ((not (var? (car old-vals)))
           (iter (cdr old-vals)
                 (cons (car old-vals) new-vals)))
          (else
           (with-closure-ref
            (lambda (name)
              (iter (cdr old-vals)
                    (cons (make-var name) new-vals)))
            (var-value (car old-vals))
            env)))))

      ((<letrec> names funcs body)
       ;; with a letrec, we need to run the primitive make-closure (and
       ;; maybe later fix-closure too) to generate the procedures, and
       ;; then run the body of the letrec in an environment with the
       ;; procedures available. so we actually don't use the letrec
       ;; machinery - we replace the letrec names with dummies and turn
       ;; the letrec names into arguments of make-closure's
       ;; continuation. this is really ugly.
       (let* ((func (car funcs))
              (closure-env (alloc-closure-vals
                            (free-vals func)))
              (new-names (map (lambda (n) (gensym "dummy-")) names)))
         (make-letrec
          new-names
          (list (visit func closure-env))
          (let ((con (gensym "con-")))
            ;; first make the closure, then run the body of the letrec.
            ;; Note: we only allow a single closure in the letrec right
            ;; now.
            (make-letcont
             (list con)
             (list (make-lambda
                    names #f (visit body env)))
             (make-call
              (make-primitive 'make-closure)
              con
              ;; the first argument of a make-closure call is special.
              (cons (car new-names)
                    (free-vals func))))))))

      ((<letcont> names conts body)
       (make-letcont
        names
        (map (lambda (con) (visit con env)) conts)
        (visit body env)))

      ((<lambda> names rest body)
       (make-lambda
        names
        rest
        (visit body env)))

      ((<call> proc cont args)
       ;; letting proc be a primitive may be a mistake
       (if (primitive? proc)
           (with-closure-refs
            (lambda (cont . args)
              (make-call proc cont args))
            (cons cont args)
            env)
           (with-closure-refs
            (lambda (proc cont . args)
              (make-call proc cont args))
            (cons* proc cont args)
            env)))

      ((<if> test consequent alternate)
       (with-closure-refs
        make-if
        (list test consequent alternate)
        env))))

  (visit cps '()))
