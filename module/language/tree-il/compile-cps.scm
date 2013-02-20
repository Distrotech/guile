(define-module (language tree-il compile-cps)
  #:use-module (language tree-il)
  #:use-module ((language cps)
                #:renamer (symbol-prefix-proc 'cps-))
  #:use-module (ice-9 match)
  #:use-module (ice-9 vlist)
  #:use-module (srfi srfi-1)
  #:export (tree-il->cps))

;; this should probably be a general utility. it simply executes a
;; function n times and returns a list of the results
(define (sample f n)
  (if (< n 1)
      '()
      (cons (f)
            (sample f (- n 1)))))

;; k is the continuation
(define (tree-il->cps tree)
  ;; with-value-name first generates some CPS that finds the value of
  ;; tree, and then calls 'gen-k' to generate more CPS code - but
  ;; 'gen-k' is called with a name which can reference the value of
  ;; tree. the real point is to abstract out the idea of *not*
  ;; generating extra continuations for constants. we could always
  ;; optimize them out later, but it seems easier to just not make them
  ;; in the first place.
  (define (with-value-name gen-k tree env)
    (cond ((const? tree)
           (let ((val-name (gensym "val-")))
             (cps-make-letval
              (list val-name)
              (list (cps-make-const (const-exp tree)))
              (gen-k val-name))))
          (else
           (let ((con (gensym "con-"))
                 (val (gensym "val-")))
             (cps-make-letcont
              (list con)
              (list (cps-make-lambda (list val) #f (gen-k val)))
              (visit con tree env))))))

  ;; like with-value-names, but takes a list of trees, and applies gen-k
  ;; to the corresponding list of values. the generated code evaluates
  ;; the list of values in the same order as they appear in the list.
  (define (with-value-names gen-k trees env)
    (let iter ((trees trees)
               (names '())) ;; names are accumulated in reverse order
      (if (null? trees)
          (apply gen-k (reverse names))
          (with-value-name
           (lambda (name) (iter (cdr trees) (cons name names)))
           (car trees)
           env))))

  ;; the next two are variants on with-value-name and with-value-names
  ;; in which I know what names I want the values to have, and I just
  ;; need to wrap them in the appropriate CPS construct. in that case,
  ;; we don't even need to pass a continuation closure - we just
  ;; pass in the code to run next.
  (define (with-value-named next tree name env)
    (cond ((const? tree)
           (cps-make-letval
            (list name)
            (list (cps-make-const (const-exp tree)))
            next))
          (else
           (let ((con (gensym "con-")))
             (cps-make-letcont
              (list con)
              (list (cps-make-lambda (list name) #f next))
              (visit con tree env))))))

  (define (with-values-named next trees names env)
    (if (null? trees)
        next
        (with-value-named
         (with-values-named next (cdr trees) (cdr names) env)
         (car trees) (car names) env)))

  ;; with-variable-boxes generates CPS that makes variable objects for
  ;; the given CPS values and then calls 'gen-k' with a new environment
  ;; in which the given names are mapped to the names of their boxes. TO
  ;; DO: let the names that will be in the environment be different than
  ;; the current CPS names of the values?
  (define (with-variable-boxes gen-k vals env)
    (if (null? vals)
        (gen-k env)
        (let ((var-names (sample (lambda () (gensym "var-"))
                                 (length vals))))
          (cps-make-letval
           var-names
           (map (lambda (var-name val)
                  (cps-make-var val))
                var-names vals)
           (gen-k
            (fold vhash-consq
                  env
                  vals var-names))))))
  
  ;; visit returns a CPS version of tree which ends by calling
  ;; continuation k. 'env' is a vhash that maps Tree-IL variable gensyms
  ;; to CPS value names.
  (define (visit k tree env)
    (match tree
      ;; note: 1. we only support lambdas with one case right now, and
      ;; totally ignore optional, rest and keyword arguments. 2. we only
      ;; support lambda forms as the outermost part of the Tree-IL.
      (($ <lambda> src meta
          ($ <lambda-case> src req opt rest kw inits gensyms body alternate))
       (cps-make-lambda gensyms
                   #f
                   (with-variable-boxes
                    (lambda (env)
                      (visit 'return body env))
                    gensyms
                    env)))
      (($ <call> src proc args)
       (with-value-names
        (lambda (proc . args)
          (cps-make-call proc k args))
        (cons proc args)
        env))
      (($ <conditional> src test consequent alternate)
       ;; the control flow for an if looks like this:
       ;;  test --> if ---> then ---> con
       ;;               \-> else  -/       
       (let ((con (gensym "con-"))
             (alt (gensym "con-")))
         (cps-make-letcont
          (list con alt)
          (list
           (cps-make-lambda '() #f (visit k consequent env))
           (cps-make-lambda '() #f (visit k alternate env)))
          (with-value-name
           (lambda (test-val)
             (cps-make-if test-val con alt))
           test
           env))))
      (($ <lexical-ref> src name gensym)
       (cps-make-call
        (cps-make-primitive 'ref)
        k
        (list (cdr (vhash-assq gensym env)))))
      (($ <lexical-set> src name gensym exp)
       (with-value-name
        (lambda (val-name)
          (cps-make-call
           (cps-make-primitive 'set)
           k
           (list (cdr (vhash-assq gensym env))
                 val-name)))
        exp env))
      (($ <seq> src head tail)
       (let ((con (gensym "con-"))
             (rest (gensym "rest-")))
         (cps-make-letcont
          (list con)
          (list (cps-make-lambda '() rest
                            (visit k tail env)))
          (visit con head env))))
      (($ <let> src names gensyms vals exp)
       (with-values-named
        (with-variable-boxes
         (lambda (env)
           (visit k exp env))
         gensyms env)
        vals gensyms env))
      (($ <toplevel-ref> src name)
       (let ((var-name (gensym "var-")))
         (cps-make-letval
          (list var-name)
          (list (cps-make-toplevel-var name))
          (cps-make-call
           (cps-make-primitive 'ref)
           k
           (list var-name)))))
      (($ <toplevel-set> src name exp)
       (with-value-name
        (lambda (set-val)
          (let ((var-name (gensym "var-")))
            (cps-make-letval
             (list var-name)
             (list (cps-make-toplevel-var name))
             (cps-make-call
              (cps-make-primitive 'set)
              k
              (list var-name set-val)))))
        exp env))
      (($ <const> src exp)
       (let ((v (gensym "val-")))
         (cps-make-letval
          (list v)
          (list (cps-make-const exp))
          (cps-make-call k #f (list v)))))
      (x (error "Unrecognized tree-il:" x))))

  (visit 'return tree vlist-null))
