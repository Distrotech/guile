(define-module (language tree-il compile-cps)
  #:use-module (language tree-il)
  #:use-module ((language cps)
                #:renamer (symbol-prefix-proc 'cps-))
  #:use-module (ice-9 match)
  #:use-module (ice-9 vlist)
  #:export (tree-il->cps))


;; k is the continuation
(define (tree-il->cps tree)
  ;; with-value-name first generates some CPS that finds the value of
  ;; tree, and then calls 'gen-k' to generate more CPS code - but
  ;; 'gen-k' is called with a name which can reference the value of
  ;; tree. the real point is to abstract out the idea of *not*
  ;; generating extra continuations for lexical variable references. we
  ;; could always optimize them out later, but it seems easier to just
  ;; not make them in the first place.
  (define (with-value-name gen-k tree env)
    (if (lexical-ref? tree)
        (gen-k (lexical-ref-gensym tree))
        (let ((con (gensym "con-"))
              (val (gensym "val-")))
          (cps-make-letcont
           (list con)
           (list (cps-make-lambda (list val) (gen-k val)))
           (visit con tree env)))))

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

  ;; with-variable-boxes generates CPS that makes variable objects for
  ;; the given variables and then calls 'gen-k' with a new environment
  ;; in which the given names are mapped to the names of their boxes.
  (define (with-variable-boxes gen-k vars env)
    (let iter ((vars vars)
               (env env))
      (if (null? vars)
          (gen-k env)
          (let ((var-name (gensym "var-")))
            (cps-make-letval
             (list var-name)
             (list (cps-make-var (car vars)))
             (iter (car vars)
                   (vhash-consq (car vars) var-name env)))))))
  
  ;; visit returns a CPS version of tree which ends by calling
  ;; continuation k. 'env' is a vhash that maps Tree-IL variable gensyms
  ;; to CPS variable names.
  (define (visit k tree env)
    (match tree
      ;; note: 1. we only support lambdas with one case right now, and
      ;; totally ignore optional, rest and keyword arguments. 2. we only
      ;; support lambda forms as the outermost part of the Tree-IL.
      (($ <lambda> src meta
          ($ <lambda-case> src req opt rest kw inits gensyms body alternate))
       (cps-make-lambda gensyms
         (visit 'return body env)))
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
           (cps-make-lambda '() (visit k consequent env))
           (cps-make-lambda '() (visit k alternate env)))
          (with-value-name
           (lambda (test-val)
             (cps-make-if test-val con alt))
           test
           env))))
      (($ <lexical-ref> src name gensym)
       (cps-make-call k #f (list gensym)))
      (($ <toplevel-ref> src name)
       (let ((var-name (gensym "var-")))
         (cps-make-letval
          (list var-name)
          (list (cps-make-toplevel-var name))
          (cps-make-call
           (cps-make-primitive 'ref)
           k
           (list var-name)))))
      (($ <const> src exp)
       (let ((v (gensym "val-")))
         (cps-make-letval
          (list v)
          (list exp)
          (cps-make-call k #f (list v)))))
      (x (error "Unrecognized tree-il:" x))))

  (visit 'return tree vlist-null))
