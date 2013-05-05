(define-module (language cps annotate)
  #:use-module (language cps)
  #:use-module (system base syntax)
  #:export (annotate-cps))

;; return CPS annotated with the given function. a name n will be
;; replaced with (cons n (annotator n)). if the annotation is #f, it
;; won't be shown. use like this at the REPL: ,pp (annotate-cps cps
;; cool-annotator-function). as a special case, if the annotator itself
;; is #f, pretty-print the CPS code (just like if the annotator returned
;; #f for every CPS element).
(define (annotate-cps cps annotator)  
  (define (visit cps)
    (define maybe-cons-ann
      (if annotator
          (lambda (n)
            (let ((ann (annotator cps)))
              (if ann
                  (cons n ann)
                  n)))
          (lambda (n) n)))
    
    (cond ((symbol? cps)
           (maybe-cons-ann cps))
          ((boolean? cps)
           ;; we get a boolean when we're called on the cont of a call
           ;; to a letcont continuation, or the rest argument of a lambda.
           cps)
          (else
           (record-case cps
                        ((<call> proc cont args)
                         `(,(maybe-cons-ann 'call)
                           ,(visit proc)
                           ,(visit cont)
                           ,(map visit args)))
                        ((<lambda> names rest body)
                         `(,(maybe-cons-ann 'lambda)
                           ,(map visit names)
                           ,(visit rest)
                           ,(visit body)))
                        ((<letval> names vals body)
                         `(,(maybe-cons-ann 'letval)
                           ,(map visit names)
                           ,(map visit vals)
                           ,(visit body)))
                        ((<letcont> names conts body)
                         `(,(maybe-cons-ann 'letcont)
                           ,(map visit names)
                           ,(map visit conts)
                           ,(visit body)))
                        ((<letrec> names funcs body)
                         `(,(maybe-cons-ann 'letrec)
                           ,(map visit names)
                           ,(map visit funcs)
                           ,(visit body)))
                        ((<primitive> name)
                         `(,(maybe-cons-ann 'primitive)
                           ,name))
                        ((<if> test consequent alternate)
                         `(,(maybe-cons-ann 'if)
                           ,(visit test)
                           ,(visit consequent)
                           ,(visit alternate)))
                        ((<const> value)
                         `(,(maybe-cons-ann 'const)
                           ,value))
                        ((<var> value)
                         `(,(maybe-cons-ann 'var)
                           ,(visit value)))
                        ((<module-var> mod name public?)
                         `(,(maybe-cons-ann 'module-var)
                           ,name))))))
  
  (visit cps))
