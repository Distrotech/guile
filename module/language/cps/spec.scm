(define-module (language cps spec)
  #:use-module (system base compile)
  #:use-module (language tree-il compile-cps)
  #:use-module (language cps compile-rtl)
  #:use-module (system vm rtl)
  #:export (cps-compile))

;; since CPS isn't complete yet, we don't want to make it part of the
;; system compiler graph, so we have our own compile function.
(define* (cps-compile x #:key (from 'scheme) (to 'value))
  (cond ((eq? from to) x)
        ((not (memq to '(scheme tree-il cps rtl value)))
         (error "Unrecognized language" to))
        (else
         (case from
           ((scheme) (cps-compile (compile x #:to 'tree-il)
                                  #:from 'tree-il #:to to))
           ((tree-il) (cps-compile (tree-il->cps x)
                                   #:from 'cps #:to to))
           ((cps) (allocate-registers-and-labels! x)
            (cps-compile (cps->rtl x)
                         #:from 'rtl #:to to))
           ((rtl) (assemble-program x))
           (else (error "Unrecognized language" from))))))
