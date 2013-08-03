(define-module (language cps cps-isomorphic)
  #:use-module (language cps)
  #:use-module (ice-9 match)
  #:use-module (srfi srfi-1)
  #:export (cps-isomorphic?))

;; our goal is to say when two pieces of CPS are isomorphic. This is
;; useful in testing the CPS compiler. We take advantage of the fact
;; that CPS names are unique to keep all of ours in one big hash table.

(define (cps-isomorphic? x y)
  (let ((x-to-y-names (make-hash-table)))
    ;; this function adds names to the name table while also checking
    ;; that the name lists are of the same length.
    (define (match-names! x-names y-names)
      (cond ((and (null? x-names) (null? y-names))
             #t)
            ((and (pair? x-names) (pair? y-names))
             (hashq-set! x-to-y-names
                         (car x-names) (car y-names))
             (match-names! (cdr x-names) (cdr y-names)))
            (else
             (pk "Couldn't match" (car x-names) (car y-names))
             #f)))

    (define (names-match? x y x-name y-name)
      (or (eq? (hashq-ref x-to-y-names x-name) y-name)
          (begin (pk "Couldn't match" x y) #f)))

    ;; one continuation has a special name.
    (match-names! '(return) '(return))

    (let rec ((x x) (y y))
      (match (cons x y)
        ((($ <letval> x-names x-vals x-body) .
          ($ <letval> y-names y-vals y-body))
         (and (every rec x-vals y-vals)
              (match-names! x-names y-names)
              (rec x-body y-body)))
        ((($ <letcont> x-names x-conts x-body) .
          ($ <letcont> y-names y-conts y-body))
         (and (match-names! x-names y-names)
              (every rec x-conts y-conts)
              (rec x-body y-body)))
        ((($ <letrec> x-names x-funcs x-body) .
          ($ <letrec> y-names y-funcs y-body))
         (and (match-names! x-names y-names)
              (every rec x-funcs y-funcs)
              (rec x-body y-body)))
        ((($ <const> x-val) . ($ <const> y-val))
         (if (equal? x-val y-val)
             #t
             (begin (pk "Couldn't match" x y)
                    #f)))
        ((($ <var> x-val) . ($ <var> y-val))
         (names-match? x y x-val y-val))
        ((($ <lambda> x-names x-rest x-body) .
          ($ <lambda> y-names y-rest y-body))
         (and (match-names! x-names y-names)
              (cond
               ((and (not x-rest) (not y-rest)) #t)
               ((and x-rest y-rest)
                (match-names! (list x-rest) (list y-rest)))
               (else (pk "couldn't match" x y) #f))
              (rec x-body y-body)))
        ((($ <call> x-proc x-cont x-args) .
          ($ <call> y-proc y-cont y-args))
         (and (cond ((and (primitive? x-proc)
                          (primitive? y-proc))
                     (eq? (primitive-name x-proc)
                          (primitive-name y-proc)))
                    ((and (symbol? x-proc) (symbol? y-proc))
                     (names-match? x y x-proc y-proc))
                    (else (pk "Couldn't match" x y) #f))
              (names-match? x y x-cont y-cont)
              (every (lambda (x-arg y-arg)
                       (names-match? x y x-arg y-arg))
                     x-args y-args)))
        ((($ <module-var> x-mod x-name x-public) .
          ($ <module-var> y-mod y-name y-public))
         (and (equal? x-mod y-mod)
              (eq? x-name y-name)
              (eq? x-public y-public)))
        ((($ <if> x-test x-then x-else) .
          ($ <if> y-test y-then y-else))
         (and (names-match? x y x-test y-test)
              (names-match? x y x-then y-then)
              (names-match? x y x-else y-else)))
        ((x . y) (pk "Couldn't match" x y) #f)
        (other (error "Internal error" other))))))

