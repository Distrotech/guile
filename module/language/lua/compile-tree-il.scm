;;; Guile Lua --- compiler

;;; Copyright (C) 2010 Free Software Foundation, Inc.
;;;
;;; This library is free software; you can redistribute it and/or
;;; modify it under the terms of the GNU Lesser General Public
;;; License as published by the Free Software Foundation; either
;;; version 3 of the License, or (at your option) any later version.
;;;
;;; This library is distributed in the hope that it will be useful,
;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;; Lesser General Public License for more details.
;;;
;;; You should have received a copy of the GNU Lesser General Public
;;; License along with this library; if not, write to the Free Software
;;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

;;; Code:

(define-module (language lua compile-tree-il)
  #:use-module (language tree-il)
  #:use-module ((srfi srfi-1) #:select (map!))
  #:use-module (srfi srfi-39)
  #:use-module ((system base syntax) #:select (record-case))
  #:use-module (rnrs control)

  #:use-module (language lua common)
  #:use-module (language lua parser)
  #:use-module (language lua runtime)

  #:export (compile-tree-il))

;; utilities

(define *runtime-name* '(language lua runtime))
(define no-arguments '(() #f #f #f () ()))


(define (ref-runtime src name)
  (make-module-ref src *runtime-name* name #t))

(define (make-runtime-application src name arguments)
  "Apply a function in the (language lua runtime) module"
  (make-application src (ref-runtime src name) arguments))

(define (make-lua-conditional src condition then else)
  "Generate a conditional with (@ (language lua runtime) true?)"
  (make-conditional src (make-runtime-application src 'true? (list condition)) then else))

(define (make-table-ref src table index)
  (make-runtime-application src 'index
    (list table (if (symbol? index) (make-const src (symbol->string index)) index))))

(define (make-table-set! src table index exp)
  (make-runtime-application src 'new-index!
    (list table (if (symbol? index) (make-const src (symbol->string index)) index) exp)))

(define (apply-named-lua-function src name get-body)
  (let* ((name (gensym (string-append " " name)))
         (parameters (list name)))
    (make-application
     src
     (make-module-ref src '(guile) 'catch #t)
     (list
      (make-const src 'lua-break)
      (make-argless-lambda src
        (make-let
         src
         parameters parameters
         (list (make-lambda src '() (get-body name)))
         (make-application src (make-lexical-ref src name name) '())))
      (make-arg-ignoring-lambda src
       (make-void src))))))

(define (while-loop->tree-il src condition body)
  "Create a WHILE loop, used by both WHILE and REPEAT."
  (apply-named-lua-function
   src "while"
   (lambda (loop)
     (make-lua-conditional
      src
      condition
      (make-sequence src
                     (list body (make-application src (make-lexical-ref src loop loop) '())))
      (make-void src)))))

;; calling conventions
(define (make-plain-lambda-case src args gensyms body . alternate)
  (make-lambda-case src args #f #f #f '() (or gensyms args) body (and (not (null? alternate)) (car alternate))))

(define (make-plain-lambda src args gensyms body . alternate)
  (make-lambda src '() (apply make-plain-lambda-case (append (list src args gensyms body) alternate))))

(define (make-arg-ignoring-lambda src body)
  (make-lambda src '() (make-lambda-case src '() #f '_ #f '() (list (gensym "_")) body #f)))

(define (make-argless-lambda src body)
  (make-plain-lambda src '() #f body))

(define (adjust-to-single-value src exp)
  "adjust an expression so that it only returns one result; the rest are dropped silently"
  (define value-gensym (gensym "%value"))
  (define adjust-gensym (gensym "%adjust"))
  (make-letrec src
  #t
  '(%adjust)
  (list adjust-gensym)
  (list
    (make-plain-lambda
     src
     '(%value)
     (list value-gensym)
     (make-lexical-ref src '%value value-gensym)))
   (make-application
    src
    (make-primitive-ref src 'call-with-values)
    (list (make-argless-lambda src exp) (make-lexical-ref src '%adjust adjust-gensym)))))

;; main compiler

(define context (make-parameter #f))

(define* (compile exp #:optional last-in-list?)
  (define* (map-compile exps #:optional care-about-last?)
    (let lp ((ls exps)
             (tree '()))
      (if (null? ls)
          (reverse! tree)
          (lp (cdr ls) (cons (compile (car ls) (and care-about-last? (null? (cdr ls)))) tree)))))

  (record-case exp
    ((ast-sequence src exps)
     (if (null? exps)
         (make-void src)
         (make-sequence src (map-compile exps))))

    ((ast-literal src exp)
     (if (eq? exp *unspecified*)
         (make-void src)
         (make-const src exp)))

    ((ast-return src exp)
     (make-application src (make-primitive-ref src 'return)
       (list (make-application src
              (make-primitive-ref src 'values)
              (if (list? exp) (map-compile exp #t) (list (compile exp)))))))

    ((ast-function src name arguments argument-gensyms variable-arguments? body)
     ;; ... is always attached because lua functions must ignore
     ;; variable arguments; the parser will catch it if ... is used in a
     ;; function that doesn't have ... in the parameter list
     (make-lambda src (if name `((name . ,name)) '()) (make-lambda-case src '() arguments '... #f (map (lambda (x) (make-const src #nil)) arguments) (append! argument-gensyms (list '...)) (compile body) #f)))

    ((ast-function-call src operator operands)
 #|    (let* ((proc (compile operator))
            (args (make-application src (make-primitive-ref src 'list) (map-compile operands)))
            (app-args (make-application src (make-primitive-ref src 'list) (list proc args)))
            (app (make-application src (make-primitive-ref src 'apply) (list (make-primitive-ref src 'apply) app-args)))) |#
     (let* ((proc (compile operator))
            (app (make-application src proc (map-compile operands))))
       (if (ast-global-ref? operator)
           (make-sequence src (list
                               (make-application src (make-module-ref src '(language lua runtime) 'check-global-function #t)
                                                 (list (make-const src (ast-global-ref-name operator))
                                                       proc))
                               app))
           app)))

    ((ast-local-block src names gensyms initial-values exp)
     (make-let src names gensyms (map-compile initial-values) (compile exp)))

    ((ast-local-ref src name gensym)
     (make-lexical-ref src name gensym))

    ((ast-local-set src name gensym exp)
     (make-lexical-set src name gensym (compile exp)))

    ((ast-global-ref src name)
     (make-table-ref src (ref-runtime src '*global-env-table*) name))

    ((ast-global-set src name exp)
     (make-table-set! src (ref-runtime src '*global-env-table*) name (compile exp)))

    ((ast-table-ref src table key)
     (make-table-ref src (compile table) (compile key)))

    ((ast-table-set src table key exp)
     (make-table-set! src (compile table) (compile key) (compile exp)))

    ((ast-condition src test then else)
     (make-conditional src (compile test) (compile then) (compile else)))

    ((ast-while-loop src condition body)
     (parameterize
         ((context 'while-loop))
       (while-loop->tree-il src (compile condition) (compile body))))

    ;; TODO: in order for this to have the same semantics as lua, all
    ;; potential subforms of while should introduce their own context,
    ;; so you can't use break inside of a function inside a while loop
    ;; for instance
    ((ast-break src)
     (unless (memq (context) '(while-loop list-for-loop numeric-for-loop))
       (syntax-error src "no loop to break"))
     (make-application src (make-module-ref src '(guile) 'throw #t) (list (make-const src 'lua-break)))
     )

    ((ast-list-for-loop src names gs-names exps body)
     (let* ((gs-iterator (gensym "iterator"))
            (gs-state (gensym "state"))
            (gs-variable (gensym "variable"))
            (gs-iterator2 (gensym "iterator"))
            (gs-state2 (gensym "state"))
            (gs-variable2 (gensym "variable"))
            (gs-loop (gensym "loop")))
       (parse-tree-il
        `(letrec*
           ;; names
           (iterator state variable loop)
           ;; gensyms
           (,gs-iterator ,gs-state ,gs-variable ,gs-loop)
           ;; vals
           ((void) (void) (void)
            (lambda ()
              (lambda-case
               (,no-arguments
                (begin
                  ;; even more complicated, assigning the values to the loop variables
                  (apply (primitive call-with-values)
                         (lambda () (lambda-case (,no-arguments (apply (lexical iterator ,gs-iterator) (lexical state ,gs-state) (lexical variable ,gs-variable)))))
                         (lambda () (lambda-case ((,names #f #f #f () ,gs-names)
                            ;; almost to the actual loop body, hang in there
                            (begin
                              (set! (lexical variable ,gs-variable) (lexical ,(car names) ,(car gs-names)))
                              (if (apply (primitive eq?) (lexical variable ,gs-variable) (const #nil))
                                  (apply (@ (guile) throw) (const lua-break))
                                  (void))
                              ,(parameterize ((context 'list-for-loop)) (unparse-tree-il (compile body)))
                              (apply (lexical loop ,gs-loop))))))))))))
           ;; initialize variables and start loop
           (begin
             (apply (primitive call-with-values)
                    (lambda () (lambda-case (,no-arguments ,(unparse-tree-il (make-sequence src (map-compile exps))))))
                    (lambda () (lambda-case (((iterator state variable) #f #f #f () (,gs-iterator2 ,gs-state2 ,gs-variable2))
                                             (begin
                                               (set! (lexical iterator ,gs-iterator) (lexical iterator ,gs-iterator2))
                                               (set! (lexical state ,gs-state) (lexical state ,gs-state2))
                                               (set! (lexical variable ,gs-variable) (lexical variable ,gs-variable2)))))))
             (apply (@ (guile) catch)
                    (const lua-break)
                    (lambda () (lambda-case (,no-arguments
                                             (apply (lexical loop ,gs-loop)))))
                    (lambda () (lambda-case (((key) #f #f #f () (,(gensym "key"))) (void))))))))))

    ;; TODO: in order for this to have the same semantics as lua, all
    ;; potential subforms of while should introduce their own context,
    ;; so you can't use break inside of a function inside a while loop
    ;; for instance

    ((ast-numeric-for-loop src named initial limit step body)
     ;; as per 5.1 manual 2.4.5, the numeric for loop can be decomposed into simpler forms
     ;; still doesn't have proper behavior, should be able to return and break inside a loop
     (let* ((gs-named (gensym (symbol->string named)))
            (gs-variable (gensym "variable"))
            (gs-limit (gensym "limit"))
            (gs-step (gensym "step"))
            (gs-loop (gensym "loop"))
            (while-condition
             `(if (apply (primitive >) (lexical step ,gs-step) (const 0))
                 (if (apply (primitive <=) (lexical variable ,gs-variable) (lexical limit ,gs-limit))
                     (apply (lexical loop ,gs-loop))
                     (void))
                 (void))))
       (parse-tree-il
        `(letrec*
           ;; names
           (,named variable limit step loop)
           ;; gensyms
           (,gs-named ,gs-variable ,gs-limit ,gs-step ,gs-loop)
           ;; vals
           ,(cons
              '(const #f)
              (append
               (map (lambda (x) `(apply (@ (language lua runtime) tonumber) ,(unparse-tree-il (compile x)))) (list initial limit step))
               ;; loop body
               (list
                `(lambda ()
                   (lambda-case
                    ;; no arguments
                    ((() #f #f #f () ())
                     ;; body
                     (begin
                       (set! (lexical ,named ,gs-named) (lexical variable ,gs-variable))
                       ,(parameterize ((context 'numeric-for-loop)) (unparse-tree-il (compile body)))
                       (set! (lexical variable ,gs-variable) (apply (primitive +) (lexical variable ,gs-variable) (lexical step ,gs-step)))
                       ,while-condition
                     )))))))
           ;; body
           (begin
             ;; if not (var and limit and step) then error() end
             (if (apply (primitive not)
                        (if (apply (@ (language lua runtime) true?) (lexical variable ,gs-variable))
                            (if (apply (@ (language lua runtime) true?) (lexical limit ,gs-limit))
                                (if (apply (@ (language lua runtime) true?) (lexical step ,gs-step))
                                    (const #t)
                                    (const #f))
                                (const #f))
                            (const #f)))
                 (apply (@ (guile) error))
                 (void))
             ,while-condition
             )))))

    ((ast-table-literal src fields)
     (let* ((table (make-runtime-application src 'make-table '())))
       (if (not (null? fields))
           ;; if the table's fields are initialized inside of the literal, we need
           ;; to store it in a variable and initialize its values
           (let* ((temp-name (gensym " table"))
                  (names (list temp-name))
                  (ref (make-lexical-ref src temp-name temp-name)))
             (make-let
              src
              names names
              (list table)
              (make-sequence
               src
               (append!
                (map
                 (lambda (x)
                   (let* ((key (compile (car x)))
                          (value (compile (cdr x))))
                     (make-runtime-application src 'new-index! (list (make-lexical-ref src temp-name temp-name) key value))))
                 fields)
                (list ref)))))
           ;; otherwise we can just return the fresh table
           table)))

    ((ast-unary-operation src operator right)
     ;; reduce simple negative numbers, like -5, to literals
     (if (and (eq? operator #\-) (ast-literal? right) (number? (ast-literal-exp right)))
         (make-const src (- (ast-literal-exp right)))
         (make-application
          src
          (case operator
            ((#\-) (ref-runtime src 'unm))
            ((#\#) (ref-runtime src 'len))
            ((not) (make-primitive-ref src 'not)))
          (list (compile right)))))

    ((ast-binary-operation src operator left right)
     (let ((left (compile left))
           (right (compile right)))
       (case operator
         ((#\+ #\- #\* #\/ #\^ #\< #\> #:<= #:>= #:== #:~= #:concat)
          (let* ((result
                  (make-runtime-application
                   src
                   (case operator
                     ((#\+) 'add)
                     ((#\-) 'sub)
                     ((#\*) 'mul)
                     ((#\/) 'div)
                     ((#\^) 'pow)
                     ((#\<) 'lt)
                     ((#\>) 'lt)
                     ((#:<=) 'le)
                     ((#:>=) 'le)
                     ((#:==) 'eq)
                     ((#:~=) 'neq)
                     ((#:concat) 'concat)
                     (else (error #:COMPILE "unhandled binary operator" operator)))
                   ;; reverse order of arguments for >, >= so they can be implemented on top of <, <=
                   (if (or (eq? operator #\>) (eq? operator #:>=))
                       (list right left)
                       (list left right)))))
            result))
         ((#:or)
          (make-lua-conditional
           src
           left
           left
           right))
         ((#:and)
          (make-lua-conditional
           src
           left
           right
           left))
         (else (error #:COMPILE "unknown binary operator" operator)))))
    ))

;; exported compiler function
(define (compile-tree-il exp env opts)
  (parameterize
      ((context #f))
    (values (compile exp) env env)))
