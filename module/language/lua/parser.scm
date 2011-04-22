;;; Guile Lua --- parser

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

;; parser.scm --- lua parser

;; This parser is based heavily on Lua's parser. It does not use
;; lalr-scm, because Lua's grammar is a little too plucky. Unlike Lua's
;; parser, it returns an abstract syntax tree instead of incrementally
;; compiling the source.

(define-module (language lua parser)
  #:use-module (srfi srfi-1)
  #:use-module (srfi srfi-8)
  #:use-module (srfi srfi-9)
  #:use-module (rnrs control)
  #:use-module (language lua common)
  #:use-module (language lua lexer)
  #:use-module (language lua runtime)
  #:export (make-parser read-lua))

;; Implicitly named records
(letrec-syntax
    ((define-record
      (lambda (stx)
        (define (id template-id . rest)
          (datum->syntax template-id
                         (apply symbol-append (map syntax->datum rest))))
        (syntax-case stx ()
          ((_ name field ...)
           (with-syntax
               ((constructor (id #'name 'make- #'name))
                (predicate (id #'name #'name '?))
               ((setter ...)
                (map (lambda (x) (id #'name #'name '- x '!)) #'(field ...)))
               ((getter ...)
                (map (lambda (x) (id #'name #'name '- x)) #'(field ...))))

             #'(begin
                 (define-record-type name
                   (constructor field ...)
                   predicate
                   (field getter setter) ...)
                 (export name)
                 (export constructor)
                 (export predicate)
                 (export getter)
                 ...
                 (export setter)
                 ...
                 ))))))

     (define-ast
      (lambda (stx)
        (define (id template-id . rest)
          (datum->syntax template-id
                         (apply symbol-append (map syntax->datum rest))))

        (syntax-case stx ()
          ((_ "aux" name field ...)
           #`(define-record #,(id #'name 'ast- #'name) #,(id #'name 'src) field ...))

          ((_ (name field ...) ...)
           #`(begin
               (define-ast "aux" name field ...)
               ...))))))

  ;; Environments & bindings
  (define-record environment parent bindings)
  (define-record binding name gensym type)

  ;; Abstract syntax tree -- all of these records are automatically
  ;; prefixed with 'ast- and have an SRC field attached.
  (define-ast
   (unary-not exp)
   (literal exp)
   (sequence exps)
   (return exp)
   (condition test then else)
   (local-block names gensyms initial-values exp)
   (unary-operation operator right)
   (local-ref name gensym)
   (local-set name gensym exp)
   (global-ref name)
   (global-set name exp)
   (table-ref table key)
   (table-set table key exp)
   (table-literal fields)
   (while-loop condition body)
   (numeric-for-loop named initial limit step body)
   (list-for-loop names gs-names exps body)
   (break)
   (function name arguments argument-gensyms variable-arguments? body)
   (function-call operator operands)
   (binary-operation operator left right)
   (variable-arguments))

  ) ; letrec-syntax

;; Constants
(define *nil-literal* (make-ast-literal #f #nil))
(define *void-literal* (make-ast-literal #f *unspecified*))
(define *default-for-step* (make-ast-literal #f 1))

(define (end-of-chunk? token)
  "Returns true if TOKEN denotes the end of a grammatical chunk."
  (or (memq token '(#:else #:elseif #:end #:until)) (eof-object? token)))

(define *special-tokens*
  '(#\. #\( #\) #\, #\- #\< #\; #\+ #\{ #\} #\[ #\] #\: #\#
    #:function #:end #:if #:return #:elseif #:then #:else #:true #:false
    #:nil #:== #:~= #:= #\> #:>= #:<= #:local #:varargs #:break #:do #:in
    #:and #:or))

(define (token/type t)
  (cond
   ((number? t) 'NUMBER)
   ((eof-object? t) 'EOS)
   ((symbol? t) 'NAME)
   ((string? t) 'STRING)
   ((memv t *special-tokens*) t)
   (else (error 'TOKEN/TYPE t))))

;; infix operator parsing
(define (binary-operator? t)
  "Return #t if the token may be a binary operator"
  (memv t '(#\+ #\* #\/ #\- #\^ #\< #\> #:== #:~= #:and #:or #:concat)))

(define (unary-operator? t)
  "Return #t if the token may be a unary operator"
  (memv t '(#\- #\# #:not)))

;; Operator precedence
(define *unary-priority* 80)

(define (priority o)
  "Return the priority of a given operator token"
  (case o
    ((#:or) 10)
    ((#:and) 20)
    ((#:== #:~= #:<= #:>= #\< #\>) 30)
    ((#\+ #\-) 60)
    ((#\* #\/ #\%) 70)
    ((#\^ #:concat) 99)))

;;;;; TREE-IL UTILITIES

(define (make-lua-assignment left right)
  "Generate an assignment from a variable and an expression"
  (cond
   ((ast-global-ref? left)
    (make-ast-global-set (ast-global-ref-src left)
                         (ast-global-ref-name left)
                         right))
   ((ast-local-ref? left)
    (make-ast-local-set (ast-local-ref-src left)
                        (ast-local-ref-name left)
                        (ast-local-ref-gensym left)
                        right))
   ((ast-table-ref? left)
    (make-ast-table-set (ast-table-ref-src left)
                        (ast-table-ref-table left)
                        (ast-table-ref-key left)
                        right))
   (else
    (error 'MAKE-LUA-ASSIGNMENT "should not happen"))))

(define (wrap-expression-in-environment src e x)
  "Wrap an expression in an enclosing lexical environment if necessary"
  (let ((locals (filter-map (lambda (binding)
                              (let ((b (cdr binding)))
                                (and (eq? (binding-type b) 'local) b)))
                            (environment-bindings e))))
    (if (null? locals)
        x
        (make-ast-local-block src
                              (map binding-name locals)
                              (map binding-gensym locals)
                              (map (lambda (c) *nil-literal*) locals)
                              x))))

;;;;; PARSER

(define (make-parser port)
  (define lexer-pair
    (call-with-values (lambda () (make-lexer port)) cons))

  (define get-source-info (car lexer-pair))
  (define lexer (cdr lexer-pair))

  ;; We need two tokens of lookahead
  (define token2 #f)

  (define (lookahead!)
    (set! token2 (lexer)))

  ;; Current token
  (define token)

  ;; Lexical environment
  (define environment #f)

  ;; True if inside a function and the function accepts variable arguments
  (define *vararg-function* #f)

  ;;;;; ENVIRONMENTS
  (define (enter-environment!)
    "Create a new environment, and set ENVIRONMENT to it"
    (set! environment
      (make-environment environment '())))

  (define (leave-environment!)
    "Set ENVIRONMENT to the current ENVIRONMENT's parent"
    (if (not environment)
        (error 'LEAVE-ENVIRONMENT! "should not happen"))
    (set! environment
      (environment-parent environment)))

  ;; Type may be 'parameter or 'local
  (define (environment-define! name type)
    "Define a new variable with NAME and TYPE"
    (if (not (member name (environment-bindings environment)))
        (environment-bindings!
         environment
         (acons name
                (make-binding
                 name
                 (gensym (string-append " " (symbol->string name)))
                 type)
                (environment-bindings environment)))))

  ;; Environment lookup procedures -- these fail silently and return #f,
  ;; because Lua allows global variables to be referenced without being
  ;; predefined

  (define* (environment-lookup-aux name #:optional (e environment))
    "Given a variable's NAME, look up its binding."
    (and e (or (assq-ref (environment-bindings e) name)
               (environment-lookup-aux name (environment-parent e)))))

  (define (environment-lookup-gensym name)
    "Given a variable's NAME, look up its gensym"
    (and=> (environment-lookup-aux name) binding-gensym))

  (define (environment-lookup-type name)
    "Given a variable's NAME, look up its global"
    (and=> (environment-lookup-aux name) binding-type))

  (define (resolve-ref src name)
    "Determine whether a variable reference is global or local"
    (let ((sym (environment-lookup-gensym name)))
      (if sym
          (make-ast-local-ref src name sym)
          (make-ast-global-ref src name))))

  ;;;;; LEXER INTERACTION

  (define (advance-aux)
    "Read a new token and store it in TOKEN"
    (if token2
        (begin
          (set! token token2)
          (set! token2 #f))
        (set! token (lexer))))

  (define-syntax advance!
    (syntax-rules ()
      ((_ x) (let ((t x)) (advance-aux) t))
      ((_) (advance-aux))))

  (define (assert-token-type type)
    "Throw an error if the current token does not have the expected type"
    (if (not (equal? (token/type token) type))
        (syntax-error (get-source-info) "expected ~a" type)))

  (define (maybe-skip-next! c)
    "Skip a token"
    (and (equal? token c) (advance! #t)))

  (define (enforce-next! expect)
    "Throw an error if the current token is not the expected token"
    (unless (maybe-skip-next! expect)
      (syntax-error (get-source-info) "expected '~A' but got '~A'" expect token)))

  ;;;;; GRAMMAR

  ;; single-name -> NAME
  (define (single-name)
    (let ((save token))
      (assert-token-type 'NAME)
      (advance!)
      save))

  ;; single-variable -> single-name
  (define (single-variable)
    (let* ((src (get-source-info))
           (save (single-name)))
      (resolve-ref src save)))

  ;; application-arguments -> '(' [ expression-list ] ')' | STRING | TABLE
  (define (application-arguments)
    (case (token/type token)
      ((STRING)
       (let ((string token))
         (advance!)
         (list (make-ast-literal #f string))))
      ((#\{)
       ;; TODO: table constructor
       ;; '('
       (list (table-literal)))
      ((#\()
       (advance!)
       (if (eqv? token #\))
           ;; ')'
           (advance! '())
           ;; [ expression-list ]
           (let* ((arguments (expression-list)))
             ;; ')'
             (enforce-next! #\))
             arguments)))
      (else
       (error 'APPLICATION-ARGUMENTS "should not happen"))))

  ;; prefix-expression -> NAME | '(' expression ')'
  (define (prefix-expression)
    (case (token/type token)
      ;; NAME
      ((NAME) (single-variable))
      ;; '('
      ((#\()
       (advance!)
       ;; expression
       (let ((save (expression)))
         ;; ')'
         (enforce-next! #\))
         ;; finished
         save))
      (else (syntax-error (get-source-info) "unexpected symbol ~a" token))))

  ;; index -> '[' expression ']'
  (define (index)
    (enforce-next! #\[)
    (let ((index (expression)))
      (enforce-next! #\])
      index))

  ;; field-selector -> '.' NAME
  (define (field-selector src prefix)
    (make-ast-table-ref src prefix
                        (make-ast-literal src (symbol->string (single-name)))))

  ;; primary-expression -> prefix-expression { field-selector [ application-arguments ] | index | application-arguments }
  (define (primary-expression)
    (let ((src (get-source-info)))
      ;; prefix-expression
      (let lp ((expr (prefix-expression)))
        (case (token/type token)
          ;; field-selector
          ((#\.) (advance!) (lp (field-selector src expr)))
          ;; index
          ((#\[) (lp (make-ast-table-ref src expr (index))))
          ;; ':' NAME application-arguments
          ((#\:)
           (advance!)
           ;; FIXME: double-evaluation of expr
           (let* ((name (single-name))
                  (args (application-arguments)))
             (lp (make-ast-function-call
                  src
                  (make-ast-table-ref
                   src expr (make-ast-literal src (symbol->string name)))
                  (cons expr args)))))
          ;; application-arguments
          ((#\( STRING #\{)
           (lp (make-ast-function-call src expr (application-arguments))))
          (else expr)))))

  ;; expression-statement -> function | assignment
  (define (expression-statement)
    (let ((primary (primary-expression)))
      (if (ast-function-call? primary)
          primary
          (assignment primary))))

  ;; record-field -> (NAME | index) '=' expression
  (define (record-field)
    (let* ((index (cond
                   ;; NAME
                   ((eq? (token/type token) 'NAME)
                    (let ((tmp (make-ast-literal #f (symbol->string token))))
                      (advance!)
                      tmp))
                   ;; index
                   (else (index))))
           (value (begin
                    ;; '='
                    (enforce-next! #:=)
                    ;; expression
                    (expression))))
      (values index value)))

  ;; field -> expression | record-field
  (define (field)
    (case (token/type token)
      ((NAME)
       (lookahead!)
       (if (eq? token2 #:=)
           (record-field)
           (values #f (expression))))
      ((#\[) (record-field))
      (else (values #f (expression)))))

  ;; field-separator -> ',' | ';'
  ;; table-fields -> [ field { field-separator field } [ field-separator ] ]
  (define (table-fields src)
    (let loop ((implicit-index 1)
               (tree '()))
      (if (eqv? token #\})
          (reverse! tree)
          (receive (index expr) (field)
            ;; field-separator
            (maybe-skip-next! #\,)
            (maybe-skip-next! #\;)
            (loop
             (if (not index) (+ implicit-index 1) implicit-index)
             (cons
              (cons (or index (make-ast-literal src implicit-index)) expr)
              tree))))))

  ;; table-literal -> '{' table-fields '}'
  (define (table-literal)
    (let ((src (get-source-info)))
      ;; '{'
      (enforce-next! #\{)
      ;; bind the table to a temporary variable with LET as it's needed
      ;; in order to initialize the table
      (let ((result (make-ast-table-literal src (table-fields src))))
        (enforce-next! #\})
        result)))

  ;; parameter-list -> [ parameter { ',' parameter } ]
  (define (parameter-list function-name)
    (let lp ((parameters '()))
      (case (token/type token)
        ((NAME)
         (let ((parameters (cons token parameters)))
           (advance!)
           (if (maybe-skip-next! #\,)
               (lp parameters)
               (values (reverse! parameters) #f))))
        ((#\))
         (values (reverse! parameters) #f))
        ((#:varargs)
         (advance!)
         (values (reverse! parameters) #t))
        (else
         (syntax-error
          (get-source-info)
          "expected either a name or ... in the parameter list of '~a', but got ~a"
          function-name token)))))

  ;; function-body -> '(' parameter-list ')' chunk END
  (define* (function-body #:optional (src (get-source-info)) (implicit-self? #f)
                          (name 'anonymous))
    ;; '('
    (enforce-next! #\()
    ;; parameter-list
    (receive (parameters variable-arguments?) (parameter-list name)
      (let* ((old-vararg-function *vararg-function*))
        (set! *vararg-function* variable-arguments?)
        (enforce-next! #\))
        ;; create function
        (enter-environment!)
        (when implicit-self?
          (environment-define! 'self 'parameter))
        (for-each (lambda (p) (environment-define! p 'parameter)) parameters)
        ;; chunk
        (let* ((body (chunk))
               (parameter-gensyms (map environment-lookup-gensym parameters))
               (result
                (make-ast-function
                 src (if (eq? name 'anonymous) #f name)
                 (if implicit-self?
                     (append parameters '(self))
                     parameters)
                 (if implicit-self?
                     (append parameter-gensyms
                             (list (environment-lookup-gensym 'self)))
                     parameter-gensyms)
                 variable-arguments?
                 (if (null? body) *void-literal* body))))
          (leave-environment!)
          ;; END
          (enforce-next! #:end)
          (set! *vararg-function* old-vararg-function)
          result))))

  ;; expression-list -> expression { ',' expression }
  (define (expression-list)
    (let loop ((tree (list (expression))))
      ;; { ',' expression }
      (if (maybe-skip-next! #\,)
          (loop (cons (expression) tree))
          ;; finished
          (reverse! tree))))

  ;; simple-expression -> (nil | true | false | NUMBER | STRING) | table-literal | FUNCTION function-body
  (define (simple-expression)
    (let ((src (get-source-info)))
      (case (token/type token)
        ;; (nil | true | false | NUMBER | STRING)
        ((#:nil) (advance! (make-ast-literal src #nil)))
        ((#:true) (advance! (make-ast-literal src #t)))
        ((#:false) (advance! (make-ast-literal src #f)))
        ((NUMBER STRING) (advance! (make-ast-literal src token)))
        ;; table-literal
        ((#\{) (table-literal))
        ;; ...
        ((#:varargs)
         (unless *vararg-function*
           (syntax-error src "cannot use '...' outside of a variable arguments function"))
         (advance! (make-ast-variable-arguments src)))
        ;; FUNCTION function-body
        ((#:function) (advance!) (function-body src))
        ;; primary-expression
        (else (primary-expression)))))

  ;; subexpression -> (simple-expression | unary-operator subexpression) { binary-operator subexpression }
  (define (subexpression limit)
    (let loop ((left
                ;; (simple-expression | unary-operator subexpression)
                (if (unary-operator? token)
                    ;; unary-operator subexpression
                    (let* ((src (get-source-info))
                           (operator token))
                      (advance!)
                      (make-ast-unary-operation
                       src operator (subexpression *unary-priority*)))
                    ;; simple-expression
                    ;; note: simple-expression may advance the current token
                    (simple-expression))))
      ;; { binary-operator subexpression }
      (if (and (binary-operator? token) (> (priority token) limit))
          (let* ((src (get-source-info))
                 (operator token))
            (advance!)
            (loop (make-ast-binary-operation
                   src operator left
                   ;; read next expression with higher priorities
                   (subexpression (priority operator)))))
          ;; finished
          left)))

  ;; expression -> subexpression
  (define (expression)
    (subexpression 0))

  ;; while-statement -> WHILE expression DO chunk END
  (define (while-statement)
    (let ((src (get-source-info)))
      ;; WHILE
      (advance!)
      ;; expression
      (let ((condition (expression)))
        ;; DO
        (enforce-next! #:do)
        ;; chunk
        (let ((body (chunk)))
          ;; END
          (enforce-next! #:end)
          (make-ast-while-loop src condition body)))))

  ;; return-statement -> RETURN expression-list
  (define (return-statement)
    (let ((src (get-source-info)))
      ;; RETURN
      (advance!)
      (make-ast-return src
                       (if (or (end-of-chunk? token) (eqv? token #\;))
                           *void-literal*
                           (expression-list)))))

  ;; FIXME: does a left-to-right assignment, so x, y = y, x probably
  ;; doesn't work. Also does not appear to handle the x, y = foo() case.
  ;;
  (define (parse-assignment src left right)
    ;; and then parses it, branching to handle overflows on either side if necessary
    (make-ast-sequence
     src
     (let loop ((left left)
                (right right)
                (tree '()))
       (cond
        ;; no overflows, and finished
        ((and (null? left) (null? right))
         (reverse! tree))
        ;; no overflows, not finished
        ((and (not (null? left)) (not (null? right)))
         (loop (cdr left)
               (cdr right)
               (cons (make-lua-assignment (car left) (car right)) tree)))
        ;; overflow on right, evaluate extra expressions on the right
        ((and (null? left) (not (null? right)))
         (reverse! (append! right tree)))
        ;; overflow on left, set all overflowed expressions to nil
        ((and (not (null? left)) (null? right))
         (let loop ((tree tree)
                    (rest left))
           (let* ((il (make-lua-assignment (car rest) *nil-literal*))
                  (rest (cdr rest)))
             (if (null? rest)
                 (reverse! (cons il tree))
                 (loop (cons il tree) (cdr rest))))))
        (else (error 'PARSE-ASSIGNMENT "should not happen"))))))

  ;; assignment -> '=' expression-list | ',' primary-expression assignment
  (define (assignment first)
    ;; assignments are unfortunately complicated because multiple variables may
    ;; be assigned to multiple expressions in a single assignment, and the
    ;; number of variables and expressions need not match

    ;; so this function accumulates the entire assignment
    (let* ((src (get-source-info))
           (left (let loop ((tree (list first)))
                   (if (eqv? token #\,)
                       (begin
                         (advance!)
                         (loop (cons (primary-expression) tree)))
                       (reverse! tree))))

           (right (begin
                    (enforce-next! #:=)
                    (expression-list))))
      (parse-assignment src left right)))

  ;; then-chunk -> (IF | ELSEIF) expression THEN chunk
  (define (then-chunk)
    ;; IF | ELSEIF
    (advance!)
    ;; expression
    (let* ((condition (expression)))
      ;; THEN
      (enforce-next! #:then)
      ;; chunk
      (values condition (chunk))))

  ;; if-statement -> then-chunk { then-chunk } [ELSE chunk] END
  (define (if-statement)
    (let ((src (get-source-info)))
      (receive (test then) (then-chunk)
        (let ((x (make-ast-condition
                  src test then
                  (let lp ()
                    (let ((src (get-source-info)))
                      (if (eq? token #:elseif)
                          (receive (test then) (then-chunk)
                            (make-ast-condition src test then (lp)))
                          (if (eq? token #:else)
                              (begin (advance!) (chunk))
                              *void-literal*)))))))
          (enforce-next! #:end)
          x))))

  ;; repeat-statement -> REPEAT chunk UNTIL expression
  (define (repeat-statement)
    (let ((src (get-source-info)))
      ;; REPEAT
      (advance!)
      ;; chunk
      (let ((body (chunk)))
        ;; UNTIL
        (enforce-next! #:until)
        ;; expression
        (let ((condition (expression)))
          (make-ast-while-loop
           src
           (make-ast-unary-operation src 'not condition)
           body)))))

  ;; function-statement -> FUNCTION NAME { field-selector } [ ':' NAME ] function-body
  (define (function-statement)
    (let* ((src (get-source-info))
           ;; FUNCTION NAME
           (name (begin (advance!) (single-name))))
      (receive (prefix type)
          (let lp ((last-expr (resolve-ref src name)))
            (if (eqv? token #\.)
                ;; { '.' NAME }
                (let ((name (begin (advance!) (single-name))))
                  (if (eq? token #\()
                      (values (cons name last-expr) 'table-function)
                      (lp (make-ast-table-ref src last-expr name))))
                ;; [ ':' NAME ]
                (if (eqv? token #\:)
                    (let ((name (begin (advance!) (single-name))))
                      (values (cons name last-expr) 'table-method))
                    (values last-expr 'function))))
        (let ((body (function-body src (eq? type 'table-method) name)))
          (case type
            ((table-function table-method)
             (make-ast-table-set
              src (cdr prefix)
              (make-ast-literal src (symbol->string (car prefix))) body))
            ((function)
             (make-lua-assignment prefix body))
            (else (error 'FUNCTION-STATEMENT "should not happen")))))))

  ;; local-statement -> LOCAL NAME { ',' NAME } [ '=' expression-list ]
  (define (local-statement)
    (let ((src (get-source-info)))
      ;; LOCAL
      ;; (already advanced by calling function)
      (let lp ((names '()))
        ;; NAME
        (assert-token-type 'NAME)
        (let ((names (advance! (cons token names))))
          (if (maybe-skip-next! #\,)
              ;; { ',' NAME }
              (lp names)
              (begin
                (for-each (lambda (n) (environment-define! n 'local)) names)
                (if (maybe-skip-next! #:=)
                    ;; [ '=' expression-list ]
                    (let ((left (map (lambda (x) (resolve-ref src x))
                                     (reverse! names))))
                      (parse-assignment src left (expression-list)))
                    ;; otherwise, it's not a declaration, not an
                    ;; assignment, and evaluates to nothing
                    *void-literal*)))))))

  (define (local-function-statement)
    (assert-token-type 'NAME)
    (let ((name token))
      (environment-define! name 'local)
      (advance!)
      (make-ast-local-set (get-source-info) name
                          (environment-lookup-gensym name)
                          (function-body))))

  ;; for-body
  (define (for-body)
    (enforce-next! #:do)
    (let ((body (chunk)))
      (enforce-next! #:end)
      body))

  ;; numeric-for -> FOR NAME '=' expression ',' expression ',' expression DO chunk END
  (define (numeric-for src name)
    (enforce-next! #:=)
    (enter-environment!)
    (environment-define! name 'local)
    (let ((initial (expression)))
      (enforce-next! #\,)
      (let* ((limit (expression))
             (step (if (maybe-skip-next! #\,)
                       (expression)
                       *default-for-step*))
             (result (make-ast-numeric-for-loop src name initial limit step
                                                (for-body))))
        (leave-environment!)
        result)))

  ;; list-for -> FOR NAME { ',' NAME } IN expression-list DO chunk END
  (define (list-for src name)
    (let ((names (let lp ((names (list name)))
                   (if (maybe-skip-next! #\,)
                       (lp (cons (single-name) names))
                       (reverse! names)))))
      (enforce-next! #:in)
      (let ((exps (expression-list)))
        (enforce-next! #:do)
        (for-each
         (lambda (name)
           (environment-define! name 'hidden))
         names)
        (let ((body (chunk)))
          (enforce-next! #:end)
          (make-ast-list-for-loop
           src names (map environment-lookup-gensym names) exps body)))))

  ;; for-statement -> FOR (numeric-for | list-for) END
  (define (for-statement)
    (let ((src get-source-info))
      (enforce-next! #:for)
      (let ((name (single-name)))
        (if (eq? token #:=)
            (numeric-for src name)
            (if (memv token '(#:in #\,))
                (list-for src name)
                (syntax-error src "expected = or in after for variable"))))))

  ;; break-statement -> BREAK
  (define (break-statement)
    (let ((src (get-source-info)))
      (enforce-next! #:break)
      (make-ast-break src)))

  ;; statement
  (define (statement)
    (case token
      ((#\;) (advance!) (statement))
      ;; statement -> return
      ((#:return) (values #t (return-statement)))
      ((#:break) (values #t (break-statement)))
      ((#:repeat) (values #f (repeat-statement)))
      ((#:while) (values #f (while-statement)))
      ((#:if) (values #f (if-statement)))
      ((#:function) (values #f (function-statement)))
      ((#:local) (advance!) (if (maybe-skip-next! #:function)
                                (values #f (local-function-statement))
                                (values #f (local-statement))))
      ((#:for) (values #f (for-statement)))
      ((#:do) (advance!) (let ((body (chunk)))
                           (enforce-next! #:end)
                           (values #f body)))
      ;; statement -> function | assignment
      (else (values #f (expression-statement)))))

  ;; chunk -> { statement [ ';' ] }
  (define (chunk)
    (let ((src (get-source-info)))
      (let loop ((is-last (end-of-chunk? token))
                 (tree '()))
        (if is-last
            (begin
              (maybe-skip-next! #\;)
              (wrap-expression-in-environment
               src
               environment
               (make-ast-sequence src (reverse! tree))))
            (receive (is-last node) (statement)
              (loop (or (end-of-chunk? token) is-last) (cons node tree)))))))

  ;; toplevel local environment
  (enter-environment!)
  ;; read first token
  (advance!)
  ;; return parser
  chunk)

(define (read-lua port)
  ((make-parser port)))
