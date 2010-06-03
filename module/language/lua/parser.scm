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
          (datum->syntax template-id (string->symbol (apply string-append (map (lambda (x) (if (string? x) x (symbol->string (syntax->datum x)))) rest)))))
        (syntax-case stx ()
          ((_ name field ...)
           (with-syntax
               ((constructor (id #'name "make-" #'name))
                (predicate (id #'name #'name "?"))
               ((setter ...)
                (map (lambda (x) (id #'name #'name "-" x "!")) #'(field ...)))
               ((getter ...)
                (map (lambda (x) (id #'name #'name "-" x)) #'(field ...))))

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
          (datum->syntax template-id (string->symbol (apply string-append (map (lambda (x) (if (string? x) x (symbol->string (syntax->datum x)))) rest)))))

        (syntax-case stx ()
          ((_ "aux" name field ...)
           #`(define-record #,(id #'name "ast-" #'name) #,(id #'name "src") field ...))

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
  (or (or-eqv? token #:else #:elseif #:end #:until) (eof-object? token)))

(define (token/type t)
  (cond ((number? t) 'NUMBER)
        ((eof-object? t) 'EOS)
        ((symbol? t) 'NAME)
        ((string? t) 'STRING)
        (else
         (case t
           ((#\. #\( #\) #\, #\- #\< #\; #\+ #\{ #\} #\[ #\] #\: #\#
#:function #:end #:if #:return #:elseif #:then #:else #:true #:false
#:nil #:== #:~= #:= #\> #:>= #:<= #:local #:dots #:break #:do #:in) t)
           (else (error 'TOKEN/TYPE t))))))

;; infix operator parsing
(define (binary-operator? t)
  "Return #t if the token may be a binary operator"
  (or-eqv? t #\+ #\* #\/ #\- #\^ #\< #\> #:== #:~= #:and #:or #:concat))

(define (unary-operator? t)
  "Return #t if the token may be a unary operator"
  (or-eqv? t #\- #\# #:not))

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
  (cond ((ast-global-ref? left)
         (make-ast-global-set (ast-global-ref-src left) (ast-global-ref-name left) right))
        ((ast-local-ref? left)
         (make-ast-local-set (ast-local-ref-src left) (ast-local-ref-name left) (ast-local-ref-gensym left) right))
        ((ast-table-ref? left)
         (make-ast-table-set (ast-table-ref-src left) (ast-table-ref-table left) (ast-table-ref-key left) right))
        (else
         (error 'MAKE-LUA-ASSIGNMENT "should not happen"))))

(define (wrap-expression-in-environment src e x)
  "Wrap an expression in an enclosing lexical environment if necessary"
  (let* ((bindings (map cdr (environment-bindings e)))
         (locals (filter-map (lambda (b) (if (eq? (binding-type b) 'local) b #f)) bindings)))
    (if (null? locals)
        x
        (make-ast-local-block src (map binding-name locals) (map binding-gensym locals) (map (lambda (c) *nil-literal*) locals) x))))

;;;;; PARSER

(define (make-parser port)
  ;; Variables that will be set to the results of MAKE-LEXER.
  (define-lua-lexer get-source-info lexer)

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
        (environment-bindings! environment (alist-cons name
                                                    (make-binding
                                                     name
                                                     (gensym (string-append " " (symbol->string name)))
                                                     type)
                                                    (environment-bindings environment)))))

  ;; Environment lookup procedures -- these fail silently and return #f,
  ;; because Lua allows global variables to be referenced without being
  ;; predefined

  (define (environment-lookup-aux name . e)
    "Given a variable's NAME, look up its binding."
    (set! e (if (null? e) environment (car e )))
    (if e
        (let ((binding (assq-ref (environment-bindings e) name)))
          (if binding
              binding
              (environment-lookup-aux name (environment-parent e))))
        #f))

  (define (environment-lookup-gensym name)
    "Given a variable's NAME, look up its gensym"
    (define binding (environment-lookup-aux name))
    (if binding
        (binding-gensym binding)
        #f))

  (define (environment-lookup-type name)
    "Given a variable's NAME, look up its global"
    (define binding (environment-lookup-aux name))
    (if binding
        (binding-type binding)
        #f))

  (define (resolve-ref src name)
    "Determine whether a variable reference is global or local"
    (let* ((binding (environment-lookup-gensym name)))
      (if binding
          (make-ast-local-ref src name binding)
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
      ((_ x) (begin (advance-aux) x))
      ((_) (advance-aux))))

  (define (assert-token-type type)
    "Throw an error if the current token does not have the expected type"
    (if (not (equal? (token/type token) type))
        (syntax-error (get-source-info) "expected ~a" type)))

  (define (maybe-skip-next! c)
    "Skip a token"
    (if (equal? token c)
        (advance! #t)
        #f))

  (define (enforce-next! expect)
    "Throw an error if the current token is not the expected token"
    (unless (maybe-skip-next! expect)
      (syntax-error (get-source-info) "expected '~A' but got '~A'" expect token)))

  ;;;;; GRAMMAR

  ;; single-name -> NAME
  (define (single-name . return-src?)
    (define save token)
    (define src (get-source-info))
    (assert-token-type 'NAME)
    (advance!)
    (if (not (null? return-src?))
        (values src save)
        save))

  ;; single-variable -> single-name
  (define (single-variable)
    (receive (src save)
             (single-name #:return-src #t)
             (resolve-ref src save)))

  ;; application-arguments -> '(' [ expression-list ] ')' | STRING | TABLE
  (define (application-arguments)
    (cond ((eq? (token/type token) 'STRING)
           (let* ((string token))
             (advance!)
             (list (make-ast-literal #f string))))
          ((eq? token #\{)
           ;; TODO: table constructor
           ;; '('
           (list (table-literal)))
          ((eq? token #\()
           (advance!)
           (if (eq? token #\))
               ;; ')'
               (advance! '())
               ;; [ expression-list ]
               (let* ((arguments (expression-list)))
                 ;; ')'
                 (enforce-next! #\))
                 arguments)))
           (else (error 'APPLICATION-ARGUMENTS "should not happen"))))

  ;; prefix-expression -> NAME | '(' expression ')'
  (define (prefix-expression)
    (cond
      ;; NAME
      ((eq? (token/type token) 'NAME) (single-variable))
      ;; '('
      ((eq? token #\()
       (begin
         (advance!)
         ;; expression
         (let* ((save (expression)))
           ;; ')'
           (enforce-next! #\))
           ;; finished
           save)))
      (else (syntax-error (get-source-info) "unexpected symbol ~a" token))))

  ;; index -> '[' expression ']'
  (define (index)
    (enforce-next! #\[)
    (let* ((indice (expression)))
      (enforce-next! #\])
      indice))

  ;; field-selector -> '.' NAME
  (define (field-selector src prefix)
    (make-ast-table-ref src prefix (make-ast-literal src (symbol->string (single-name)))))

  ;; primary-expression -> prefix-expression { field-selector [ application-arguments ] | index | application-arguments }
  (define (primary-expression)
    (define src (get-source-info))
    ;; prefix-expression
    (define prefix (prefix-expression))
    (let lp ((expr prefix))
      (case (token/type token)
          ;; field-selector
          ((#\.) (advance!) (lp (field-selector src expr)))
          ;; index
          ((#\[)
           (let* ((indice (index)))
             (lp (make-ast-table-ref src expr indice))))
          ;; ':' NAME application-arguments
          ((#\:)
           (advance!)
           (assert-token-type 'NAME)
           (let* ((name (single-name)))
             (lp
              (make-ast-function-call src
              (make-ast-table-ref src expr (make-ast-literal src (symbol->string name)))
              (cons expr (application-arguments))))))
          ;; application-arguments
          ((#\( STRING #\{)
           (lp (make-ast-function-call src expr (application-arguments))))
          (else expr))))

  ;; expression-statement -> function | assignment
  (define (expression-statement)
    (define primary (primary-expression))
    (if (ast-function-call? primary)
        primary
        (assignment primary)))


  ;; record-field -> (NAME | index) '=' expression
  (define (record-field)
    (let* ((indice
            (cond
              ;; NAME
              ((eq? (token/type token) 'NAME)
               (let ((tmp (make-ast-literal #f (symbol->string token))))
                 (advance!)
                 tmp))
              ;; index
              (else (index))))
           (value
            (begin
              ;; '='
              (enforce-next! #:=)
              ;; expression
              (expression))))
      (values indice value)))

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
    (if (eq? token #\})
        '()
        (let loop ((implicit-indice 1)
                   (tree '()))
          (if (eq? token #\})
              (reverse! tree)
              (receive
               (indice expr)
               (field)
               ;; field-separator
               (maybe-skip-next! #\,)
               (maybe-skip-next! #\;)

               (loop
                (if (not indice) (+ implicit-indice 1) implicit-indice)
                (cons
                 (cons (or indice (make-ast-literal src implicit-indice)) expr)
                 tree)))))))

  ;; table-literal -> '{' table-fields '}'
  (define (table-literal)
    (define src (get-source-info))
    ;; '{'
    (enforce-next! #\{)
    ;; bind the table to a temporary variable with LET as it's needed in order to initialize the table
    (let* ((result (make-ast-table-literal src (table-fields src))))
      result
      (enforce-next! #\})
      result))

  ;; parameter-list -> [ parameter { ',' parameter } ]
  (define (parameter-list function-name)
    (if (eq? token #\))
        (values '() #f)
        (let lp ((parameters '()))
          ;; parameter
          (let* ((parameters
                  (if (eq? (token/type token) 'NAME)
                      (append! parameters (list token))
                      (if (eq? token #:dots)
                          (values parameters #f)
                          (syntax-error (get-source-info) "expected either a name or ... in the parameter list of '~a', but got ~a" function-name token))))
                 (last-token token))
            (advance!)
            (if (eq? token #\,)
                (if (eq? last-token #:dots)
                    (syntax-error (get-source-info) "expected ')' after ... in the parameter list of '~a'" function-name)
                    (advance! (lp parameters)))
                (values parameters (eq? last-token #:dots)))))))

  ;; function-body -> '(' parameter-list ')' chunk END
  (define* (function-body #:optional (src (get-source-info)) (implicit-self? #f) (name 'anonymous))
    ;; '('
    (enforce-next! #\()
    ;; parameter-list
    (receive (parameters variable-arguments?)
             (parameter-list name)
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
                       (make-ast-function src (if (eq? name 'anonymous) #f name)
                                          (if implicit-self? (append parameters '(self)) parameters)
                                          (if implicit-self? (append parameter-gensyms (list (environment-lookup-gensym 'self))) parameter-gensyms)
                                          variable-arguments? (if (null? body) *void-literal* body))))
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
    (define src (get-source-info))
    (receive
     (advance? result)
     (case (token/type token)
       ;; (nil | true | false | NUMBER | STRING)
       ((#:true #:false #:nil NUMBER STRING)
        (values
          #t
          (make-ast-literal
           src
           (cond ((eq? token #:true) #t)
                 ((eq? token #:false) #f)
                 ((eq? token #:nil) #nil)
                 (else token)))))
       ;; table-literal
       ((#\{) (values #f (table-literal)))
       ;; ...
       ((#:dots)
        (unless *vararg-function*
          (syntax-error src "cannot use '...' outside of a variable arguments function"))
        (values #t (make-ast-variable-arguments src)))
       ;; FUNCTION function-body
       ((#:function) (advance!) (values #f (function-body src)))
       ;; primary-expression
       (else (values #f (primary-expression))))
     (if advance?
         (advance!))
     result))

  ;; subexpression -> (simple-expression | unary-operator subexpression) { binary-operator subexpression }
  (define (subexpression limit)
    (define left)
    ;; test for preceding unary operator
    (set! left
      ;; (simple-expression | unary-operator subexpression)
      (if (unary-operator? token)
          ;; unary-operator subexpression
          (let* ((src (get-source-info))
                 (operator token))
            (advance!)
            (make-ast-unary-operation src operator (subexpression *unary-priority*)))
          ;; simple-expression
          ;; note: simple-expression may advance the current token
          (simple-expression)))

    (let loop ((left left))
      ;; { binary-operator subexpression }
      (if (and (binary-operator? token) (> (priority token) limit))
          (let* ((src (get-source-info))
                 (operator token))
            (advance!)
            ;; read next expression with higher priorities
            (let* ((right (subexpression (priority operator))))
              (loop (make-ast-binary-operation src operator left right))))
          ;; finished
          left)))

  ;; expression -> subexpression
  (define (expression)
    (subexpression 0))

  ;; while-statement -> WHILE expression DO chunk END
  (define (while-statement)
    (define src (get-source-info))
    ;; WHILE
    (advance!)
    ;; expression
    (let* ((condition (expression)))
      ;; DO
      (enforce-next! #:do)
      ;; chunk
      (let* ((body (chunk)))
        ;; END
        (enforce-next! #:end)
        (make-ast-while-loop src condition body))))

  ;; return-statement -> RETURN expression-list
  (define (return-statement)
    (define src (get-source-info))

    ;; RETURN
    (advance!)

    (make-ast-return src (if (or (end-of-chunk? token) (eq? token #\;))
                         *void-literal*
                         (expression-list))))

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
           (left (let loop ((x first)
                            (tree '()))
                   (set! tree (cons x tree))
                   (if (eq? token #\,)
                       (advance! (loop (primary-expression) tree))
                       (reverse! tree))))

           (right (begin
                    (enforce-next! #:=)
                    (expression-list))))
      (parse-assignment src left right)

      ) ; let*
    ) ; assignment

  ;; then-chunk -> (IF | ELSEIF) expression THEN chunk
  (define (then-chunk)
    ;; IF | ELSEIF
    (advance!)
    ;; expression
    (let* ((condition (expression)))
      ;; THEN
      (enforce-next! #:then)
      ;; chunk
      (let* ((body (chunk)))
        (values condition body))))

  ;; if-statement -> then-chunk { then-chunk } [ELSE chunk] END
  (define (if-statement)
    (define if-src (get-source-info))
    (define x
      (receive (test then)
               (then-chunk)
               (make-ast-condition
                if-src test then
                (let lp ()
                  (define src (get-source-info))
                  (if (eq? token #:elseif)
                      (receive (test then)
                               (then-chunk)
                               (make-ast-condition src test then (lp)))
                      (if (eq? token #:else)
                          (advance! (chunk))
                          *void-literal*))))))
    (enforce-next! #:end)
    x)

  ;; repeat-statement -> REPEAT chunk UNTIL expression
  (define (repeat-statement)
    (define src (get-source-info))
    ;; REPEAT
    (advance!)
    ;; chunk
    (let* ((body (chunk)))
      ;; UNTIL
      (enforce-next! #:until)
      ;; expression
      (let* ((condition (expression)))
        (make-ast-while-loop
         src
         (make-ast-unary-operation src 'not condition)
         body))))

  ;; function-statement -> FUNCTION NAME { field-selector } [ ':' NAME ] function-body
  (define (function-statement)
    (define src (get-source-info))
    ;; FUNCTION NAME
    (define name (advance! (single-name)))

    (receive (prefix type)
             (let lp ((last-expr (resolve-ref src name)))
               (if (eq? token #\.)
                   ;; { '.' NAME }
                   (let* ((name (advance! (single-name))))
                     (if (eq? token #\()
                           (values (cons name last-expr) 'table-function)
                           (lp (make-ast-table-ref src last-expr name))))
                   ;; [ ':' NAME ]
                   (if (eq? token #\:)
                       (let* ((name (advance! (single-name))))
                         (values (cons name last-expr) 'table-method))
                       (values last-expr 'function))))
             (define body (function-body src (eq? type 'table-method) name))
             (case type
               ((table-function table-method)
                (make-ast-table-set src (cdr prefix) (make-ast-literal src (symbol->string (car prefix))) body))
               ((function) (make-lua-assignment prefix body))
               (else (error 'FUNCTION-STATEMENT "should not happen")))))

  ;; local-statement -> LOCAL NAME { ',' NAME } [ '=' expression-list ]
  (define (local-statement)
    (define src (get-source-info))
    ;; LOCAL
    ;; (already advanced by calling function)

    (let lp ((names '()))
      ;; NAME
      (assert-token-type 'NAME)
      (set! names (cons token names))
      (advance!)
      (if (maybe-skip-next! #\,)
          ;; { ',' NAME }
          (lp names)
          (begin
            (for-each (lambda (n) (environment-define! n 'local)) names)
            (if (maybe-skip-next! #:=)
                ;; [ '=' expression-list ]
                (let* ((left (map (lambda (x) (resolve-ref src x)) names))
                       (right (expression-list)))
                  (parse-assignment src left (reverse! right)))
                ;; otherwise, it's not a declaration, not an assignment, and evaluates to nothing
                *void-literal*)))))

  (define (local-function-statement)
    (assert-token-type 'NAME)
    (let* ((name token))
      (environment-define! name 'local)
      (advance!)
      (make-ast-local-set (get-source-info) name (environment-lookup-gensym name) (function-body))))

  ;; for-body
  (define (for-body)
    (enforce-next! #:do)
    (let* ((body (chunk)))
      (enforce-next! #:end)
      body))

  ;; numeric-for -> FOR NAME '=' expression ',' expression ',' expression DO chunk END
  (define (numeric-for src name)
    (define step *default-for-step*)
    (advance!)
    (enforce-next! #:=)
    (enter-environment!)
    (environment-define! name 'local)
    (let* ((initial (expression)))
      (enforce-next! #\,)
      (let* ((limit (expression)))
        (when (eq? token #\,)
          (advance!)
          (set! step (expression)))
        (let* ((result (make-ast-numeric-for-loop src name initial limit step (for-body))))
          (leave-environment!)
          result))))

  ;; list-for -> FOR NAME { ',' NAME } IN expression-list DO chunk END
  (define (list-for src name)
    (let* ((names
            (let lp ((names (list name)))
              (advance!)
              (if (eq? token #\,)
                  (begin
                    (advance!)
                    (assert-token-type 'NAME)
                    (lp (cons token names)))
                  (reverse! names)))))
      (enforce-next! #:in)
      (let* ((exps (expression-list)))
        (enforce-next! #:do)
        (for-each
         (lambda (name)
           (environment-define! name 'hidden))
         names)
        (let* ((body (chunk)))
          (enforce-next! #:end)
          (make-ast-list-for-loop src names (map environment-lookup-gensym names) exps body)))))

  ;; for-statement -> FOR (numeric-for | list-for) END
  (define (for-statement)
    (define src (get-source-info))
    (enforce-next! #:for)
    (assert-token-type 'NAME)
    (let* ((name token)
           (result
            (begin
              (lookahead!)
              (if (eq? token2 #:=)
                  (numeric-for src name)
                  (if (or-eqv? token2 #:in #\,)
                      (list-for src name)
                      (syntax-error src "expected = or in after for variable"))))))
      result))

  ;; break-statement -> BREAK
  (define (break-statement)
    (enforce-next! #:break)
    (make-ast-break (get-source-info)))

  ;; statement
  (define (statement)
    (case token
      ((#\;) (advance!) (statement))
      ;; statement -> return
      ((#:return #:break)
       (values
         #t
         (case token
           ((#:return) (return-statement))
           ((#:break) (break-statement)))))
      ((#:if #:function #:do #:while #:repeat #:local #:for)
       (values
         #f
          (case token
            ((#:repeat) (repeat-statement))
            ((#:while) (while-statement))
            ((#:if) (if-statement))
            ((#:function) (function-statement))
            ((#:local)
             (advance!)
             (if (maybe-skip-next! #:function)
                 (local-function-statement)
                 (local-statement)))
            ((#:for) (for-statement))
            ((#:do)
             (begin
               (advance!)
               (let* ((body (chunk)))
                 (enforce-next! #:end)
                 body))))))
      ;; statement -> function | assignment
      (else (values #f (expression-statement)))))

  ;; chunk -> { statement [ ';' ] }
  (define (chunk)
    (define src (get-source-info))
    (let loop ((is-last (end-of-chunk? token))
               (tree '()))
      (if is-last
          (begin
            (maybe-skip-next! #\;)
            (wrap-expression-in-environment
             src
             environment
             (make-ast-sequence src (reverse! tree))))
        (receive
         (is-last node)
         (statement)
         (loop (or (end-of-chunk? token) is-last) (cons node tree))))))

  (initialize-lua-lexer! port get-source-info lexer)

  ;; toplevel local environment
  (enter-environment!)
  ;; read first token
  (advance!)
  ;; return parser
  chunk)

(define (read-lua port)
  (define parser (make-parser port))
  (parser))
