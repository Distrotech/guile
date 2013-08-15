;;; Continuation-passing style (CPS) intermediate language (IL)

;; Copyright (C) 2013 Free Software Foundation, Inc.

;;;; This library is free software; you can redistribute it and/or
;;;; modify it under the terms of the GNU Lesser General Public
;;;; License as published by the Free Software Foundation; either
;;;; version 3 of the License, or (at your option) any later version.
;;;;
;;;; This library is distributed in the hope that it will be useful,
;;;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;;;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;;;; Lesser General Public License for more details.
;;;;
;;;; You should have received a copy of the GNU Lesser General Public
;;;; License along with this library; if not, write to the Free Software
;;;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA

;;; Commentary:
;;;
;;;
;;; Code:

(define-module (language tree-il compile-cps)
  #:use-module (ice-9 match)
  #:use-module ((srfi srfi-1) #:select (fold filter-map))
  #:use-module (srfi srfi-26)
  #:use-module ((system foreign) #:select (make-pointer pointer->scm))
  #:use-module (language cps)
  #:use-module (language tree-il analyze)
  #:use-module (language tree-il optimize)
  #:use-module ((language tree-il)
                #:select
                (<void>
                 <const> <primitive-ref> <lexical-ref> <lexical-set>
                 <module-ref> <module-set>
                 <toplevel-ref> <toplevel-set> <toplevel-define>
                 <conditional>
                 <call> <primcall>
                 <seq>
                 <lambda> <lambda-case>
                 <let> <letrec> <fix> <let-values>
                 <prompt> <abort>
                 make-conditional make-const
                 tree-il-src
                 tree-il-fold))
  #:export (compile-cps))

;; Helpers.
(define-inlinable (make-$let1k cont body)
  (make-$letk (list cont) body))
(define-inlinable (make-$let1v src k name sym cont-body body)
  (make-$let1k (make-$cont src k (make-$kargs (list name) (list sym) cont-body))
               body))
(define-inlinable (make-$let1c src name sym val cont-body)
  (let ((k (gensym "kconst")))
    (make-$let1v src k name sym cont-body (make-$continue k (make-$const val)))))
(define-inlinable (make-$letk* conts body)
  (match conts
    (() body)
    ((cont . conts)
     (make-$let1k cont (make-$letk* conts body)))))
(define-inlinable (make-let src val-proc body-proc)
  (let ((k (gensym "k")) (sym (gensym "v")))
    (make-$let1v src k 'tmp sym (body-proc sym) (val-proc k))))

(define *branching-primitives*
  '(null? nil? pair? struct? char? eq? eqv? equal? < <= = >= >))

(define (branching-primitive? name)
  (memq name *branching-primitives*))

;; Guile's semantics are that a toplevel lambda captures a reference on
;; the current module, and that all contained lambdas use that module to
;; resolve toplevel variables.  This parameter tracks whether or not we
;; are in a toplevel lambda.  If we are in a lambda, the parameter is
;; bound to a fresh name identifying the module that was current when
;; the toplevel lambda is defined.
;;
;; This is more complicated than it need be.  Ideally we should resolve
;; all toplevel bindings to bindings from specific modules, unless the
;; binding is unbound.  This is always valid if the compilation unit
;; sets the module explicitly, as when compiling a module, but it
;; doesn't work for files auto-compiled for use with `load'.
;;
(define current-topbox-scope (make-parameter #f))

(define (toplevel-box src name bound? val-proc)
  (let ((name-sym (gensym "name"))
        (bound?-sym (gensym "bound?")))
    (make-$let1c
     src 'name name-sym name
     (make-$let1c
      src 'bound? bound?-sym bound?
      (make-let
       src
       (lambda (k)
         (match (current-topbox-scope)
           (#f
            (make-$continue k (make-$primcall
                               'resolve
                               (list name-sym bound?-sym))))
           (scope
            (let ((scope-sym (gensym "scope")))
              (make-$let1c
               src 'scope scope-sym scope
               (make-$continue k (make-$primcall
                               'cached-toplevel-box
                               (list scope-sym name-sym bound?-sym))))))))
       val-proc)))))

(define (module-box src module name public? bound? val-proc)
  (let ((module-sym (gensym "module"))
        (name-sym (gensym "name"))
        (public?-sym (gensym "public?"))
        (bound?-sym (gensym "bound?")))
    (make-$let1c
      src 'module module-sym module
      (make-$let1c
       src 'name name-sym name
       (make-$let1c
        src 'public? public?-sym public?
        (make-$let1c
         src 'bound? bound?-sym bound?
         (make-let
          src
          (lambda (k)
            (make-$continue k (make-$primcall
                            'cached-module-box
                            (list module-sym name-sym public?-sym bound?-sym))))
          val-proc)))))))

(define (capture-toplevel-scope src scope k)
  (let ((module (gensym "module"))
        (scope-sym (gensym "scope"))
        (kmodule (gensym "kmodule")))
    (make-$let1c
     src 'scope scope-sym scope
     (make-$let1v
      src kmodule 'module module
      (make-$continue
       k
       (make-$primcall 'cache-current-module! (list module scope-sym)))
      (make-$continue kmodule (make-$primcall 'current-module '()))))))

(define (fold-formals proc seed arity gensyms inits)
  (match arity
    (($ $arity req opt rest kw allow-other-keys?)
     (let ()
       (define (fold-req names gensyms seed)
         (match names
           (() (fold-opt opt gensyms inits seed))
           ((name . names)
            (proc name (car gensyms) #f
                  (fold-req names (cdr gensyms) seed)))))
       (define (fold-opt names gensyms inits seed)
         (match names
           (() (fold-rest rest gensyms inits seed))
           ((name . names)
            (proc name (car gensyms) (car inits)
                  (fold-opt names (cdr gensyms) (cdr inits) seed)))))
       (define (fold-rest rest gensyms inits seed)
         (match rest
           (#f (fold-kw kw gensyms inits seed))
           (name (proc name (car gensyms) #f
                       (fold-kw kw (cdr gensyms) inits seed)))))
       (define (fold-kw kw gensyms inits seed)
         (match kw
           (()
            (unless (null? gensyms)
              (error "too many gensyms"))
            (unless (null? inits)
              (error "too many inits"))
            seed)
           (((key name var) . kw)
            (unless (eq? var (car gensyms))
              (error "unexpected keyword arg order"))
            (proc name var (car inits)
                  (fold-kw kw (cdr gensyms) (cdr inits) seed)))))
       (fold-req req gensyms seed)))))

(define (unbound? src sym kt kf)
  (define tc8-iflag 4)
  (define unbound-val 9)
  (define unbound-bits (logior (ash unbound-val 8) tc8-iflag))
  (let ((unbound-sym (gensym "unbound"))
        (ktest (gensym "ktest")))
    (make-$let1c
     src 'unbound unbound-sym (pointer->scm (make-pointer unbound-bits))
     (make-$let1k
      (make-$cont src ktest (make-$kif kt kf))
      (make-$continue ktest (make-$primcall 'eq? (list sym unbound-sym)))))))

(define (init-default-value name sym subst init body)
  (match (assq-ref subst sym)
    ((subst-sym box?)
     (let ((knext (gensym "knext"))
           (kbound (gensym "kbound"))
           (kunbound (gensym "kunbound"))
           (src (tree-il-src init)))
       (define (maybe-box k make-body)
         (if box?
             (let ((kbox (gensym "kbox"))
                   (phi (gensym "phi")))
               (make-$let1k
                (make-$cont src kbox
                            (make-$kargs (list name) (list phi)
                                         (make-$continue
                                          k
                                          (make-$primcall 'box (list phi)))))
                (make-body kbox)))
             (make-body k)))
       (make-$let1k
        (make-$cont src knext (make-$kargs (list name) (list subst-sym) body))
        (maybe-box
         knext
         (lambda (k)
           (make-$letk*
            (list
             (make-$cont src kbound
                         (make-$kargs '() '() (make-$continue k (make-$var sym))))
             (make-$cont src kunbound
                         (make-$kargs '() '() (convert init k subst))))
            (unbound? src sym kunbound kbound)))))))))

;; exp k-name alist -> term
(define (convert exp k subst)
  ;; exp (v-name -> term) -> term
  (define (convert-arg exp k)
    (match exp
      (($ <lexical-ref> src name sym)
       (match (assq-ref subst sym)
         ((box #t)
          (make-let src
                    (lambda (k)
                      (make-$continue k (make-$primcall 'box-ref (list box))))
                    k))
         ((subst #f) (k subst))
         (#f (k sym))))
      (else (make-let (tree-il-src exp)
                      (cut convert exp <> subst)
                      k))))
  ;; (exp ...) ((v-name ...) -> term) -> term
  (define (convert-args exps k)
    (match exps
      (() (k '()))
      ((exp . exps)
       (convert-arg exp
                    (lambda (name)
                      (convert-args exps
                                    (lambda (names)
                                      (k (cons name names)))))))))
  (define (box-bound-var name sym body)
    (match (assq-ref subst sym)
      ((box #t)
       (let ((k (gensym "k")))
         (make-$let1v #f k name box body
                      (make-$continue k (make-$primcall 'box (list sym))))))
      (else body)))

  (match exp
    (($ <lexical-ref> src name sym)
     (match (assq-ref subst sym)
       ((box #t)
        (make-$continue k (make-$primcall 'box-ref (list box))))
       ((subst #f) (make-$continue k (make-$var subst)))
       (#f (make-$continue k (make-$var sym)))))
    (($ <void> src) (make-$continue k (make-$void)))
    (($ <const> src exp) (make-$continue k (make-$const exp)))
    (($ <primitive-ref> src name) (make-$continue k (make-$prim name)))
    (($ <lambda> src meta body)
     ;; FIXME: propagate src to kentry
     (if (current-topbox-scope)
         (make-$continue k (make-$fun meta (gensym "self") '()
                                      (convert body 'ktail subst)))
         (let ((scope (gensym "scope"))
               (kscope (gensym "kscope")))
           (make-$let1k
            (make-$cont src kscope
                     (make-$kargs '() '() 
                                  (parameterize ((current-topbox-scope scope))
                                    (convert exp k subst))))
            (capture-toplevel-scope src scope kscope)))))

    (($ <module-ref> src mod name public?)
     (module-box
      src mod name public? #t
      (lambda (box)
        (make-$continue k (make-$primcall 'box-ref (list box))))))
    (($ <module-set> src mod name public? exp)
     (convert-arg
      exp
      (lambda (val)
        (module-box
         src mod name public? #f
         (lambda (box)
           (make-$continue k (make-$primcall 'box-set! (list box val))))))))
    (($ <toplevel-ref> src name)
     (toplevel-box
      src name #t
      (lambda (box)
        (make-$continue k (make-$primcall 'box-ref (list box))))))
    (($ <toplevel-set> src name exp)
     (convert-arg
      exp
      (lambda (val)
        (toplevel-box
         src name #f
         (lambda (box)
           (make-$continue k (make-$primcall 'box-set! (list box val))))))))
    (($ <toplevel-define> src name exp)
     (make-let src
               (lambda (k) (make-$continue k (make-$const name)))
               (lambda (name)
                 (convert-arg
                  exp
                  (lambda (val)
                    (make-$continue k (make-$primcall 'define! (list name val))))))))

    (($ <call> src proc args)
     (convert-args (cons proc args)
                   (match-lambda
                    ((proc . args) (make-$continue k (make-$call proc args))))))

    (($ <primcall> src name args)
     (if (branching-primitive? name)
         (convert (make-conditional src exp (make-const #f #t)
                                    (make-const #f #f))
                  k subst)
         (convert-args args
                       (lambda (args)
                         (make-$continue k (make-$primcall name args))))))

    ;; Prompts with inline handlers.
    (($ <prompt> src escape-only? tag body
        ($ <lambda> hsrc hmeta
           ($ <lambda-case> _ hreq #f hrest #f () hsyms hbody #f)))
     ;; Handler:
     ;;   khargs: check args returned to handler, -> khbody
     ;;   khbody: the handler, -> k
     ;;
     ;; Post-body:
     ;;   krest: collect return vals from body to list, -> kpop
     ;;   kpop: pop the prompt, -> kprim
     ;;   kprim: load the values primitive, -> kret
     ;;   kret: (apply values rvals), -> k
     ;;
     ;; Escape prompts evaluate the body with the continuation of krest.
     ;; Otherwise we do a no-inline call to body, continuing to krest.
     (convert-arg
      tag
      (lambda (tag)
        (let ((khargs (gensym "khargs"))
              (khbody (gensym "khbody")))
          (make-$let1k
           (let ((hnames (append hreq (if hrest (list hrest) '()))))
             (make-$cont hsrc khbody
                         (make-$kargs hnames hsyms
                                      (fold box-bound-var
                                            (convert hbody k subst)
                                            hnames hsyms))))
           (make-$let1k
            (make-$cont hsrc khargs
                        (make-$ktrunc (make-$arity hreq '() hrest '() #f)
                                      khbody))
            (cond
             (escape-only?
              (let ((kret (gensym "kret"))
                    (kprim (gensym "kvalues"))
                    (prim (gensym "values"))
                    (kpop (gensym "kpop"))
                    (krest (gensym "krest"))
                    (vals (gensym "vals")))
                (make-$letk*
                 (list
                  (make-$cont
                   src kpop
                   (make-$kargs
                    (list 'rest) (list vals)
                    (make-$let1k
                     (make-$cont
                      src kret
                      (make-$kargs
                       '() '()
                       (make-$let1k
                        (make-$cont
                         src kprim
                         (make-$kargs
                          (list 'prim) (list prim)
                          (make-$continue
                           k
                           (make-$primcall 'apply (list prim vals)))))
                        (make-$continue kprim (make-$prim 'values)))))
                     (make-$continue kret (make-$primcall 'pop-prompt '())))))
                  (make-$cont src krest
                              (make-$ktrunc (make-$arity '() '() 'rest '() #f)
                                            kpop)))
                 (let ((kbody (gensym "kbody")))
                   (if escape-only?
                       (make-$let1k
                        (make-$cont (tree-il-src body) kbody
                                    (convert body krest subst))
                        (make-$continue kbody (make-$prompt #t tag khargs)))
                       (convert-arg
                        body
                        (lambda (body)
                          (make-$let1k
                           (make-$cont
                            (tree-il-src body) kbody
                            (make-$continue
                             krest
                             (make-$primcall 'call-thunk/no-inline (list body))))
                           (make-$continue
                            kbody
                            (make-$prompt #f tag khargs)))))))))))))))))

    ;; Eta-convert prompts without inline handlers.
    (($ <prompt> src escape-only? tag body handler)
     (convert-args
      (list tag body handler)
      (lambda (args)
        (make-$continue k (make-$primcall 'call-with-prompt args)))))

    (($ <abort> src tag args tail)
     (convert-args (append (list tag) args (list tail))
                   (lambda (args*)
                     (make-$continue k (make-$primcall 'abort args*)))))

    (($ <conditional> src test consequent alternate)
     (let ((kif (gensym "kif"))
           (kt (gensym "k"))
           (kf (gensym "k")))
       (make-$letk*
        (list (make-$cont (tree-il-src consequent) kt
                          (make-$kargs '() '() (convert consequent k subst)))
              (make-$cont (tree-il-src alternate) kf
                          (make-$kargs '() '() (convert alternate k subst))))
        (make-$let1k
         (make-$cont src kif (make-$kif kt kf))
         (match test
           (($ <primcall> src (? branching-primitive? name) args)
            (convert-args args
                          (lambda (args)
                            (make-$continue kif (make-$primcall name args)))))
           (_ (convert-arg test
                           (lambda (test)
                             (make-$continue kif (make-$var test))))))))))

    (($ <lexical-set> src name gensym exp)
     (convert-arg
      exp
      (lambda (exp)
        (match (assq-ref subst gensym)
          ((box #t)
           (make-$continue k (make-$primcall 'box-set! (list box exp))))))))

    (($ <lambda-case> src req opt rest kw inits gensyms body alternate)
     (let ((arity (make-$arity req (or opt '()) rest
                               (if kw (cdr kw) '()) (and kw (car kw)))))
       (make-$cont
        src (gensym "kentry")
        (make-$kentry
         arity
         (make-$cont
          src (gensym "kcase")
          (make-$kargs
           (fold-formals (lambda (name sym init names)
                           (cons name names))
                         '()
                         arity gensyms inits)
           gensyms
           (fold-formals (lambda (name sym init body)
                           (if init
                               (init-default-value name sym subst init body)
                               (box-bound-var name sym body)))
                         (convert body k subst)
                         arity gensyms inits)))
         (and alternate (convert alternate k subst))))))

    (($ <seq> src head tail)
     (let ((ktrunc (gensym "ktrunc"))
           (kseq (gensym "kseq")))
       (make-$letk* (list (make-$cont (tree-il-src tail) kseq
                                   (make-$kargs '() '()
                                                (convert tail k subst)))
                          (make-$cont src ktrunc
                                   (make-$ktrunc (make-$arity '() '() #f '() #f)
                                                 kseq)))
                    (convert head ktrunc subst))))

    (($ <let> src names syms vals body)
     (let lp ((names names) (syms syms) (vals vals))
       (match (list names syms vals)
         ((() () ()) (convert body k subst))
         (((name . names) (sym . syms) (val . vals))
          (let ((klet (gensym "k")))
            (make-$let1v src klet name sym
                         (box-bound-var name sym (lp names syms vals))
                         (convert val klet subst)))))))

    (($ <fix> src names gensyms (($ <lambda> lsrc lmeta lbody) ...) body)
     ;; Some letrecs can be contified; that happens later.
     (make-$letrec names gensyms
                   (map (lambda (src meta body)
                          ;; FIXME: propagate src to kentry
                          (make-$fun meta (gensym "self") '()
                                     (convert body 'ktail subst)))
                        lsrc lmeta lbody)
                   (convert body k subst)))

    (($ <let-values> src exp
        ($ <lambda-case> lsrc req () rest #f () syms body #f))
     (let* ((ktrunc (gensym "ktrunc"))
            (kargs (gensym "kargs"))
            (names (append req (if rest (list rest) '())))
            (arity (make-$arity req '() rest '() #f)))
       (make-$letk* (list (make-$cont src kargs
                                   (make-$kargs names syms
                                                (fold box-bound-var
                                                      (convert body k subst)
                                                      names syms)))
                          (make-$cont src ktrunc
                                   (make-$ktrunc arity kargs)))
                    (convert exp ktrunc subst))))))

(define (build-subst exp)
  "Compute a mapping from lexical gensyms to substituted gensyms.  The
usual reason to replace one variable by another is assignment
conversion.  Default argument values is the other reason.

Returns a list of (ORIG-SYM SUBST-SYM BOXED?).  A true value for BOXED?
indicates that the replacement variable is in a box."
  (define (box-set-vars exp subst)
    (match exp
      (($ <lexical-set> src name sym exp)
       (if (assq sym subst)
           subst
           (cons (list sym (gensym "b") #t) subst)))
      (_ subst)))
  (define (default-args exp subst)
    (match exp
      (($ <lambda-case> src req opt rest kw inits gensyms body alternate)
       (fold-formals (lambda (name sym init subst)
                       (if init
                           (let ((box? (match (assq-ref subst sym)
                                         ((box #t) #t)
                                         (#f #f)))
                                 (subst-sym (gensym (symbol->string name))))
                             (cons (list sym subst-sym box?) subst))
                           subst))
                     subst
                     (make-$arity req (or opt '()) rest
                                  (if kw (cdr kw) '()) (and kw (car kw)))
                     gensyms
                     inits))
      (_ subst)))
  (tree-il-fold box-set-vars default-args '() exp))

(define (cps-convert exp)
  (convert exp 'ktail (build-subst exp)))

(define (cps-convert/thunk exp)
  (make-$fun '() (gensym "init") '()
             (make-$cont
              (tree-il-src exp)
              (gensym "kentry")
              (make-$kentry (make-$arity '() '() #f '() #f)
                            (make-$cont
                             (tree-il-src exp)
                             (gensym "kinit")
                             (make-$kargs '() '()
                                          (cps-convert exp)))
                            #f))))

(define *comp-module* (make-fluid))

(define %warning-passes
  `((unused-variable     . ,unused-variable-analysis)
    (unused-toplevel     . ,unused-toplevel-analysis)
    (unbound-variable    . ,unbound-variable-analysis)
    (arity-mismatch      . ,arity-analysis)
    (format              . ,format-analysis)))

(define (optimize-tree-il x e opts)
  (define warnings
    (or (and=> (memq #:warnings opts) cadr)
        '()))

  ;; Go through the warning passes.
  (let ((analyses (filter-map (lambda (kind)
                                (assoc-ref %warning-passes kind))
                              warnings)))
    (analyze-tree analyses x e))

  (optimize x e opts))

(define (compile-cps exp env opts)
  (values (cps-convert/thunk (optimize-tree-il exp env opts))
          env
          env))
