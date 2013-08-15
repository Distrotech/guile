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
  #:use-module (language cps primitives)
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

;; (put 'build-cps 'scheme-indent-function 0)
;; (put 'build-cps* 'scheme-indent-function 1)
;; (put '$letk 'scheme-indent-function 1)
;; (put '$letk* 'scheme-indent-function 1)
;; (put '$letconst 'scheme-indent-function 1)
;; (put '$continue 'scheme-indent-function 1)
;; (put '$kargs 'scheme-indent-function 2)
;; (put 'convert-arg 'scheme-indent-function 1)
;; (put 'convert-args 'scheme-indent-function 1)

(define-syntax build-cont
  (syntax-rules (unquote $kif $ktrunc $kargs)
    ((_ (unquote exp))
     exp)
    ((_ ($kif kt kf))
     (make-$kif kt kf))
    ((_ ($ktrunc req rest kargs))
     (make-$ktrunc (make-$arity req '() rest '() #f) kargs))
    ((_ ($kargs (name ...) (sym ...) body))
     (make-$kargs (list name ...) (list sym ...) (build-cps body)))
    ((_ ($kargs names syms body))
     (make-$kargs names syms (build-cps body)))))

(define-syntax build-cont-decl
  (syntax-rules (unquote)
    ((_ (unquote exp)) exp)
    ((_ (k src cont)) (make-$cont src k (build-cont cont)))))

(define-syntax build-arity
  (syntax-rules (unquote)
    ((_ (unquote exp)) exp)
    ((_ (req opt rest kw allow-other-keys?))
     (make-$arity req opt rest kw allow-other-keys?))))

(define-syntax build-fun-entry
  (syntax-rules (unquote)
    ((_ (unquote exp)) exp)
    ((_ ($kentry k src arity cont-decl))
     (make-$cont src k (make-$kentry (build-arity arity)
                                     (build-cont-decl cont-decl))))))

(define-syntax build-fun
  (syntax-rules (unquote)
    ((_ ($fun meta self free (unquote body)))
     (make-$fun meta self free body))
    ((_ ($fun meta self free (entry ...)))
     (make-$fun meta self free (list (build-fun-entry entry) ...)))))

(define-syntax build-call
  (syntax-rules (unquote
                 $var $void $const $prim $fun $call $primcall $values $prompt)
    ((_ (unquote exp)) exp)
    ((_ ($var sym)) (make-$var sym))
    ((_ ($void)) (make-$void))
    ((_ ($const val)) (make-$const val))
    ((_ ($prim name)) (make-$prim name))
    ((_ ($fun . args)) (build-fun ($fun . args)))
    ((_ ($call proc (arg ...))) (make-$call proc (list arg ...)))
    ((_ ($call proc args)) (make-$call proc args))
    ((_ ($primcall name (arg ...))) (make-$primcall name (list arg ...)))
    ((_ ($primcall name args)) (make-$primcall name args))
    ((_ ($values (arg ...))) (make-$values (list arg ...)))
    ((_ ($values args)) (make-$values args))
    ((_ ($prompt escape? tag handler)) (make-$prompt escape? tag handler))))

(define-syntax build-cps
  (syntax-rules (unquote $letk $letk* $letconst $letrec $continue)
    ((_ (unquote exp))
     exp)
    ((_ ($letk (cont-decl ...) body))
     (make-$letk (list (build-cont-decl cont-decl) ...)
                 (build-cps body)))
    ((_ ($letk* () body))
     (build-cps body))
    ((_ ($letk* (cont-decl cont-decls ...) body))
     (build-cps ($letk (cont-decl) ($letk* (cont-decls ...) body))))
    ((_ ($letconst () body))
     (build-cps body))
    ((_ ($letconst ((name sym val) tail ...) body))
     (build-cps* (kconst)
       ($letk ((kconst #f ($kargs (name) (sym) ($letconst (tail ...) body))))
         ($continue kconst ($const val)))))
    ((_ ($letrec names gensyms funs body))
     (make-$letrec names gensyms funs (build-cps body)))
    ((_ ($continue k exp)) (make-$continue k (build-call exp)))))

(define-syntax build-cps*
  (syntax-rules ()
    ((_ (sym ...) form)
     (let ((sym (gensym (symbol->string 'sym))) ...)
      (build-cps form)))))

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
  (build-cps* (name-sym bound?-sym kbox box)
    ($letconst (('name name-sym name)
                ('bound? bound?-sym bound?))
      ($letk ((kbox src ($kargs ('box) (box) ,(val-proc box))))
        ,(match (current-topbox-scope)
           (#f
            (build-cps
              ($continue kbox
                ($primcall 'resolve
                           (name-sym bound?-sym)))))
           (scope
            (build-cps* (scope-sym)
              ($letconst (('scope scope-sym scope))
                ($continue kbox
                  ($primcall 'cached-toplevel-box
                             (scope-sym name-sym bound?-sym)))))))))))

(define (module-box src module name public? bound? val-proc)
  (build-cps* (module-sym name-sym public?-sym bound?-sym kbox box)
    ($letconst (('module module-sym module)
                ('name name-sym name)
                ('public? public?-sym public?)
                ('bound? bound?-sym bound?))
      ($letk ((kbox src ($kargs ('box) (box) ,(val-proc box))))
        ($continue kbox
          ($primcall 'cached-module-box
                     (module-sym name-sym public?-sym bound?-sym)))))))

(define (capture-toplevel-scope src scope k)
  (build-cps* (module scope-sym kmodule)
    ($letconst (('scope scope-sym scope))
      ($letk ((kmodule src ($kargs ('module) (module)
                             ($continue k
                               ($primcall 'cache-current-module!
                                          (module scope-sym))))))
        ($continue kmodule
          ($primcall 'current-module ()))))))

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
  (build-cps* (unbound ktest)
    ($letconst (('unbound unbound (pointer->scm (make-pointer unbound-bits))))
      ($letk ((ktest src ($kif kt kf)))
        ($continue ktest
          ($primcall 'eq? (sym unbound)))))))

(define (init-default-value name sym subst init body)
  (match (assq-ref subst sym)
    ((subst-sym box?)
     (let ((src (tree-il-src init)))
       (define (maybe-box k make-body)
         (if box?
             (build-cps* (kbox phi)
               ($letk ((kbox src ($kargs (name) (phi)
                                   ($continue k ($primcall 'box (phi))))))
                 ,(make-body kbox)))
             (make-body k)))
       (build-cps* (knext kbound kunbound)
         ($letk ((knext src ($kargs (name) (subst-sym) ,body)))
           ,(maybe-box
             knext
             (lambda (k)
               (build-cps
                 ($letk ((kbound src ($kargs () () ($continue k ($var sym))))
                         (kunbound src ($kargs () () ,(convert init k subst))))
                   ,(unbound? src sym kunbound kbound)))))))))))

;; exp k-name alist -> term
(define (convert exp k subst)
  ;; exp (v-name -> term) -> term
  (define (convert-arg exp k)
    (match exp
      (($ <lexical-ref> src name sym)
       (match (assq-ref subst sym)
         ((box #t)
          (build-cps* (kunboxed unboxed)
            ($letk ((kunboxed src ($kargs ('unboxed) (unboxed) ,(k unboxed))))
              ($continue kunboxed ($primcall 'box-ref (box))))))
         ((subst #f) (k subst))
         (#f (k sym))))
      (else
       (let ((src (tree-il-src exp)))
         (build-cps* (karg arg)
           ($letk ((karg src ($kargs ('arg) (arg) ,(k arg))))
             ,(convert exp karg subst)))))))
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
       (build-cps* (k)
         ($letk ((k #f ($kargs (name) (sym) ,body)))
           ($continue k ($primcall 'box (sym))))))
      (else body)))

  (match exp
    (($ <lexical-ref> src name sym)
     (match (assq-ref subst sym)
       ((box #t) (build-cps ($continue k ($primcall 'box-ref (box)))))
       ((subst #f) (build-cps ($continue k ($var subst))))
       (#f (build-cps ($continue k ($var sym))))))

    (($ <void> src)
     (build-cps ($continue k ($void))))

    (($ <const> src exp)
     (build-cps ($continue k ($const exp))))

    (($ <primitive-ref> src name)
     (build-cps ($continue k ($prim name))))

    (($ <lambda> src meta body)
     ;; FIXME: add src field to fun, add tail field also
     (let ()
       (define (convert-entries body)
         (match body
           (($ <lambda-case> src req opt rest kw inits gensyms body alternate)
            (let* ((arity (make-$arity req (or opt '()) rest
                                       (if kw (cdr kw) '()) (and kw (car kw))))
                   (names (fold-formals (lambda (name sym init names)
                                          (cons name names))
                                        '()
                                        arity gensyms inits)))
              (cons
               (build-cps* (kentry kargs)
                 ,(build-fun-entry
                   ($kentry
                    kentry src ,arity
                    (kargs
                     src
                     ($kargs names gensyms
                       ,(fold-formals
                         (lambda (name sym init body)
                           (if init
                               (init-default-value name sym subst init body)
                               (box-bound-var name sym body)))
                         (convert body 'ktail subst)
                         arity gensyms inits))))))
               (if alternate (convert-entries alternate) '()))))))
       (if (current-topbox-scope)
           (build-cps* (self)
             ($continue k
               ($fun meta self '() ,(convert-entries body))))
           (build-cps* (scope kscope)
             ($letk ((kscope src ($kargs () ()
                                   ,(parameterize ((current-topbox-scope scope))
                                      (convert exp k subst)))))
               ,(capture-toplevel-scope src scope kscope))))))

    (($ <module-ref> src mod name public?)
     (module-box
      src mod name public? #t
      (lambda (box)
        (build-cps ($continue k ($primcall 'box-ref (box)))))))

    (($ <module-set> src mod name public? exp)
     (convert-arg exp
       (lambda (val)
         (module-box
          src mod name public? #f
          (lambda (box)
            (build-cps ($continue k ($primcall 'box-set! (box val)))))))))

    (($ <toplevel-ref> src name)
     (toplevel-box
      src name #t
      (lambda (box)
        (build-cps ($continue k ($primcall 'box-ref (box)))))))

    (($ <toplevel-set> src name exp)
     (convert-arg exp
       (lambda (val)
         (toplevel-box
          src name #f
          (lambda (box)
            (build-cps ($continue k ($primcall 'box-set! (box val)))))))))

    (($ <toplevel-define> src name exp)
     (convert-arg exp
       (lambda (val)
         (build-cps* (kname name-sym)
           ($letconst (('name name-sym name))
             ($continue k ($primcall 'define! (name-sym val))))))))

    (($ <call> src proc args)
     (convert-args (cons proc args)
       (match-lambda
        ((proc . args)
         (build-cps ($continue k ($call proc args)))))))

    (($ <primcall> src name args)
     (if (branching-primitive? name)
         (convert (make-conditional src exp (make-const #f #t)
                                    (make-const #f #f))
                  k subst)
         (convert-args args
           (lambda (args)
             (build-cps ($continue k ($primcall name args)))))))

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
        (let ((hnames (append hreq (if hrest (list hrest) '()))))
          (build-cps* (khargs khbody kret kprim prim kpop krest vals kbody)
            ($letk* ((khbody hsrc ($kargs hnames hsyms
                                    ,(fold box-bound-var
                                           (convert hbody k subst)
                                           hnames hsyms)))
                     (khargs hsrc ($ktrunc hreq hrest khbody))
                     (kpop src
                           ($kargs ('rest) (vals)
                             ($letk ((kret
                                      src
                                      ($kargs () ()
                                        ($letk ((kprim
                                                 src
                                                 ($kargs ('prim) (prim)
                                                   ($continue k
                                                     ($primcall 'apply
                                                                (prim vals))))))
                                          ($continue kprim
                                            ($prim 'values))))))
                               ($continue kret
                                 ($primcall 'pop-prompt ())))))
                     (krest src ($ktrunc '() 'rest kpop)))
              ,(if escape-only?
                   (build-cps
                     ($letk ((kbody (tree-il-src body) 
                                    ($kargs () ()
                                      ,(convert body krest subst))))
                       ($continue kbody ($prompt #t tag khargs))))
                   (convert-arg body
                     (lambda (thunk)
                       (build-cps
                         ($letk ((kbody (tree-il-src body) 
                                        ($kargs () ()
                                          ($continue krest
                                            ($primcall 'call-thunk/no-inline
                                                       (thunk))))))
                           ($continue kbody
                             ($prompt #f tag khargs)))))))))))))

    ;; Eta-convert prompts without inline handlers.
    (($ <prompt> src escape-only? tag body handler)
     (convert-args
      (list tag body handler)
      (lambda (args)
        (build-cps
          ($continue k ($primcall 'call-with-prompt args))))))

    (($ <abort> src tag args tail)
     (convert-args (append (list tag) args (list tail))
                   (lambda (args*)
                     (build-cps ($continue k ($primcall 'abort args*))))))

    (($ <conditional> src test consequent alternate)
     (build-cps* (kif kt kf)
       ($letk* ((kt (tree-il-src consequent) ($kargs () ()
                                               ,(convert consequent k subst)))
                (kf (tree-il-src alternate) ($kargs () ()
                                              ,(convert alternate k subst)))
                (kif src ($kif kt kf)))
         ,(match test
            (($ <primcall> src (? branching-primitive? name) args)
             (convert-args args
               (lambda (args)
                 (build-cps ($continue kif ($primcall name args))))))
            (_ (convert-arg test
                 (lambda (test)
                   (build-cps ($continue kif ($var test))))))))))

    (($ <lexical-set> src name gensym exp)
     (convert-arg
      exp
      (lambda (exp)
        (match (assq-ref subst gensym)
          ((box #t)
           (build-cps
             ($continue k ($primcall 'box-set! (box exp)))))))))

    (($ <seq> src head tail)
     (build-cps* (ktrunc kseq)
       ($letk* ((kseq (tree-il-src tail) ($kargs () ()
                                           ,(convert tail k subst)))
                (ktrunc src ($ktrunc '() #f kseq)))
         ,(convert head ktrunc subst))))

    (($ <let> src names syms vals body)
     (let lp ((names names) (syms syms) (vals vals))
       (match (list names syms vals)
         ((() () ()) (convert body k subst))
         (((name . names) (sym . syms) (val . vals))
          (build-cps* (klet)
            ($letk ((klet src ($kargs (name) (sym)
                                ,(box-bound-var name sym
                                                (lp names syms vals)))))
              ,(convert val klet subst)))))))

    (($ <fix> src names gensyms funs body)
     ;; Some letrecs can be contified; that happens later.
     (if (current-topbox-scope)
         (build-cps* (self)
           ($letrec names
                    gensyms
                    (map (lambda (fun)
                           (match (convert fun k subst)
                             (($ $continue _ (and fun ($ $fun)))
                              fun)))
                         funs)
                    ,(convert body k subst)))
         (build-cps* (scope kscope)
           ($letk ((kscope src ($kargs () ()
                                 ,(parameterize ((current-topbox-scope scope))
                                    (convert exp k subst)))))
             ,(capture-toplevel-scope src scope kscope)))))

    (($ <let-values> src exp
        ($ <lambda-case> lsrc req () rest #f () syms body #f))
     (let ((names (append req (if rest (list rest) '()))))
       (build-cps* (ktrunc kargs)
         ($letk* ((kargs src ($kargs names syms
                               ,(fold box-bound-var
                                      (convert body k subst)
                                      names syms)))
                  (ktrunc src ($ktrunc req rest kargs)))
           ,(convert exp ktrunc subst)))))))

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
  (let ((src (tree-il-src exp)))
    (build-cps* (init kentry kinit)
      ,(build-fun
        ($fun '() init '()
              (($kentry kentry src ('() '() #f '() #f)
                        (kinit src ($kargs () ()
                                     ,(cps-convert exp))))))))))

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
