(define-module (language cps)
  #:use-module (system base syntax) ;; for define-type
  #:use-module (ice-9 match)
  #:export (<letval> letval? make-letval letval-names letval-vals letval-body
            <const> const? make-const const-value
            <var> var? make-var var-value
            <toplevel-var> toplevel-var? make-toplevel-var toplevel-var-name
            <letrec> letrec? make-letrec letrec-names letrec-funcs letrec-body
            <letcont> letcont? make-letcont letcont-names
                      letcont-conts letcont-body
            <lambda> lambda? make-lambda lambda-names lambda-rest lambda-body
            <call> call? make-call call-proc call-cont call-args
            <primitive> primitive? make-primitive primitive-name
            <if> if? make-if if-test if-consequent if-alternate

            parse-cps unparse-cps))

;; The CPS representation used in this file is based on the paper
;; "Compiling with Continuations, Continued", by Andrew Kennedy.
;; Although it's called CPS, it's not really what you (or at least I)
;; would think of as "traditional" CPS, because all the functions are
;; declared via 'let...' forms. <letcont> distinguishes functions which
;; a) will never need a closure allocated and b) do not take their
;; continuations as arguments. Every new function produced by the
;; Scheme->CPS transformation has this property.

;; This representation has some useful properties:

;;  1) first, it's a runnable Scheme program (or close enough to
;;  Scheme). The CPS transformation applies to every Scheme program and
;;  preserves semantics.

;;  2) the let-based CPS is a representation of the dominator tree of
;;  the control flow graph of this program. in every <let___> block, the
;;  code in the body must be executed before the funcs or conts, and
;;  once control exits the body, it never goes back. basically, the let
;;  forms represent some subset of the control flow graph in two parts,
;;  and control only flows one direction between the parts.

;;  3) all of the values named in the CPS representation are immutable,
;;  so we can always substitute the definition of a name for that
;;  name. we handle immutable values by putting them inside box objects
;;  (as it happens, this is how we have to handle them in the VM, too,
;;  in the general case). see below for more info.

;; CPS Is Not About Continuations

;; Interestingly enough, we don't require that all continuations be
;; described by functions, even though that's the origin of CPS. the
;; reason is that we can't really convert all continuation captures to
;; function calls unless we can look inside every function (both Scheme
;; and C), see whether it captures its continuation, and rewrite it so
;; that it works with a function instead (or alternatively use a calling
;; convention where continuations are always reified, but that seems
;; terrible). we might be able to rewrite certain continuations or
;; delimited continuations as functions, but we can't assume we'll get
;; them all. so we really are using the continuations as a way to
;; represent control flow, and not as real continuations!

;; Mutable Variables

;; The handling of mutable variables is interesting. We would eventually
;; like to handle mutable variables and structs the same way - a
;; container object that holds some number of mutable slots, with a
;; mutable variable being the special case of holding only one
;; value. (Ideally we'd also model hash tables like that, but that's
;; ambitious.) Kennedy's paper handles struct-like objects by having
;; structure creation in the value part of a letval form, and
;; introducing a 'let' form to pull the values out. However, the rewrite
;; rules from his paper won't work if the structures are mutable,
;; because then you can't just substitute - you have to check the entire
;; control-flow graph up to that point to make sure the variable wasn't
;; modified. So instead of having another form, we just have a special
;; primitive function 'ref' that pulls the value out of a box, and a
;; special primitive 'set' that sets the values in boxes.

;; CPS and CPS-Data

;; The data structure is a combination of <cps> and <cps-data>
;; objects. The only reason to separate them is to be more clear about
;; what things can go where - <cps-data> objects can only appear as the
;; value part of a letval, and only <cps-data> objects can be there.

;; Naming Conventions

;; The things that would normally be thought of as "variables" in CPS
;; (i.e. the things that symbols refer to) are very different than the
;; "variable objects" that we use to represent mutable variables. To
;; keep things straight, we try to use "value" for the things that
;; symbols refer to, since they are constant values, and "variable" for
;; the variable objects, since they vary.

(define-type <cps>
  ;; <letval> values can be anything in the <cps-data> declaration
  ;; below. I think it's an open question whether we need letvals - we
  ;; could also imagine having some primitive functions that define
  ;; constants and variable objects, and then replace letvals with
  ;; letconts in which the body would have access to the variables or
  ;; constants.
  (<letval> names vals body)
  ;; Kennedy's paper calls this 'letfun', but 'letrec' is more standard
  ;; in Scheme
  (<letrec> names funcs body)
  ;; the important thing about continuations (as opposed to functions)
  ;; is that they can always be compiled as jumps. this is information
  ;; that was in the program itself, but would be lost if we compiled
  ;; everything to lambdas without distinguishing them in some
  ;; way. also, continuations can never be referenced, so we don't need
  ;; to worry about packaging them up.
  (<letcont> names conts body)
  ;; the 'lambda' form appears in the 'funcs' list of a letrec form, the
  ;; 'conts' list of a letcont form, and as the outermost form of a
  ;; compilation unit (when we're compiling a procedure at a time) to
  ;; distinguish procedure arguments from top-level variables. names is
  ;; a proper list of symbols, and rest is either #f or a single symbol
  ;; naming a rest argument.
  (<lambda> names rest body)
  ;; the 'call' form literally represents a call. the procedure will be
  ;; a variable bound by either a lambda form, a letval, a letrec, or a
  ;; letcont, or the special value 'return (which means to return from
  ;; the enclosing lambda). cont is the continuation that we pass to the
  ;; procedure. it's separate from the args because it can point to a
  ;; letcont continuation and they cannot, so it is different for
  ;; purposes of register allocation (and, of course, code
  ;; generation). the cont slot will be #f if proc is a letcont
  ;; continuation or 'return.
  (<call> proc cont args)
  ;; the 'primitive' form represents a primitive procedure. it will
  ;; probably appear in the 'proc' field of a <call> record, so maybe we
  ;; should have a merged 'primcall' record like Tree-IL does, but it
  ;; could also appear in a <letval> values list. the name of a
  ;; primitive is a symbol.
  (<primitive> name)
  ;; the 'if' form is like a Scheme 'if', except that the test must be a
  ;; lexical variable, and the consequent and alternate must be names of
  ;; continuations. the if will jump to whichever continuation is
  ;; appropriate. in the future, I'd like to make 'if a primitive
  ;; procedure and not a special form. that requires having a way for
  ;; primitive procedures to be inlined, but otherwise might be all
  ;; right.
  (<if> test consequent alternate)  
  ;; we don't have the 'let' form from Kennedy's paper. see the comments
  ;; about mutable variables above for the reason.
  )

(define-type <cps-data>
  ;; const represents constants.
  (<const> value)
  ;; var is for lexical variables. these things map to variable objects
  ;; in the VM. value is the value it is initialized to. it should be a
  ;; CPS value (which is a symbol).
  (<var> value)
  ;; toplevel vars are like pseudo-vars. instead of actually creating a
  ;; variable object, we'll just remember that there *is* a variable
  ;; object already in existence and look it up when we need it. we
  ;; remember the name of the variable so that we can look it up.
  (<toplevel-var> name))

(define (parse-cps tree)
  (match tree
    (('letval names vals body)
     (make-letval names
                  (map parse-cps vals)
                  (parse-cps body)))
    (('const value)
     (make-const value))
    (('var value)
     (make-var value))
    (('toplevel-var name)
     (make-toplevel-var name))
    (('letrec names funcs body)
     (make-letrec names
                  (map parse-cps funcs)
                  (parse-cps body)))
    (('letcont names conts body)
     (make-letcont names
                   (map parse-cps conts)
                   (parse-cps body)))
    (('lambda names rest body)
     (make-lambda names rest (parse-cps body)))
    (('call ('primitive prim) cont args)
     (make-call (make-primitive prim) cont args))
    (('call proc cont args)
     (make-call proc cont args))
    (('primitive name)
     (make-primitive name))
    (('if test consequent alternate)
     (make-if test consequent alternate))
    (_ (error "couldn't parse CPS" tree))))

(define (unparse-cps cps)
  (match cps
    (($ <letval> names vals body)
     (list 'letval names vals (unparse-cps body)))
    (($ <const> value)
     (list 'const value))
    (($ <var> value)
     (list 'var value))
    (($ <toplevel-var> name)
     (list 'toplevel-var name))
    (($ <letrec> names funcs body)
     (list 'letrec names
           (map unparse-cps funcs)
           (unparse-cps body)))
    (($ <letcont> names conts body)
     (list 'letcont names
           (map unparse-cps conts)
           (unparse-cps body)))
    (($ <lambda> names rest body)
     (list 'lambda names rest (unparse-cps body)))
    (($ <call> ($ <primitive> prim) cont args)
     (list 'call (list 'primitive prim) cont args))
    (($ <call> proc cont args)
     (list 'call proc cont args))
    (($ <primitive> name)
     (list 'primitive name))
    (($ <if> test consequent alternate)
     (list 'if test consequent alternate))
    (_ (error "couldn't unparse CPS" cps))))
