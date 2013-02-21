(define-module (language cps allocate)
  #:use-module (language cps)
  #:use-module (system base syntax) ; for record-case
  #:use-module (srfi srfi-1)
  #:use-module (ice-9 receive)
  #:use-module (language cps annotate)
  #:export (allocate-registers-and-labels
            show-regs show-labels))

;; This function walks some CPS and allocates registers and labels for
;; it. It's certainly not optimal yet.
(define (allocate-registers-and-labels cps)
  ;; we associate a register number with every CPS value (which will
  ;; always be a symbol)
  (define register (make-object-property))

  ;; when we make a call, we need to know where to put the new stack
  ;; frame. this holds that information.
  (define call-frame-start (make-object-property))

  ;; when we have a continuation that can accept any number of values,
  ;; it needs to know where to put them on the stack. this holds that
  ;; information. TO DO: could this be combined with the previous
  ;; property?
  (define rest-args-start (make-object-property))

  ;; this holds the number of registers needed by every 'lambda' form, so we
  ;; can allocate them with the reserve-locals or
  ;; assert-nargs-ee/nlocals instructions.
  (define nlocals (make-object-property))

  ;; and every contination gets a label, so we can jump to it. this is
  ;; indexed by the names of the continuations, not the actual lambda
  ;; objects.
  (define label (make-object-property))

  (define next-label!
    (let ((label-counter 0))
      (lambda ()
        (let ((label
               (string->symbol
                (string-append
                 "l-" (number->string label-counter)))))
          (set! label-counter (+ label-counter 1))
          label))))

  ;; visit walks the CPS
  (define (visit cps counter)
    ;; counter is the number of registers we've already allocated.
    (record-case cps
      ;; call is kind of a weird case, because although it doesn't need
      ;; any extra registers, the new frame needs to be on top of the
      ;; stack. so we save the end of the stack in its own property.
      ((<call>)
       (set! (call-frame-start cps) counter)
       counter)

      ((<lambda> names rest body)
       ;; we can't actually handle continuations with any number of
       ;; values (except in some special cases), because we wouldn't be
       ;; able to allocate registers for an subsequent instructions
       ;; without knowing how many registers this will use. so if we get
       ;; a rest arg, we remember where the top of the stack is and then
       ;; emit either a bind-rest or drop-values instruction.
       (let* ((after-names
               ;; assign register numbers to each name
               (fold (lambda (name counter)
                       (set! (register name) counter)
                       (1+ counter))
                     counter names))
              (total
               (visit body after-names)))
         (when rest
               (set! (rest-args-start rest) total)
               (set! total (+ total 1)))
         ;; we reserve one more than whatever number of values we have
         ;; because we might need an extra space to move values
         ;; around. see generate-shuffle. this doesn't really feel
         ;; elegant, but I don't have a better solution right now.
         (set! (nlocals cps) (+ total 1))))
      
      ((<letval> names vals body)
       ;; allocate the registers
       (let ((counter
              (fold
               (lambda (name counter)
                 (set! (register name) counter)
                 (1+ counter))
               counter names)))

         ;; and visit the body of the letval
         (visit body counter)))
      
      ;; an important scoping point: none of the arguments to any of the
      ;; <letcont>'s continuations are in scope for any of the other
      ;; continuations, or the body. therefore, we allocate registers
      ;; for them independently. (TO DO: if we have a bunch of
      ;; continuations that are going to call each other recursively, we
      ;; should try to set up our allocation to avoid unnecessary
      ;; moves.)
      ((<letcont> names conts body)
       ;; allocate labels for the continuations
       (map (lambda (n)
              (set! (label n) (next-label!)))
            names)
       ;; then allocate registers for all of the continuations and the
       ;; body. we need to return the maximum of the register numbers
       ;; used so that whatever procedure we're part of will allocate
       ;; the right number of registers.
       (apply max (visit body counter)
              (map (lambda (c) (visit c counter)) conts)))
      
      ;; in a letrec, unlike a letcont, we do have to allocate registers
      ;; to hold the actual functions, because they could be used as
      ;; values instead of just as static jump targets. but they can
      ;; also reference each other, so we should allocate labels for
      ;; them too.
      ((<letrec> names funcs body)
       ;; allocate labels for the functions
       (map
        (lambda (name)
          (set! (label name) (next-label!)))
        names)

       ;; allocate registers *within* the functions
       (map (lambda (f) (visit f 0)) funcs)

       ;; and allocate registers for the functions and the body
       (let ((total
              (fold
               (lambda (name counter)
                 (set! (register name) counter)
                 (1+ counter))
               0 names)))
         (visit body counter)
         counter))
      
      ;; an if has no interesting content, so we don't need to do
      ;; anything here.
      ((<if> test consequent alternate)
       counter)))

  (visit cps 0)

  (values register
          call-frame-start
          rest-args-start
          nlocals
          label
          next-label!))

(define (show-regs cps)
  (receive (register call-frame-start rest-args-start
            nlocals label next-label!)
    (allocate-registers-and-labels cps)
    (annotate-cps cps register)))

(define (show-labels cps)
  (receive (register call-frame-start rest-args-start
            nlocals label next-label!)
    (allocate-registers-and-labels cps)
    (annotate-cps cps label)))
