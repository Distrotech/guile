
(define-module (ice-9 debugging new)
  #:use-module (ice-9 debugging traps)
  #:use-module (ice-9 gds-client)
  #:export-syntax (trace break))

(define (advised proc before values-handler)
  (lambda args
    (before args)
    (call-with-values
	(lambda ()
	  (apply proc args))
      values-handler)))

(define-syntax trace
  (syntax-rules ()
    ((trace proc)
     (let ((old-proc proc))
       (set! proc (advised proc
			   (lambda (args)
			     (display ";TRACE: ")
			     (display 'proc)
			     (display " ")
			     (write args)
			     (newline))
			   (lambda results
			     (for-each (lambda (result)
					 (display ";TRACE: ")
					 (display 'proc)
					 (display " => ")
					 (write result)
					 (newline))
				       results)
			     (apply values results))))))))

(define-syntax break
  (syntax-rules ()
    ((break proc)
     (let ((old-proc proc))
       (set! proc (advised proc
			   (lambda (args)
			     (display ";BREAK: ")
			     (display 'proc)
			     (display " ")
			     (write args)
			     (newline)
			     (gds-debug-trap
			      (throw->trap-context 'breakpoint '())))
			   values))))))

;; (define-macro (trace proc)
;;   `(let ((proc ,proc))
;;      (set! ,proc
;; 	   (lambda args
;; 	     (display ";TRACE: ")
;; 	     (display ',proc)
;; 	     (display " ")
;; 	     (write args)
;; 	     (newline)
;; 	     (call-with-values
;; 		 (lambda ()
;; 		   (apply proc args))
;; 	       (lambda results
;; 		 (for-each (lambda (result)
;; 			     (display ";TRACE: ")
;; 			     (display ',proc)
;; 			     (display " => ")
;; 			     (write result)
;; 			     (newline))
;; 			   results)
;; 		 (apply values results)))))))
;; 
;; (define-macro (break proc)
;;   `(let ((proc ,proc))
;;      (set! ,proc
;; 	   (lambda args
;; 	     (display ";TRACE: ")
;; 	     (display ',proc)
;; 	     (display " ")
;; 	     (write args)
;; 	     (newline)
;; 	     (call-with-values
;; 		 (lambda ()
;; 		   (apply proc args))
;; 	       (lambda results
;; 		 (for-each (lambda (result)
;; 			     (display ";TRACE: ")
;; 			     (display ',proc)
;; 			     (display " => ")
;; 			     (write result)
;; 			     (newline))
;; 			   results)
;; 		 (apply values results)))))))
