;;; r7rs-libraries.scm --- Support for the R7RS `define-library' form

;;      Copyright (C) 2013 Free Software Foundation, Inc.
;;
;; This library is free software; you can redistribute it and/or
;; modify it under the terms of the GNU Lesser General Public
;; License as published by the Free Software Foundation; either
;; version 3 of the License, or (at your option) any later version.
;;
;; This library is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; Lesser General Public License for more details.
;;
;; You should have received a copy of the GNU Lesser General Public
;; License along with this library; if not, write to the Free Software
;; Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA


;; This file is included from boot-9.scm and assumes the existence of
;; (and expands into) procedures and syntactic forms defined therein.

(define-syntax define-library
  (lambda (form)
    (syntax-case form ()
      ((_ (module-name ...) (decl-type . decl-args) ...)
       (and-map (lambda (x)
                  (or (identifier? x)
                      (exact-integer? (syntax->datum x))))  ; XXX FIXME handle exact integers properly
                #'(module-name ...))
       (let loop ((decls #'((decl-type . decl-args) ...))
                  (imports '())
                  (exports '())
                  (bodies '()))
         (if (null? decls)
             #`(library (module-name ...)
                 (export #,@(reverse exports))
                 (import #,@(reverse imports))
                 #,@(reverse bodies))
             (let ((decl (car decls)))
               (define (splice-in xs)
                 (loop (append xs (cdr decls)) imports exports bodies))
               (define (new-imports specs)
                 (loop (cdr decls) (append (reverse specs) imports) exports bodies))
               (define (new-exports specs)
                 (loop (cdr decls) imports (append (reverse specs) exports) bodies))
               (define (new-bodies xs)
                 (loop (cdr decls) imports exports (append (reverse xs) bodies)))
               (syntax-case decl (export
                                  import
                                  begin
                                  include
                                  include-ci
                                  include-library-declarations
                                  cond-expand)
                 ((export spec ...)
                  (let ()
                    (define (convert-spec spec)
                      (syntax-case spec (rename)
                        ((rename id1 id2)
                         (and (identifier? #'id1)
                              (identifier? #'id2))
                         #'(rename (id1 id2)))
                        (id
                         (identifier? #'id)
                         #'id)
                        (_ (syntax-violation 'export "invalid export spec"
                                             decl spec))))
                    (new-exports (map convert-spec #'(spec ...)))))
                 ((import set ...)
                  (new-imports #'(set ...)))
                 ((begin cmd-or-defn ...)
                  (new-bodies #'(cmd-or-defn ...)))
                 ((include filename1 filename2 ...)
                  (and-map (lambda (fn)
                             (string? (syntax->datum fn)))
                           #'(filename1 filename2 ...))
                  (new-bodies (%read-files-for-include #'(filename1 filename2 ...)
                                                       #f
                                                       decl)))
                 ((include-ci filename1 filename2 ...)
                  (and-map (lambda (fn)
                             (string? (syntax->datum fn)))
                           #'(filename1 filename2 ...))
                  (new-bodies (%read-files-for-include #'(filename1 filename2 ...)
                                                       #t
                                                       decl)))
                 ((include-library-declarations filename1 filename2 ...)
                  (and-map (lambda (fn)
                             (string? (syntax->datum fn)))
                           #'(filename1 filename2 ...))
                  (splice-in (%read-files-for-include #'(filename1 filename2 ...)
                                                      #f
                                                      decl)))
                 ((cond-expand clause1 clause2 ...)
                  (splice-in (%cond-expand decl)))))))))))
