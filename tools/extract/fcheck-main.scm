;;; tools/extract/fcheck-main.scm -- the CHICKEN side of the per-function
;;; differential: each vector (NAME (ARGS...) EXPECTED NOUT), written from
;;; ACL2's own evaluation (tools/extract/fcheck.lisp), is applied to the
;;; extracted procedure and compared with equal?.  One line per vector:
;;; AGREE / DIFFER / RAISE, the function, and for a non-agreement the
;;; arguments, the expected and the observed value.
(include "runtime.scm")
(include "served.scm")
(include "native.scm")
(include "hostio.scm")
(include "fntable.scm")
(import (chicken process signal))

;; A vector that runs past its budget is reported HANG, not waited on (a
;; mutant's non-terminating recursion must not stop the run).
(define vector-escape #f)
(set-signal-handler! signal/alrm (lambda (s) (when vector-escape (vector-escape 'hang))))

(define (show x) (let ((s (with-output-to-string (lambda () (write x)))))
                   (if (> (string-length s) 300) (string-append (substring s 0 300) "...") s)))

(define (check entry)
  (let* ((name (car entry)) (args (cadr entry)) (expected (caddr entry)) (nout (cadddr entry))
         (proc (hash-table-ref/default extracted-functions name #f)))
    (if (not proc)
        (print "RAISE\t" name "\tnot extracted")
        (let ((got (call/cc
                    (lambda (k)
                      (set! vector-escape k)
                      (set-alarm! 5)
                      (let ((v (handle-exceptions exn (list 'raised (condition->list exn))
                                 (if (> nout 1)
                                     (call-with-values (lambda () (apply proc args)) list)
                                     (apply proc args)))))
                        (set-alarm! 0)
                        (set! vector-escape #f)
                        v)))))
          (cond ((eq? got 'hang) (print "HANG\t" name "\t" (show args)))
                ((and (pair? got) (eq? (car got) 'raised))
                 (print "RAISE\t" name "\t" (show args) "\t" (show (cadr got))))
                ((equal? got expected) (print "AGREE\t" name))
                (else (print "DIFFER\t" name "\t" (show args) "\t" (show expected) "\t" (show got))))))))

(define (main args)
  (for-each (lambda (path)
              (call-with-input-file path
                (lambda (p) (let loop () (let ((e (read p))) (unless (eof-object? e) (check e) (loop)))))))
            args))
(main (command-line-arguments))
