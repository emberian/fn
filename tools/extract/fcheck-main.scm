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
  (let* ((id (car entry)) (name (cadr entry)) (args (caddr entry)) (expected (cadddr entry))
         (nout (car (cddddr entry)))
         (proc (hash-table-ref/default extracted-functions name #f)))
    (if (not proc)
        (print "RAISE\t" id "\t" name "\tnot extracted")
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
          (cond ((eq? got 'hang) (print "HANG\t" id "\t" name "\t" (show args)))
                ((and (pair? got) (eq? (car got) 'raised))
                 (print "RAISE\t" id "\t" name "\t" (show args) "\t" (show (cadr got))))
                ((equal? got expected) (print "AGREE\t" id "\t" name))
                (else (print "DIFFER\t" id "\t" name "\t" (show args) "\t" (show expected) "\t" (show got))))))))

(define (main args)
  (print "FCHECK-BEGIN")
  (let ((n 0))
    (for-each (lambda (path)
                (call-with-input-file path
                  (lambda (p) (let loop () (let ((e (read p)))
                                             (unless (eof-object? e) (check e) (set! n (+ n 1)) (loop)))))))
              args)
    (print "FCHECK-COMPLETE\t" n)
    (flush-output)))
(main (command-line-arguments))
