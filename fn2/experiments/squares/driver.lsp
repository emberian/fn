(in-package "ACL2")
:q
(handler-case
 (progn
  (defparameter *e1-load-start* (get-internal-real-time))
  (multiple-value-bind (erp val state)
    (let ((*features* (adjoin :acl2-loop-only *features*)))
      (with-suppression (ld "fn2/experiments/squares/load.lsp" :ld-error-action :error)))
    (declare (ignore state)) (assert (and (not erp) (eq val :eof))))
  (let ((mutant (sb-ext:posix-getenv "E1_MUTANT")))
   (when (and mutant (not (equal mutant "ORIGINAL")))
    (multiple-value-bind (erp val state)
      (let ((*features* (adjoin :acl2-loop-only *features*)))
       (with-suppression
        (ld (format nil "fn2/experiments/squares/mutants/~A.lsp" mutant) :ld-error-action :error)))
      (declare (ignore state)) (assert (and (not erp) (eq val :eof))))))
  (load "fn2/experiments/squares/runner.lsp")
  (format t "E1 LOAD seconds=~,6F~%" (/ (- (get-internal-real-time) *e1-load-start*) internal-time-units-per-second))
  (finish-output)
  (e1-main)
  (sb-ext:exit :code 0))
 (cl:error (condition)
   (format t "E1 DRIVER-ERROR ~A~%" condition) (finish-output) (sb-ext:exit :code 2)))
