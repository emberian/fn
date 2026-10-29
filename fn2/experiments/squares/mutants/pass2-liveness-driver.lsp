(in-package "ACL2")
:q
(declaim (special *e1q-stream* *pass2-core-transitions* *pass2-ref-transitions*))
(handler-case
  (progn
    (defparameter *pass2-root* (namestring (truename ".")))
    (defparameter *pass2-qa* (parse-integer (or (sb-ext:posix-getenv "FN2_PASS2_QA") "4")))
    (defparameter *pass2-output* (sb-ext:posix-getenv "FN2_PASS2_OUTPUT"))
    (multiple-value-bind (erp value state)
      (let ((*features* (adjoin :acl2-loop-only *features*)))
        (with-suppression
          (ld `((set-prover-step-limit 300000)
                (set-cbd ,(concatenate 'string *pass2-root* "fn2/tests/"))
                (ld "sim-layer-a.lisp" :ld-error-action :error)
                (set-guard-checking nil)) :ld-error-action :error)))
      (declare (ignore state))
      (assert (and (not erp) (eq value :eof))))
    (load (merge-pathnames "fn2/experiments/squares/mutants/qualification-hooks.lsp" *pass2-root*))
    (load (merge-pathnames "fn2/experiments/squares/mutants/pass2-liveness-hooks.lsp" *pass2-root*))
    (defparameter *pass2-profile*
      (put-assoc-equal :qa *pass2-qa*
        (put-assoc-equal :c 1 (put-assoc-equal :accept-credits 1 *fn2-profile-tiny*))))
    (assert (fn2-core-profilep *pass2-profile*))
    (assert (> (fn2-profile-h *pass2-profile*) 3))
    (assert (>= (min (fn2-profile-o *pass2-profile*) (fn2-profile-qa *pass2-profile*))
                (+ (* 2 (fn2-profile-c *pass2-profile*))
                   (fn2-profile-accept-credits *pass2-profile*) 1)))
    (with-open-file (*e1q-stream* (merge-pathnames *pass2-output* *pass2-root*)
                                :direction :output :if-exists :supersede)
      (e1q-record (list :profile *pass2-profile* :seed 20261028 :safety-target 1
                       :premises :pass :mutant :original))
      (pass2-install)
      (unwind-protect
        (let ((result (catch 'pass2-done
                        (fn2-sim-run-echo 20261028 1 *pass2-profile*))))
          (e1q-record (list :result result))
          (let ((*print-pretty* nil))
            (format t "E1 PASS2 LIVENESS qa=~D result=~S witness=~A~%"
                    *pass2-qa* result *pass2-output*))
          (finish-output))
        (e1q-restore)))
    (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "E1 PASS2 LIVENESS ERROR: ~A~%" condition)
    (sb-ext:exit :code 1)))
