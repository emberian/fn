; Fresh process per qualification. See README.md for launch environment.
(in-package "ACL2")
:q
(declaim (special *e1q-stream* *e1q-tape* *e1q-start* *e1q-core*
                  *e1q-reference* *e1q-turn* *e1q-randoms* *e1q-boundary*
                  *e1q-tape-used* *e1q-replay*))
(handler-case
  (progn
    (defparameter *e1q-root* (namestring (truename ".")))
    (defparameter *e1q-mutant* (or (sb-ext:posix-getenv "FN2_E1_MUTANT") "ORIGINAL"))
    (defparameter *e1q-seed* (parse-integer (or (sb-ext:posix-getenv "FN2_E1_SEED") "20261028")))
    (defparameter *e1q-path* (or (sb-ext:posix-getenv "FN2_E1_OUTPUT")
                               "fn2/experiments/squares/mutants/qualification.sexp"))
    (defparameter *e1q-load-start* (get-internal-real-time))
    (multiple-value-bind (erp value state)
      (let ((*features* (adjoin :acl2-loop-only *features*)))
        (with-suppression
          (ld `((set-prover-step-limit 300000)
                (set-cbd ,(concatenate 'string *e1q-root* "fn2/tests/"))
                (ld "sim-layer-a.lisp" :ld-error-action :error)
                (set-guard-checking nil)) :ld-error-action :error)))
      (declare (ignore state))
      (assert (and (not erp) (eq value :eof))))
    (unless (string= *e1q-mutant* "ORIGINAL")
      (multiple-value-bind (erp value state)
        (let ((*features* (adjoin :acl2-loop-only *features*)))
          (with-suppression
            (ld `((set-cbd ,(concatenate 'string *e1q-root* "fn2/experiments/squares/mutants/"))
                  (ld ,(concatenate 'string *e1q-mutant* ".lsp") :ld-error-action :error)
                  (set-guard-checking nil)) :ld-error-action :error)))
        (declare (ignore state))
        (assert (and (not erp) (eq value :eof)))))
    (load (merge-pathnames "fn2/experiments/squares/mutants/qualification-hooks.lsp" *e1q-root*))
    (defparameter *e1q-profile*
      (put-assoc-equal :c 1 (put-assoc-equal :accept-credits 1 *fn2-profile-tiny*)))
    (assert (fn2-core-profilep *e1q-profile*))
    (when (sb-ext:posix-getenv "FN2_E1_REPLAY")
      (setf *e1q-replay* t)
      (with-open-file (s (merge-pathnames (sb-ext:posix-getenv "FN2_E1_REPLAY") *e1q-root*))
        (setf *e1q-tape*
          (loop for form = (read s nil :eof) until (eq form :eof)
                when (eq (car form) :random) collect (third form)))))
    (setf *print-pretty* nil)
    (defparameter *e1q-load-seconds*
      (/ (- (get-internal-real-time) *e1q-load-start*)
         (float internal-time-units-per-second 1d0)))
    (format t "E1 QUALIFICATION LOAD mutant=~A seconds=~,6F~%" *e1q-mutant* *e1q-load-seconds*)
    (finish-output)
    (with-open-file (*e1q-stream* (merge-pathnames *e1q-path* *e1q-root*) :direction :output :if-exists :supersede)
      (e1q-record (list :manifest :mutant *e1q-mutant* :seed *e1q-seed*
                       :profile *e1q-profile* :connections 1 :wall-budget 120
                       :transition-cap 500000 :load-seconds *e1q-load-seconds*))
      (setf *e1q-start* (get-internal-real-time))
      (e1q-install)
      (unwind-protect
        (let* ((answer (catch 'e1q-end (fn2-sim-run-echo *e1q-seed* 1 *e1q-profile*)))
               (seconds (e1q-seconds)))
          (e1q-record (list :result answer :seconds seconds :core *e1q-core*
                           :reference *e1q-reference* :turns *e1q-turn*
                           :randoms *e1q-randoms* :replay-used *e1q-tape-used*
                           :remaining-replay (length *e1q-tape*) :first-failure *e1q-boundary*))
          (format t "E1 QUALIFICATION mutant=~A seed=~D verdict=~S seconds=~,6F core=~D reference=~D turns=~D randoms=~D boundary=~S schedule=~A~%"
            *e1q-mutant* *e1q-seed* (first answer) seconds *e1q-core* *e1q-reference*
            *e1q-turn* *e1q-randoms* *e1q-boundary* *e1q-path*)
          (finish-output))
        (e1q-restore)))
    (sb-ext:exit :code 0))
  (cl:error (condition)
    (format *error-output* "E1 QUALIFICATION ERROR: ~A~%" condition)
    (sb-ext:exit :code 1)))
