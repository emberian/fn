(in-package "ACL2")
:q
(handler-case
 (progn
  (multiple-value-bind (erp val state)
    (let ((*features* (adjoin :acl2-loop-only *features*)))
      (with-suppression
       (ld "fn2/experiments/squares/e2/load.lsp" :ld-error-action :error)))
    (declare (ignore state)) (assert (and (not erp) (eq val :eof))))
  (load "fn2/experiments/squares/e2/checker.lsp")
  (load "fn2/experiments/squares/e2/q1-campaigns.lsp")
  (setf *sq-runtime-rows* (copy-tree (table-alist 'sq-squares (w *the-live-state*)))
        *sq-coverage* (copy-tree (table-alist 'sq-coverage (w *the-live-state*)))
        *sq-revision* (or (sb-ext:posix-getenv "SQ_REVISION")
                          (error "SQ_REVISION must identify HEAD and experiment source bytes")))
  (assert (= (length *sq-runtime-rows*) 45))
  (sq-write-object "fn2/experiments/squares/e2/q1-translated.sexp"
    (loop for i below (length *fn2-e1-labels*) for id = (sq-q1-id i)
          collect (cons id (getf (cdr (assoc id *sq-runtime-rows*)) :translated))))
  (assert (sq-q4-template-negative))
  (format t "E2 Q4 TEMPLATE PASS count-only-step=~S count-only-composition=~S~%"
          (sq-q4-count-generated-step *rs-s1* *rs-s2* '(:read 1))
          (sq-q4-count-generated-composition *rs-s1* *rs-s2* *rs-suffix* '(:count 2)))
  (sq-run-declared-evidence)
  (let ((pass (sq-report)))
    (sq-write-object "fn2/experiments/squares/e2/evidence.sexp"
                     (list :revision *sq-revision* :coverage *sq-coverage*
                           :rows *sq-runtime-rows*))
    (sq-write-evidence-events "fn2/experiments/squares/e2/evidence-events.lsp")
    ; Replay the append events into ACL2's table, retaining the original proof
    ; field and validating record scopes. Raw snapshots are not the store.
    (multiple-value-bind (erp val state)
      (let ((*features* (adjoin :acl2-loop-only *features*)))
        (with-suppression
         (ld "fn2/experiments/squares/e2/evidence-events.lsp" :ld-error-action :error)))
      (declare (ignore state)) (assert (and (not erp) (eq val :eof))))
    (let ((stored (table-alist 'sq-squares (w *the-live-state*))))
      (assert (= (length stored) (length *sq-runtime-rows*)))
      (dolist (entry *sq-runtime-rows*)
        (assert (equal entry (assoc (car entry) stored)))))
    (assert pass)
    (format t "E2 ACCEPTANCE PASS rows=45 Q1=40-owed Q4=5-proved proof-status-unchanged=T~%")
    (finish-output) (sb-ext:exit :code 0)))
 (cl:error (condition)
   (format t "E2 DRIVER-ERROR ~A~%" condition)
   (finish-output) (sb-ext:exit :code 2)))
