;;; Reload in the actual warm developer owner after trace.lisp. No root worker
;;; hooks are recompiled or overwritten; exercise the shared macro directly.
(in-package "ACL2")

(defun fntr-run ()
  (let ((*fnn-trace-state* nil) (*fnn-trace-parent* nil)
        (*fnn-trace-parent-state* nil)
        (*fnn-trace-operation* nil) (*fnn-trace-connection-generation* nil)
        (old nil) (fresh nil))
    (fnn-trace-start :capacity 4)
    (setf old *fnn-trace-state*)
    (assert (equal (multiple-value-list
                    (fnn-trace-span (:old-sink :operation 19)
                      (fnn-trace-start :capacity 4)
                      (setf fresh *fnn-trace-state*)
                      (fnn-trace-span (:fresh-root)
                        (fnn-trace-span (:fresh-child) (values 1 2 3 4 5 6)))))
                   '(1 2 3 4 5 6)))
    (let* ((rows (fnn-trace-state-rows fresh)) (root (aref rows 0)) (child (aref rows 1)))
      (assert (null (fnn-trace-row-parent root)))
      (assert (= (fnn-trace-row-parent child) (fnn-trace-row-id root)))
      (assert (= (fnn-trace-row-operation child) 19))
      (assert (eq (fnn-trace-row-outcome (aref (fnn-trace-state-rows old) 0)) :returned)))
    ;; An old compiled hook only binds its numeric ID. Without provenance,
    ;; it cannot establish an ancestor in this sink, even if IDs coincide.
    (let ((*fnn-trace-parent* 1) (*fnn-trace-parent-state* nil))
      (fnn-trace-span (:legacy-unknown-parent) :ok)
      (assert (null (fnn-trace-row-parent (aref (fnn-trace-state-rows fresh) 2)))))
    (format t "NATIVE_TRACE_RESTART_PASS~%")
    :passed))
