; Actual native root1 source-selector admission, not a shadow archive model.
; Runnable but unexecuted under source-only grant.
(in-package "ACL2")
(include-book "../books/event-archive-producer")
(assert-event (and (fn2-run-layout-internal-p 20) (not (fn2-run-layout-internal-p 3))))
(defun fn2-ear1u-test ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-checkpoint-source
  (mv-let (answer fn2-checkpoint-source)
   (b* ((fn2-checkpoint-source (fn2-checkpoint-source-init 1 fn2-checkpoint-source))
        (fn2-checkpoint-source (fn2-checkpoint-source-set-phase 0 *fn2-checkpoint-source-phase-scan* fn2-checkpoint-source))
        (fn2-checkpoint-source (fn2-checkpoint-source-consider 20 1 7 0 fn2-checkpoint-source))
        (internal (equal (fn2-checkpoint-source-found 0 fn2-checkpoint-source) 0))
        (fn2-checkpoint-source (fn2-checkpoint-source-consider 3 1 7 0 fn2-checkpoint-source)))
    (mv (and internal (= (fn2-checkpoint-source-found 0 fn2-checkpoint-source) 1)
             (= (fn2-checkpoint-source-schema 0 fn2-checkpoint-source) 3)) fn2-checkpoint-source)) answer)))
(assert-event (fn2-ear1u-test))
