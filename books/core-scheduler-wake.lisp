; The shared concrete scheduler wake. Diagnostic tracing and pending wake
; handoffs are callers' concerns; this primitive validates the actual principal
; and performs the existing bounded scheduler insertion, idempotently.
(in-package "ACL2")
(include-book "assembly-access")

(defun fn2-core-scheduler-wake (id fn2-core)
  (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)
                  :guard-hints (("Goal" :in-theory (enable fn2-core-wfp)))))
  (if (equal id *fn2-none*) fn2-core
    (if (not (eq (fn2-machine-principal-slot-read-code id fn2-core) :ok))
        (fn2-core-stop *fn2-stop-reason-wake-bounds* fn2-core)
  (let ((principal (fn2-machine-principal-slot id fn2-core)))
    (stobj-let ((fn2-sched (fn2-core-sched fn2-core)))
      (code fn2-sched) (fn2-sched-make-runnable id principal fn2-sched)
      (case code
        ((:ok :already) fn2-core)
        (:bounds (fn2-core-stop *fn2-stop-reason-wake-bounds* fn2-core))
        (otherwise (fn2-core-stop *fn2-stop-reason-wake-state* fn2-core))))))))
(fn2-core-preserves fn2-core-scheduler-wake (id fn2-core) :rows nil :prefix "")
(in-theory (disable fn2-core-scheduler-wake))
