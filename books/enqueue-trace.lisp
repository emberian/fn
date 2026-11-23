; Diagnostic evidence of an already performed scheduler enqueue. There is
; no pending wake queue and no instrumentation capacity gate on scheduling.
; The existing ring reports loss explicitly; incomplete evidence is rejected
; by replay. A standalone core enqueue is itself one complete trace event.
(in-package "ACL2")
(include-book "assembly-callbacks-b2")
(local (in-theory (disable fn2-trace-lost)))
(local (defthm fn2-core-trace-type-fc
         (implies (fn2-corep fn2-core)
                  (fn2-tracep (fn2-core-trace fn2-core)))
         :rule-classes :forward-chaining))
(defun fn2-core-record-enqueue (id fn2-core)
 (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
 (if (not (eq (fn2-machine-principal-slot-read-code id fn2-core) :ok))
     (stobj-let ((fn2-trace (fn2-core-trace fn2-core))) (fn2-trace)
      (update-fn2-trace-lost (min *fn2-u60-max* (+ 1 (fn2-trace-lost fn2-trace))) fn2-trace)
      fn2-core)
   (let ((principal (fn2-machine-principal-slot id fn2-core)))
    (stobj-let ((fn2-trace (fn2-core-trace fn2-core))) (fn2-trace)
     (fn2-trace-append *fn2-trace-kind-enqueue* id principal 0 0 0 0 nil *fn2-none* 0 0 fn2-trace)
     fn2-core))))
(fn2-core-preserves fn2-core-record-enqueue (id fn2-core) :rows nil)
(in-theory (disable fn2-core-record-enqueue))
