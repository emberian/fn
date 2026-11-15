; Reference-only semantic primitive. Literal FIFO decisions do not inspect
; the diagnostic ring or the reference core's unused intrusive queue.
(in-package "ACL2")
(include-book "reference-state-model")

; Keep all original outputs at their existing positions and append the
; independent FIFO carrier. Lists may also carry selection history; only
; the existing literal queue field changes through FN2-REF-WAKE.
(defun fn2-ref-effect-scheduler-wake (id fn2-ref-core lists)
  (declare (xargs :stobjs fn2-ref-core :verify-guards nil))
  (mv-let (lists fn2-ref-core) (fn2-ref-wake id lists fn2-ref-core)
    (mv fn2-ref-core lists)))

; Complete callback carrier relation for the generated selected-body square.
; Scalars means every original non-core result, in original ABI order.
; This is an output predicate, not an attachment or refinement theorem.
(defun-nx fn2-ref-effect-whole-resultp (actual-scalars modeled-scalars
                                      fn2-core fn2-ref-core lists)
  (and (equal actual-scalars modeled-scalars)
       (fn2-representation-relation fn2-core fn2-ref-core lists)))
