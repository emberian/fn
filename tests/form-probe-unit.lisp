; MACHINE-FORM 6.5 P4 probe: the assembly's wrapper of a child-level arm is
; one stobj-let of its children; its core facts come from the per-child facts.
(in-package "ACL2")
(include-book "../books/assembly-access")
(include-book "form-probe-kind")

(defun fn2-probe-wrapper (id kind principal fn2-core)
  (declare (xargs :stobjs fn2-core :guard (and (fn2-core-wfp fn2-core) (fn2-machine-idp id fn2-core))))
  (let ((slot (fn2-machine-slot id fn2-core)))
    (stobj-let ((fn2-echo (fn2-echo-table fn2-core))
                (fn2-pool (fn2-core-pool fn2-core))
                (fn2-ops (fn2-core-ops fn2-core)))
      (code fn2-echo fn2-pool fn2-ops)
      (if (and (natp slot) (< slot (fn2-echo-rows fn2-echo)))
          (fn2-probe-issue-half slot 0 0 kind 1 id 1 principal fn2-echo fn2-pool fn2-ops)
        (mv :bounds fn2-echo fn2-pool fn2-ops))
      (mv code fn2-core))))
(fn2-core-preserves fn2-probe-wrapper (id kind principal fn2-core) :position 1 :rows nil)
