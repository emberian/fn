; Bounded decisions used by the actual C maintenance owner. These read actual
; carriers; none accepts a caller readiness, cut or completed-page assertion.
(in-package "ACL2")
(include-book "checkpoint-master-state")
(fn2-book-layer :c)

(defun fn2-checkpoint-catalog-step (scan highest candidate found fn2-checkpoints)
 (declare (xargs :stobjs fn2-checkpoints
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (unsigned-byte-p 32 scan)
              (unsigned-byte-p 60 highest) (unsigned-byte-p 32 candidate) (booleanp found))))
 (if (>= scan (fn2-checkpoints-rows fn2-checkpoints))
     (cond ((not found) (mv :no-space scan highest candidate found 0))
           ((not (unsigned-byte-p 60 (+ 1 highest))) (mv :exhausted scan highest candidate found 0))
           (t (mv :ready scan highest candidate found (+ 1 highest))))
   (let* ((state (fn2-checkpoints-state scan fn2-checkpoints))
          (installed (and (member-equal state (list *fn2-checkpoint-state-installed* *fn2-checkpoint-state-promoting* *fn2-checkpoint-state-promoted*))
                          (< 0 (fn2-checkpoints-installation-commit scan fn2-checkpoints))))
          (next-highest (if installed (max highest (fn2-checkpoints-checkpoint scan fn2-checkpoints)) highest))
          (choose (and (not found) (equal state *fn2-checkpoint-state-free*))))
    (if (unsigned-byte-p 32 (+ 1 scan))
        (mv :more (+ 1 scan) next-highest (if choose scan candidate) (or found choose) 0)
      (mv :exhausted scan highest candidate found 0)))))

(defcost fn2-checkpoint-catalog-op :child fn2-checkpoint-catalog-step :answers t
 :tables (fn2-core-checkpoints)
 :doc "Inspect one actual candidate; choose a FREE row and an identity above installed predecessors before acquiring the C cut.")

(defun fn2-checkpoint-plan-phase-children (fn2-checkpoint-plan)
 (declare (xargs :stobjs fn2-checkpoint-plan :guard (fn2-checkpoint-plan-wfp fn2-checkpoint-plan)))
 (if (< 0 (fn2-checkpoint-plan-rows fn2-checkpoint-plan))
     (mv :ok (fn2-checkpoint-plan-phase 0 fn2-checkpoint-plan)) (mv :bounds 0)))
(defcost fn2-checkpoint-plan-phase-op :child fn2-checkpoint-plan-phase-children :answers (:ok :bounds)
 :tables (fn2-core-checkpoint-plan)
 :doc "Read the actual bounded reservation planner phase; no external closure flag.")

(defcost fn2-checkpoint-plan-begin-op :child fn2-checkpoint-plan-begin :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-checkpoint-build fn2-core-checkpoints
          fn2-core-checkpoint-refs fn2-core-checkpoint-construction fn2-core-extents fn2-core-checkpoint-plan-marks)
 :doc "Start counting the actual completed source roots and retained construction set.")
(defcost fn2-checkpoint-plan-count-op :child fn2-checkpoint-plan-count-step :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-checkpoint-build fn2-core-checkpoint-refs
          fn2-core-checkpoint-construction fn2-core-extents fn2-core-checkpoint-plan-marks)
 :doc "Inspect one actual extent and aggregate its exact completed construction bytes.")
(defcost fn2-checkpoint-plan-size-op :child fn2-checkpoint-plan-size-step :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-extents)
 :doc "Advance one monotone ticket/arena fixedpoint iteration under actual allocator capacity.")
(defcost fn2-checkpoint-plan-reserve-op :child fn2-checkpoint-plan-reserve-step :answers t :effects :per-use
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-checkpoint-construction fn2-core-extents fn2-core-control)
 :doc "Reserve one derived map, arena or journal ticket extent; retained prefixes survive refusal.")
(defcost fn2-checkpoint-plan-validate-op :child fn2-checkpoint-plan-validate-step :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-checkpoint-build fn2-core-checkpoint-refs
          fn2-core-checkpoint-construction fn2-core-extents fn2-core-checkpoint-plan-marks)
 :doc "Validate one actual reservation identity and ordinal before the physical copy gate.")
