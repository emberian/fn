; Bounded decisions used by the actual C maintenance owner. These read actual
; carriers; none accepts a caller readiness, cut or completed-page assertion.
(in-package "ACL2")
(include-book "checkpoint-master-abort")
(include-book "retirement")
(include-book "checkpoint-metadata-resources")
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

(defun fn2-checkpoint-catalog-retained-step (scan highest candidate found fn2-checkpoints fn2-checkpoint-teardown-debt)
 (declare (xargs :stobjs (fn2-checkpoints fn2-checkpoint-teardown-debt) :verify-guards nil
  :guard (and (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-teardown-debt-wfp fn2-checkpoint-teardown-debt)
              (unsigned-byte-p 32 scan) (unsigned-byte-p 60 highest) (unsigned-byte-p 32 candidate) (booleanp found))))
 (mv-let (code next high chosen have identity) (fn2-checkpoint-catalog-step scan highest candidate found fn2-checkpoints)
  (if (and (eq code :more) (not found) (equal chosen scan) (fn2-checkpoint-teardown-debt-heldp scan fn2-checkpoint-teardown-debt))
      (mv :more next high candidate nil 0)
    (mv code next high chosen have identity))))
(defcost fn2-checkpoint-catalog-op :child fn2-checkpoint-catalog-retained-step :answers t
 :tables (fn2-core-checkpoints fn2-core-checkpoint-teardown-debt)
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
(defcost fn2-checkpoint-plan-reserve-op :child fn2-checkpoint-plan-reserve-step :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-checkpoint-construction fn2-core-extents fn2-core-control)
 :doc "Reserve one derived map, arena or journal ticket extent; retained prefixes survive refusal.")
(defcost fn2-checkpoint-plan-validate-op :child fn2-checkpoint-plan-validate-step :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-checkpoint-build fn2-core-checkpoint-refs
          fn2-core-checkpoint-construction fn2-core-extents fn2-core-checkpoint-plan-marks)
 :doc "Validate one actual reservation identity and ordinal before the physical copy gate.")

(defun fn2-checkpoint-master-ready-children (token okind oslot ogen fn2-checkpoint-plan fn2-checkpoint-build
                                            fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs)
 (declare (xargs :stobjs (fn2-checkpoint-plan fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs)
  :guard (and (fn2-checkpoint-plan-wfp fn2-checkpoint-plan) (fn2-checkpoint-build-wfp fn2-checkpoint-build)
              (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints)
              (fn2-checkpoint-refs-wfp fn2-checkpoint-refs))))
 (mv-let (code checkpoint c extent epoch allocation slot gen)
  (fn2-checkpoint-build-ready token okind oslot ogen fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs)
  (declare (ignore checkpoint extent epoch allocation slot gen))
  (if (and (eq code :ready)
           (fn2-checkpoint-plan-closedp token okind oslot ogen fn2-checkpoint-plan fn2-csnapshot)
           (equal c (fn2-checkpoint-plan-candidate 0 fn2-checkpoint-plan)))
      (mv :ready c) (mv :pending 0))))
(defcost fn2-checkpoint-master-ready-op :child fn2-checkpoint-master-ready-children :answers (:ready :pending)
 :tables (fn2-core-checkpoint-plan fn2-core-checkpoint-build fn2-core-csnapshot fn2-core-checkpoints fn2-core-checkpoint-refs)
 :doc "Derive final B admission's candidate from actual closed C construction and physically ready descriptor state.")

(defun fn2-checkpoint-master-allocation-count-children (token okind oslot ogen fn2-retirement-control fn2-extents)
 (declare (xargs :stobjs (fn2-retirement-control fn2-extents)
  :guard (and (fn2-retirement-control-wfp fn2-retirement-control) (fn2-extents-wfp fn2-extents))))
 (if (and (< 0 (fn2-retirement-control-rows fn2-retirement-control))
          (equal (fn2-retirement-control-state 0 fn2-retirement-control) *fn2-retirement-state-staged*)
          (equal (fn2-retirement-control-allocation-member 0 fn2-retirement-control) 1)
          (equal (fn2-retirement-control-token 0 fn2-retirement-control) token)
          (equal (fn2-retirement-control-owner-kind 0 fn2-retirement-control) okind)
          (equal (fn2-retirement-control-owner-slot 0 fn2-retirement-control) oslot)
          (equal (fn2-retirement-control-owner-gen 0 fn2-retirement-control) ogen)
          (equal (fn2-alloc-freeze-phase fn2-extents) 2)
          (equal (fn2-alloc-freeze-token fn2-extents) token)
          (equal (fn2-alloc-freeze-owner-kind fn2-extents) okind)
          (equal (fn2-alloc-freeze-owner-slot fn2-extents) oslot)
          (equal (fn2-alloc-freeze-owner-gen fn2-extents) ogen))
     (mv :ok (fn2-retirement-control-count 0 fn2-retirement-control)) (mv :state 0)))
(defcost fn2-checkpoint-master-allocation-count-op :child fn2-checkpoint-master-allocation-count-children
 :answers (:ok :state) :tables (fn2-core-retirement-control fn2-core-extents)
 :doc "Read exact owner/token staged allocation count; only an actual empty scan may bypass allocation admission.")

(defun fn2-checkpoint-master-pressure-children (seen fn2-checkpoint-root1 fn2-csnapshot fn2-extents fn2-pool fn2-commit-root fn2-boot-config)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-csnapshot fn2-extents fn2-pool fn2-commit-root fn2-boot-config)
  :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-extents-wfp fn2-extents) (fn2-pool-wfp fn2-pool) (fn2-commit-root-wfp fn2-commit-root) (fn2-boot-config-wfp fn2-boot-config) (unsigned-byte-p 60 seen))))
 (mv :ok
  (and (equal (fn2-boot-config-checkpoint-layout-ready fn2-boot-config) 1)
       (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
       (< 0 (fn2-csnapshot-rows fn2-csnapshot))
       (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-idle*)
       (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*)
       (equal (fn2-alloc-freeze-phase fn2-extents) 0)
       (equal (fn2-alloc-freeze-token fn2-extents) 0)
       (< 0 (fn2-alloc-blocked fn2-extents))
       (< seen (fn2-alloc-last-retirement fn2-extents))
       (fn2-checkpoint-directory-roomp fn2-extents fn2-commit-root)
       (fn2-checkpoint-admission-roomp 0 fn2-pool))
  (fn2-alloc-last-retirement fn2-extents)))
(defcost fn2-checkpoint-master-pressure-op :child fn2-checkpoint-master-pressure-children :answers (:ok)
 :tables (fn2-core-checkpoint-root1 fn2-core-csnapshot fn2-core-extents fn2-core-pool fn2-core-commit-root fn2-core-boot-config)
 :doc "Report actual retirement debt with cached bundle and directory hints; permission is rechecked only at the held cut.")

; The lower release cursor resets root1 to IDLE only after all nineteen
; actual lease releases succeed. This observation ends the abstract bundle
; hold once, rather than pretending that each partial release drops it.
(defun fn2-checkpoint-master-release-complete-children (token kind owner gen fn2-checkpoint-root1 fn2-checkpoint-plan
                                                      fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
                                                      fn2-checkpoint-refs fn2-checkpoint-publication fn2-extents)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-checkpoint-plan fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
                          fn2-checkpoint-refs fn2-checkpoint-publication fn2-extents)
  :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-plan-wfp fn2-checkpoint-plan)
              (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-checkpoints-wfp fn2-checkpoints) (fn2-checkpoint-refs-wfp fn2-checkpoint-refs)
              (fn2-checkpoint-publication-wfp fn2-checkpoint-publication) (fn2-extents-wfp fn2-extents))))
 (mv-let (code c)
  (fn2-checkpoint-master-ready-children token kind owner gen fn2-checkpoint-plan fn2-checkpoint-build
   fn2-csnapshot fn2-checkpoints fn2-checkpoint-refs)
  (if (and (eq code :ready) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
           (< 0 (fn2-checkpoint-publication-rows fn2-checkpoint-publication))
           (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-idle*)
           (equal (fn2-checkpoint-root1-reserved 0 fn2-checkpoint-root1) 0)
           (equal (fn2-checkpoint-root1-owner-kind 0 fn2-checkpoint-root1) kind)
           (equal (fn2-checkpoint-root1-owner-slot 0 fn2-checkpoint-root1) owner)
           (equal (fn2-checkpoint-root1-owner-gen 0 fn2-checkpoint-root1) gen)
           (equal (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication) *fn2-checkpoint-publication-phase-complete*)
           (equal (fn2-checkpoint-publication-candidate 0 fn2-checkpoint-publication) c)
           (equal (fn2-checkpoint-publication-bundle-released 0 fn2-checkpoint-publication) 1)
           (equal (fn2-alloc-freeze-phase fn2-extents) 2)
           (equal (fn2-alloc-freeze-token fn2-extents) token)
           (equal (fn2-alloc-freeze-owner-kind fn2-extents) kind)
           (equal (fn2-alloc-freeze-owner-slot fn2-extents) owner)
           (equal (fn2-alloc-freeze-owner-gen fn2-extents) gen)) :ok :state)))
(defcost fn2-checkpoint-master-release-complete-op :child fn2-checkpoint-master-release-complete-children
 :answers (:ok :state)
 :tables (fn2-core-checkpoint-root1 fn2-core-checkpoint-plan fn2-core-checkpoint-build fn2-core-csnapshot fn2-core-checkpoints
          fn2-core-checkpoint-refs fn2-core-checkpoint-publication fn2-core-extents)
 :effects ((:release (:storage-window :storage-window)))
 :doc "End the abstract working-bundle hold only from actual terminal lease release and same-owner completed publication.")

(defun fn2-checkpoint-retirement-frontier-children (fn2-extents)
 (declare (xargs :stobjs fn2-extents :guard (fn2-extents-wfp fn2-extents)))
 (fn2-alloc-last-retirement fn2-extents))
(defcost fn2-checkpoint-retirement-frontier-op :child fn2-checkpoint-retirement-frontier-children
 :tables (fn2-core-extents)
 :doc "Capture actual retirement debt after C/B drain; only successful publication advances the actor's seen frontier.")
