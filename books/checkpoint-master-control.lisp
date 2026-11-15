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
          fn2-core-checkpoint-refs fn2-core-checkpoint-construction fn2-core-extents fn2-core-checkpoint-plan-marks fn2-core-checkpoint-planning)
 :doc "Start counting the actual completed source roots and retained construction set.")
(defcost fn2-checkpoint-plan-count-op :child fn2-checkpoint-plan-count-step :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-checkpoint-build fn2-core-checkpoint-refs
          fn2-core-checkpoint-construction fn2-core-extents fn2-core-checkpoint-plan-marks)
 :doc "Inspect one actual extent and aggregate its exact completed construction bytes.")
(defcost fn2-checkpoint-plan-size-op :child fn2-checkpoint-plan-size-step :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-extents)
 :doc "Advance one monotone ticket/arena fixedpoint iteration under actual allocator capacity.")
(defcost fn2-checkpoint-plan-reserve-op :child fn2-checkpoint-plan-reserve-step :answers t
 :tables (fn2-core-checkpoint-plan fn2-core-csnapshot fn2-core-checkpoint-construction fn2-core-extents fn2-core-control fn2-core-checkpoint-planning fn2-core-checkpoint-recipe fn2-core-checkpoint-recipe-order)
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

(defun fn2-checkpoint-master-pressure-children (seen fn2-checkpoint-root1 fn2-csnapshot fn2-extents fn2-pool fn2-commit-root fn2-boot-config fn2-checkpoint-master fn2-machines fn2-checkpoint-retry fn2-checkpoint-retry-classes fn2-id-engine fn2-seals)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-csnapshot fn2-extents fn2-pool fn2-commit-root fn2-boot-config fn2-checkpoint-master fn2-machines fn2-checkpoint-retry fn2-checkpoint-retry-classes fn2-id-engine fn2-seals)
  :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-extents-wfp fn2-extents) (fn2-pool-wfp fn2-pool) (fn2-commit-root-wfp fn2-commit-root) (fn2-boot-config-wfp fn2-boot-config) (unsigned-byte-p 60 seen) (fn2-checkpoint-master-wfp fn2-checkpoint-master) (fn2-machines-wfp fn2-machines) (fn2-checkpoint-retry-wfp fn2-checkpoint-retry) (fn2-checkpoint-retry-classes-wfp fn2-checkpoint-retry-classes) (fn2-id-engine-wfp fn2-id-engine) (fn2-seals-wfp fn2-seals))))
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
       (fn2-checkpoint-admission-roomp 0 fn2-pool)
       ; A failed forecast is owed work, but identical inputs cannot progress.
       ; The stamp is only a wake hint: actual held admission is always redone.
       (not (and (< 0 (fn2-checkpoint-master-rows fn2-checkpoint-master))
                 (< *fn2-checkpoint-master-kind* (fn2-machines-kind-bases-length fn2-machines))
                 (fn2-checkpoint-retry-samep *fn2-checkpoint-master-kind*
                  (fn2-machines-kind-basesi *fn2-checkpoint-master-kind* fn2-machines)
                  (fn2-checkpoint-master-generation 0 fn2-checkpoint-master)
                  fn2-checkpoint-retry fn2-checkpoint-retry-classes fn2-csnapshot fn2-id-engine fn2-seals fn2-extents fn2-commit-root fn2-pool))))
  (fn2-alloc-last-retirement fn2-extents)))
(defcost fn2-checkpoint-master-pressure-op :child fn2-checkpoint-master-pressure-children :answers (:ok)
 :tables (fn2-core-checkpoint-root1 fn2-core-csnapshot fn2-core-extents fn2-core-pool fn2-core-commit-root fn2-core-boot-config fn2-checkpoint-master-table fn2-core-machines fn2-core-checkpoint-retry fn2-core-checkpoint-retry-classes fn2-core-id-engine fn2-core-seals)
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

; Materialized after machine tables, before generated actor faces. Capture is
; AFTER actual cleanup; own cancelled allocation identities cannot wake it.
(defmacro fn2-checkpoint-master-retry-events ()
 '(progn
   (defun fn2-checkpoint-master-retry-record-children (fn2-checkpoint-master fn2-machines fn2-csnapshot fn2-checkpoint-root1 fn2-checkpoint-future fn2-checkpoint-build fn2-checkpoints fn2-extents fn2-pool fn2-commit-root fn2-id-engine fn2-seals fn2-control fn2-checkpoint-retry fn2-checkpoint-retry-classes)
    (declare (xargs :stobjs (fn2-checkpoint-master fn2-machines fn2-csnapshot fn2-checkpoint-root1 fn2-checkpoint-future fn2-checkpoint-build fn2-checkpoints fn2-extents fn2-pool fn2-commit-root fn2-id-engine fn2-seals fn2-control fn2-checkpoint-retry fn2-checkpoint-retry-classes) :guard (and (fn2-checkpoint-master-wfp fn2-checkpoint-master) (fn2-machines-wfp fn2-machines) (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-future-wfp fn2-checkpoint-future) (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-extents-wfp fn2-extents) (fn2-pool-wfp fn2-pool) (fn2-commit-root-wfp fn2-commit-root) (fn2-id-engine-wfp fn2-id-engine) (fn2-seals-wfp fn2-seals) (fn2-control-wfp fn2-control) (fn2-checkpoint-retry-wfp fn2-checkpoint-retry) (fn2-checkpoint-retry-classes-wfp fn2-checkpoint-retry-classes))))
    (b* (((unless (and (< 0 (fn2-checkpoint-master-rows fn2-checkpoint-master))
                       (< 0 (fn2-csnapshot-rows fn2-csnapshot)) (< 0 (fn2-checkpoint-root1-rows fn2-checkpoint-root1))
                       (< 0 (fn2-checkpoint-future-rows fn2-checkpoint-future)) (< 0 (fn2-checkpoint-build-rows fn2-checkpoint-build))
                       (< *fn2-checkpoint-master-kind* (fn2-machines-kind-bases-length fn2-machines))))
           (mv :bounds fn2-checkpoint-retry fn2-checkpoint-retry-classes))
         (id (fn2-machines-kind-basesi *fn2-checkpoint-master-kind* fn2-machines))
         (gen (fn2-checkpoint-master-generation 0 fn2-checkpoint-master))
         (c (fn2-checkpoint-master-candidate 0 fn2-checkpoint-master))
         (token (fn2-checkpoint-master-token 0 fn2-checkpoint-master))
         (reason (fn2-checkpoint-master-refusal-reason 0 fn2-checkpoint-master))
         ((unless (and (member-equal (fn2-checkpoint-master-phase 0 fn2-checkpoint-master)
                        (list *fn2-checkpoint-master-state-abort-empty* *fn2-checkpoint-master-state-abort-complete*))
                       (natp id) (< id (fn2-machines-rows fn2-machines)) (posp gen) (posp token)
                       (equal (fn2-machines-kind id fn2-machines) *fn2-checkpoint-master-kind*) (equal (fn2-machines-slot id fn2-machines) 0)
                       (member-equal reason (list *fn2-checkpoint-retry-pool* *fn2-checkpoint-retry-directory* *fn2-checkpoint-retry-physical*))
                       (equal token (fn2-csnapshot-token 0 fn2-csnapshot))
                       (equal (fn2-csnapshot-owner-kind 0 fn2-csnapshot) *fn2-checkpoint-master-kind*)
                       (equal (fn2-csnapshot-owner-slot 0 fn2-csnapshot) id) (equal (fn2-csnapshot-owner-gen 0 fn2-csnapshot) gen)
                       (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-idle*)
                       (equal (fn2-alloc-freeze-phase fn2-extents) 0) (equal (fn2-alloc-freeze-token fn2-extents) 0)
                       (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-idle*)
                       (equal (fn2-checkpoint-root1-reserved 0 fn2-checkpoint-root1) 0)
                       (equal (fn2-checkpoint-future-phase 0 fn2-checkpoint-future) *fn2-checkpoint-future-phase-idle*)
                       (equal (fn2-checkpoint-future-reserved 0 fn2-checkpoint-future) 0)
                       (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-idle*)
                       (< c (fn2-checkpoints-rows fn2-checkpoints))
                       (equal (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-free*)
                       (equal (fn2-control-stop fn2-control) 0)))
          (mv :owner fn2-checkpoint-retry fn2-checkpoint-retry-classes)))
     (fn2-checkpoint-retry-record *fn2-checkpoint-master-kind* id gen reason
      fn2-checkpoint-retry fn2-checkpoint-retry-classes fn2-csnapshot fn2-id-engine fn2-seals fn2-extents fn2-commit-root fn2-pool)))
   (fn2-checkpoint-retry-preserves fn2-checkpoint-master-retry-record-children
    (fn2-checkpoint-master fn2-machines fn2-csnapshot fn2-checkpoint-root1 fn2-checkpoint-future fn2-checkpoint-build fn2-checkpoints fn2-extents fn2-pool fn2-commit-root fn2-id-engine fn2-seals fn2-control fn2-checkpoint-retry fn2-checkpoint-retry-classes)
    :carriers ((fn2-checkpoint-retry 1 :prefix "-RETRY") (fn2-checkpoint-retry-classes 2 :prefix "-CLASSES")))))
(defcost fn2-checkpoint-master-retry-record-op :child fn2-checkpoint-master-retry-record-children
 :answers (:ok :bounds :owner :directory-state)
 :tables (fn2-checkpoint-master-table fn2-core-machines fn2-core-csnapshot fn2-core-checkpoint-root1 fn2-core-checkpoint-future
          fn2-core-checkpoint-build fn2-core-checkpoints fn2-core-extents fn2-core-pool fn2-core-commit-root fn2-core-id-engine fn2-core-seals
          fn2-core-control fn2-core-checkpoint-retry fn2-core-checkpoint-retry-classes)
 :doc "Capture current-owner refusal fingerprint only after exact C/B/candidate/27-resource cleanup; preserve retirement debt.")
