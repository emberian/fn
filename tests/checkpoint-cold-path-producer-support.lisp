; Exact shared producer/observer support for persisted cold-path fixtures.
; Test-only maintenance entry; activation remains NIL, scheduler unqualified.
; No selected candidate, authenticated phase or persistence outcome is seeded.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../books/node-profile")
(include-book "checkpoint-cold-path-drive")

(defconst *fn2-ccp-image-size* 33554432)
(defconst *fn2-ccp-profile*
 (put-assoc-equal :sim-sectors (/ *fn2-ccp-image-size* 512)
  (fn2-image-profile *fn2-node-profile*)))

(defun fn2-ccp-live-complete-p (publish batch fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if publish
  (let ((id (fn2-machine-kind-base *fn2-checkpoint-master-kind* fn2-core)))
   (and (eq (fn2-checkpoint-master-snapshot-read-code id fn2-core) :ok)
        (member-equal (fn2-machine-phase id fn2-core)
         (list *fn2-checkpoint-master-state-idle* *fn2-checkpoint-master-state-disabled*))
        (= (fn2-checkpoint-master-row-token id fn2-core) 0)
        (stobj-let ((fn2-checkpoint-publication (fn2-core-checkpoint-publication fn2-core))) (complete)
         (and (= (fn2-checkpoint-publication-has-base 0 fn2-checkpoint-publication) 1)
              (= (fn2-checkpoint-publication-phase 0 fn2-checkpoint-publication) *fn2-checkpoint-publication-phase-complete*)) complete)))
  (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (complete)
   (and (posp batch) (<= batch (fn2-commit-root-installed 0 fn2-commit-root))) complete)))

(defun fn2-ccp-live-drive (fuel publish batch fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
 (cond ((zp fuel) (mv :fuel fn2-core fn2-sim fn2-own))
       ((fn2-core-stopped-p fn2-core) (mv :failed fn2-core fn2-sim fn2-own))
       ((fn2-ccp-live-complete-p publish batch fn2-core) (mv :complete fn2-core fn2-sim fn2-own))
       (t (b* (((mv status fn2-core fn2-sim fn2-own) (fn2-ccp-pump fn2-core fn2-sim fn2-own)))
           (if (eq status :failed) (mv status fn2-core fn2-sim fn2-own)
            (fn2-ccp-live-drive (- fuel 1) publish batch fn2-core fn2-sim fn2-own))))))

; Enter only the parked, empty typed owner. Candidate, checkpoint number,
; source cut, roots, verification and Fence results come from its real arms.
(defun fn2-ccp-maintenance-entry (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((id (fn2-machine-kind-base *fn2-checkpoint-master-kind* fn2-core))
      ((unless (and (eq (fn2-checkpoint-master-snapshot-read-code id fn2-core) :ok)
                    (member-equal (fn2-machine-phase id fn2-core)
                     (list *fn2-checkpoint-master-state-idle* *fn2-checkpoint-master-state-disabled*))
                    (= (fn2-checkpoint-master-row-token id fn2-core) 0)
                    (= (fn2-checkpoint-master-row-pending id fn2-core) 0))) (mv :state fn2-core))
      (fn2-core (fn2-checkpoint-master-put-core id (phase *fn2-checkpoint-master-state-catalog*)
        (scan 0) (highest 0) (candidate 0) (candidate-found 0)))
      (fn2-core (fn2-exec-wake id fn2-core)))
  (mv :ok fn2-core)))

(defun fn2-ccp-prefix-and-publication (fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* (((mv admitted writer prefix & fn2-core) (fn2-commit-admit-keyed 1 0 0 0 0 fn2-core))
      ((unless (eq admitted :ok)) (mv admitted 0 0 fn2-core fn2-sim fn2-own))
      (fn2-core (fn2-exec-wake writer fn2-core))
      ((mv committed fn2-core fn2-sim fn2-own) (fn2-ccp-live-drive 200000 nil prefix fn2-core fn2-sim fn2-own))
      ((unless (eq committed :complete)) (mv committed 0 0 fn2-core fn2-sim fn2-own))
      ((mv entered fn2-core) (fn2-ccp-maintenance-entry fn2-core))
      ((unless (eq entered :ok)) (mv entered 0 0 fn2-core fn2-sim fn2-own))
      ((mv published fn2-core fn2-sim fn2-own) (fn2-ccp-live-drive 400000 t 0 fn2-core fn2-sim fn2-own))
      ((unless (eq published :complete)) (mv published 0 0 fn2-core fn2-sim fn2-own))
      ((mv admitted writer suffix & fn2-core) (fn2-commit-admit-keyed 1 0 0 0 0 fn2-core))
      ((unless (eq admitted :ok)) (mv admitted 0 0 fn2-core fn2-sim fn2-own))
      (fn2-core (fn2-exec-wake writer fn2-core))
      ((mv committed fn2-core fn2-sim fn2-own) (fn2-ccp-live-drive 200000 nil suffix fn2-core fn2-sim fn2-own)))
  (mv committed prefix suffix fn2-core fn2-sim fn2-own)))

; This observation is after the actual constructor/replay path, never setup.
; Both the recovered terminal and selected source must still be current while
; issuance is frozen. The terminal includes the installation and new suffix.
(defun fn2-ccp-before-open-p (prefix suffix fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (let ((recovery (fn2-machine-kind-base *fn2-recovery-machine-kind* fn2-core)))
  (and (fn2-ccp-epoch-fence-p fn2-core)
       (eq (fn2-boot-recovered fn2-core) :ok)
       (fn2-recovery-selected-current-p recovery fn2-core)
       (= (fn2-machine-rc-base recovery fn2-core) prefix)
       (= (fn2-machine-rc-chain recovery fn2-core) suffix)
       (stobj-let ((fn2-extents (fn2-core-extents fn2-core))
                   (fn2-commit-root (fn2-core-commit-root fn2-core))
                   (fn2-checkpoint-summary (fn2-core-checkpoint-summary fn2-core))) (closed)
        (and (= (fn2-alloc-freeze-phase fn2-extents) 4) (= (fn2-alloc-epoch-begun fn2-extents) 0)
             (= (fn2-commit-root-base-ready 0 fn2-commit-root) 1)
             (= (fn2-commit-root-base-batch 0 fn2-commit-root) prefix)
             (= (fn2-commit-root-installed 0 fn2-commit-root) suffix)
             (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-applied*)
             (= (fn2-checkpoint-summary-cut-commit 0 fn2-checkpoint-summary) prefix)) closed))))

