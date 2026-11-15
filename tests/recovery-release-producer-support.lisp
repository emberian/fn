; Intended whole-antecedent consumer packet, SOURCE ONLY / UNEXECUTED.
; Actual image create, maintenance publication, RELEASE submission, persisted
; simulator crash, selected boot, and reread precede every packet assertion.
; The test-only catalog entry is the existing parked-owner entry: automatic
; maintenance activation is not claimed. Initial retired allocation is made
; with the real allocator and included by the actual frozen-map producer.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "checkpoint-cold-path-producer-support")
(include-book "../books/assembly-attach")

; One actor turn makes the real observer/checker boundary observable. This
; changes scheduling quantum only, not any stored-data or profile capacity.
(defconst *fn2-rrc-profile* (put-assoc-equal :aturn 1 *fn2-ccp-profile*))

(defun fn2-rrc-retired-target (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (let ((commit (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (commit)
                (+ 1 (fn2-commit-root-proposed 0 fn2-commit-root)) commit)))
  (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (code e ep allocation fn2-extents)
   (b* (((mv reserved & e ep allocation fn2-extents) (fn2-alloc-reserve fn2-extents))
        ((unless (eq reserved :ok)) (mv reserved 0 0 0 fn2-extents))
        ((mv allocated fn2-extents) (fn2-alloc-commit-allocation e ep allocation 0 0 fn2-extents))
        ((unless (eq allocated :ok)) (mv allocated e ep allocation fn2-extents))
        ((mv retired fn2-extents) (fn2-alloc-retire e ep allocation commit fn2-extents)))
    (mv retired e ep allocation fn2-extents)) (mv code e ep allocation fn2-core))))

(defun fn2-rrc-stage (kind owner generation fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-checkpoint-publication (fn2-core-checkpoint-publication fn2-core))
             (fn2-checkpoint-lifecycle (fn2-core-checkpoint-lifecycle fn2-core))
             (fn2-checkpoints (fn2-core-checkpoints fn2-core))
             (fn2-checkpoint-refs (fn2-core-checkpoint-refs fn2-core))
             (fn2-checkpoint-bytes (fn2-core-checkpoint-bytes fn2-core))
             (fn2-extents (fn2-core-extents fn2-core))
             (fn2-alloc-edges (fn2-core-alloc-edges fn2-core))
             (fn2-ops (fn2-core-ops fn2-core))
             (fn2-allocation-release (fn2-core-allocation-release fn2-core)))
  (code fn2-allocation-release)
  (fn2-allocation-release-stage kind owner generation fn2-checkpoint-publication
   fn2-checkpoint-lifecycle fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
   fn2-extents fn2-alloc-edges fn2-ops fn2-allocation-release)
  (mv code fn2-core)))

(defun fn2-rrc-persist (fuel kind owner generation batch event fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
 (b* (((mv code actual-batch actual-event fn2-core)
       (fn2-allocation-release-poll kind owner generation fn2-core))
      ((when (eq code :persisted))
       (mv (if (and (= batch actual-batch) (= event actual-event)) :persisted :identity)
           fn2-core fn2-sim fn2-own))
      ((when (or (zp fuel) (fn2-core-stopped-p fn2-core) (not (eq code :waiting))))
       (mv (list :not-persisted code) fn2-core fn2-sim fn2-own))
      ((mv status fn2-core fn2-sim fn2-own) (fn2-ccp-pump fn2-core fn2-sim fn2-own))
      ((when (eq status :failed)) (mv :failed fn2-core fn2-sim fn2-own)))
  (fn2-rrc-persist (- fuel 1) kind owner generation batch event fn2-core fn2-sim fn2-own)))

(defun fn2-rrc-submit (fuel kind owner generation fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
 (b* (((mv code batch event fn2-core)
       (fn2-allocation-release-submit kind owner generation fn2-core))
      ((when (or (eq code :submitted) (zp fuel) (fn2-core-stopped-p fn2-core)
                 (not (member-eq code '(:waiting :exhausted)))))
       (mv code batch event fn2-core fn2-sim fn2-own))
      ((mv status fn2-core fn2-sim fn2-own) (fn2-ccp-pump fn2-core fn2-sim fn2-own))
      ((when (eq status :failed)) (mv :failed batch event fn2-core fn2-sim fn2-own)))
  (fn2-rrc-submit (- fuel 1) kind owner generation fn2-core fn2-sim fn2-own)))

; Stop only after the actual replay dispatcher successfully began this RELEASE.
; Stage11 is observed, never manufactured. Both retained original-journal and
; installation-J metadata must agree before the adapter packet can enter.
(defun fn2-rrc-selected-release (fuel batch event fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil :measure (nfix fuel)))
 (b* ((id (fn2-machine-kind-base *fn2-recovery-machine-kind* fn2-core))
      (generation (fn2-machine-generation id fn2-core))
      (ready (and (= (fn2-machine-rc-commit id fn2-core) batch)
                  (= (fn2-machine-rc-stage id fn2-core) 11)
                  (fn2-rp-release-current-p id generation fn2-core)
                  (fn2-rp-release-installation-metadata-p fn2-core)
                  (stobj-let ((fn2-allocation-release (fn2-core-allocation-release fn2-core))) (same)
                   (= (fn2-allocation-release-event 0 fn2-allocation-release) event) same)))
      ((when ready) (mv :release id fn2-core fn2-sim fn2-own))
      ((when (or (zp fuel) (fn2-core-stopped-p fn2-core)
                 (eq (fn2-boot-status fn2-core) :ready)))
       (mv :missing-release id fn2-core fn2-sim fn2-own))
      ((mv status fn2-core fn2-sim fn2-own) (fn2-ccp-pump fn2-core fn2-sim fn2-own))
      ((when (eq status :failed)) (mv :failed id fn2-core fn2-sim fn2-own)))
  (fn2-rrc-selected-release (- fuel 1) batch event fn2-core fn2-sim fn2-own)))

; SAME producer prefix, ending before process death. No assertion is imported.
(defun fn2-rrc-producer (fn2-core fn2-sim fn2-own)
 (declare (xargs :stobjs (fn2-core fn2-sim fn2-own) :verify-guards nil))
 (b* ((fn2-core (fn2-init-executor *fn2-rrc-profile* :null nil fn2-core))
      (fn2-sim (fn2-sim-init 1 :none "release-connected" *fn2-rrc-profile* fn2-sim))
      (fn2-own (fn2-own-init *fn2-rrc-profile* fn2-own))
      ((mv started fn2-core) (fn2-boot-start t *fn2-ccp-image-size* fn2-core))
      ((mv created fn2-core fn2-sim fn2-own) (fn2-ccp-drive 200000 nil fn2-core fn2-sim fn2-own))
      ((unless (and (eq started :ok) (eq created :ready)))
       (mv (list :create started created) fn2-core fn2-sim fn2-own))
      ; Image executor init configures the actual protected group before
      ; foreground/bootstrap. Never substitute a configured-count flag or
      ; reconfigure after the image has started using its credits.
      ((mv release-credit & &) (fn2-release-live-credit-info fn2-core))
      ((unless (eq release-credit :ok))
       (mv (list :release-credit release-credit) fn2-core fn2-sim fn2-own))
      ((mv retired target ep allocation fn2-core) (fn2-rrc-retired-target fn2-core))
      ((unless (eq retired :ok)) (mv (list :target retired) fn2-core fn2-sim fn2-own))
      ((mv publication prefix suffix fn2-core fn2-sim fn2-own)
       (fn2-ccp-prefix-and-publication fn2-core fn2-sim fn2-own))
      ((unless (and (eq publication :complete) (posp prefix) (< prefix suffix)))
       (mv (list :publication publication) fn2-core fn2-sim fn2-own))
      (owner (fn2-machine-kind-base *fn2-checkpoint-master-kind* fn2-core))
      (generation (fn2-machine-generation owner fn2-core))
      ((mv staged fn2-core) (fn2-rrc-stage *fn2-checkpoint-master-kind* owner generation fn2-core))
      ((unless (eq staged :staged)) (mv (list :stage staged) fn2-core fn2-sim fn2-own))
      ((mv submitted batch event fn2-core fn2-sim fn2-own)
       (fn2-rrc-submit 200000 *fn2-checkpoint-master-kind* owner generation fn2-core fn2-sim fn2-own))
      ((unless (eq submitted :submitted)) (mv (list :submit submitted) fn2-core fn2-sim fn2-own))
      ((mv persisted fn2-core fn2-sim fn2-own)
       (fn2-rrc-persist 200000 *fn2-checkpoint-master-kind* owner generation batch event fn2-core fn2-sim fn2-own))
      ((unless (eq persisted :persisted)) (mv (list :persist persisted) fn2-core fn2-sim fn2-own))
      )
  (mv (list :persisted target ep allocation prefix suffix batch event)
      fn2-core fn2-sim fn2-own)))
