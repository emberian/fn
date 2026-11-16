; B's actual pinned physical read, bound to the retained entry origin and
; exact operation generation. Short/ambiguous reads retain pins and buffers.
(in-package "ACL2")
(include-book "checkpoint-payload-state")
(include-book "checkpoint-payload-physical")
(fn2-book-layer :c)

(defmacro fn2-checkpoint-payload-issue-mv (code)
 `(mv ,code fn2-checkpoint-payload fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))

(defun fn2-checkpoint-payload-issue (budget fn2-checkpoint-payload fn2-checkpoint-retained-entry fn2-csnapshot fn2-checkpoints fn2-fields
                                    fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-checkpoint-payload fn2-checkpoint-retained-entry fn2-csnapshot fn2-checkpoints fn2-fields
                          fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
  :guard (and (fn2-checkpoint-payload-wfp fn2-checkpoint-payload) (fn2-checkpoint-retained-entry-wfp fn2-checkpoint-retained-entry)
              (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-fields-wfp fn2-fields)
              (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges) (fn2-pool-wfp fn2-pool)
              (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control))))
 (b* (((unless (and (natp budget) (< 0 budget))) (fn2-checkpoint-payload-issue-mv :yield))
      ((unless (and (fn2-checkpoint-payload-sourcep fn2-checkpoint-payload fn2-checkpoint-retained-entry fn2-csnapshot fn2-checkpoints fn2-fields)
                     (equal (fn2-checkpoint-payload-pending 0 fn2-checkpoint-payload) 0)
                     (member (fn2-checkpoint-payload-phase 0 fn2-checkpoint-payload)
                      (list *fn2-checkpoint-payload-phase-manifest-read* *fn2-checkpoint-payload-phase-block-read*))))
       (fn2-checkpoint-payload-issue-mv :source))
      (manifestp (equal (fn2-checkpoint-payload-phase 0 fn2-checkpoint-payload) *fn2-checkpoint-payload-phase-manifest-read*))
      (relative (if manifestp (floor (fn2-checkpoint-payload-manifest-position 0 fn2-checkpoint-payload) *fn2-commit-unit-bytes*) 0))
      ((unless (or (not manifestp) (< relative *fn2-storage-extent-units*)))
       (fn2-checkpoint-payload-issue-mv :manifest-geometry))
      (unit (if manifestp (+ (fn2-checkpoint-payload-source-unit 0 fn2-checkpoint-payload) relative)
              (fn2-checkpoint-payload-block-unit 0 fn2-checkpoint-payload)))
      (epoch (if manifestp (fn2-checkpoint-payload-source-epoch 0 fn2-checkpoint-payload) (fn2-checkpoint-payload-block-epoch 0 fn2-checkpoint-payload)))
      (allocation (if manifestp (fn2-checkpoint-payload-source-allocation 0 fn2-checkpoint-payload) (fn2-checkpoint-payload-block-allocation 0 fn2-checkpoint-payload)))
      (slot (if manifestp (fn2-checkpoint-payload-manifest-slot 0 fn2-checkpoint-payload) (fn2-checkpoint-payload-data-slot 0 fn2-checkpoint-payload)))
      (gen (if manifestp (fn2-checkpoint-payload-manifest-gen 0 fn2-checkpoint-payload) (fn2-checkpoint-payload-data-gen 0 fn2-checkpoint-payload)))
      (len (if manifestp *fn2-commit-unit-bytes* (fn2-checkpoint-payload-block-length 0 fn2-checkpoint-payload)))
      (kind (fn2-checkpoint-payload-owner-kind 0 fn2-checkpoint-payload))
      (owner (fn2-checkpoint-payload-owner-slot 0 fn2-checkpoint-payload))
      (generation (fn2-checkpoint-payload-owner-gen 0 fn2-checkpoint-payload))
      ((unless (and (posp len) (<= len *fn2-commit-unit-bytes*)
                     (fn2-checkpoint-source-claimedp (fn2-checkpoint-payload-candidate 0 fn2-checkpoint-payload)
                      (fn2-checkpoint-payload-checkpoint 0 fn2-checkpoint-payload) (floor unit *fn2-storage-extent-units*) epoch allocation
                      fn2-extents fn2-alloc-edges fn2-ops fn2-checkpoints)))
       (fn2-checkpoint-payload-issue-mv :retention))
      ((mv code fn2-pool) (fn2-pool-reset slot gen kind owner generation fn2-pool))
      ((unless (eq code :ok)) (fn2-checkpoint-payload-issue-mv code))
      ((mv code opslot opgen fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges)
       (fn2-block-read-children unit epoch allocation 0 len slot gen kind owner generation 0
        fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control))
      ((when (eq code :exhausted)) (fn2-checkpoint-payload-issue-mv code))
      (fn2-checkpoint-payload (fn2-checkpoint-payload-put 0 (op-slot opslot) (op-gen opgen)
       (loaded-unit (if manifestp relative (fn2-checkpoint-payload-loaded-unit 0 fn2-checkpoint-payload)))
       (pending (if (or (eq code :ok) (equal (fn2-control-stop fn2-control) 1)) 1 0))
       (phase (if (eq code :ok) (if manifestp *fn2-checkpoint-payload-phase-wait-manifest* *fn2-checkpoint-payload-phase-wait-block*)
                *fn2-checkpoint-payload-phase-uncertain*)))))
  (fn2-checkpoint-payload-issue-mv (if (eq code :ok) :issued code))))

; Exact pre-finish completion only. Decoding starts on a later worker turn,
; after the normal operation finish restored the owned input workspace.


(fn2-checkpoint-payload-preserves fn2-checkpoint-payload-issue
 (budget fn2-checkpoint-payload fn2-checkpoint-retained-entry fn2-csnapshot fn2-checkpoints fn2-fields fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 :hyps ((fn2-checkpoint-payloadp fn2-checkpoint-payload) (fn2-checkpoint-payload-wfp fn2-checkpoint-payload)
        (fn2-checkpoint-retained-entryp fn2-checkpoint-retained-entry) (fn2-checkpoint-retained-entry-wfp fn2-checkpoint-retained-entry)
        (fn2-csnapshotp fn2-csnapshot) (fn2-csnapshot-wfp fn2-csnapshot)
        (fn2-checkpointsp fn2-checkpoints) (fn2-checkpoints-wfp fn2-checkpoints)
        (fn2-fieldsp fn2-fields) (fn2-fields-wfp fn2-fields)
        (fn2-extentsp fn2-extents) (fn2-extents-wfp fn2-extents)
        (fn2-alloc-edgesp fn2-alloc-edges) (fn2-alloc-edges-wfp fn2-alloc-edges)
        (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
        (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
        (fn2-controlp fn2-control) (fn2-control-wfp fn2-control))
 :specs (("-CHECKPOINT-PAYLOAD-TYPE" fn2-checkpoint-payloadp 1)
         ("-CHECKPOINT-PAYLOAD-WFP" fn2-checkpoint-payload-wfp 1)
         ("-CHECKPOINT-PAYLOAD-ROWS" fn2-checkpoint-payload-rows 1 :frame fn2-checkpoint-payload)
         ("-POOL-TYPE" fn2-poolp 2)
         ("-POOL-WFP" fn2-pool-wfp 2)
         ("-POOL-ROWS" fn2-pool-rows 2 :frame fn2-pool)
         ("-OPS-TYPE" fn2-opsp 3)
         ("-OPS-WFP" fn2-ops-wfp 3)
         ("-OPS-ROWS" fn2-ops-rows 3 :frame fn2-ops)
         ("-CONTROL-TYPE" fn2-controlp 4)
         ("-CONTROL-WFP" fn2-control-wfp 4)
         ("-CONTROL-ROWS" fn2-control-rows 4 :frame fn2-control)
         ("-EXTENTS-TYPE" fn2-extentsp 5)
         ("-EXTENTS-WFP" fn2-extents-wfp 5)
         ("-EXTENTS-ROWS" fn2-extents-rows 5 :frame fn2-extents)
         ("-ALLOC-EDGES-TYPE" fn2-alloc-edgesp 6)
         ("-ALLOC-EDGES-WFP" fn2-alloc-edges-wfp 6)
         ("-ALLOC-EDGES-ROWS" fn2-alloc-edges-rows 6 :frame fn2-alloc-edges)))



; defcorechild's prefinish extension returns every enlisted child. Only the
; actual payload harvest mutates state; the provenance children pass through
; unchanged. No operation identity is reconstructed from an actor observer.
