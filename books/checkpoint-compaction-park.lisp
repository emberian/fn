; Repeated source scans release the old catalog lease without releasing the
; root1-owned input page/read windows or changing their generations.
(in-package "ACL2")
(include-book "checkpoint-compaction-workspaces")
(include-book "run-physical-release")
(fn2-book-layer :c)

(defun fn2-checkpoint-compaction-park-source
 (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction) (fn2-checkpoint-root1-wfp fn2-checkpoint-root1)
 (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
 (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed)
 (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
 (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool))))
 (b* (((unless (and (fn2-checkpoint-compaction-ownerp fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
                    (fn2-checkpoint-compaction-windowsp fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-pool)
                    (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-source*)
                    (equal (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-park*)))
       (mv :source fn2-checkpoint-compaction fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
      (token (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction))
      (kind (fn2-checkpoint-compaction-owner-kind 0 fn2-checkpoint-compaction))
      (owner (fn2-checkpoint-compaction-owner-slot 0 fn2-checkpoint-compaction))
      (generation (fn2-checkpoint-compaction-owner-gen 0 fn2-checkpoint-compaction))
      ((unless (and (fn2-checkpoint-source-reader-attachedp token kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-run-loads fn2-run-cursors)
                    (fn2-checkpoint-source-reader-windowsp token kind owner generation fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-pool)
                    (equal (fn2-run-loads-rows fn2-run-loads) (fn2-checkpoint-summary-leases-rows fn2-checkpoint-summary-leases))))
       (mv :owner fn2-checkpoint-compaction fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
      (c (fn2-b-checkpoint-source-cursor-from-rows (fn2-run-loads-rows fn2-run-loads)))
      ((unless (and (member (fn2-run-loads-phase c fn2-run-loads) (list *fn2-run-load-phase-reserved* *fn2-run-load-phase-ready*))
                    (equal (fn2-run-loads-pending c fn2-run-loads) 0)))
       (mv :pending fn2-checkpoint-compaction fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
      ((mv code fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)
       (fn2-run-load-park-source-mutations))
      ((unless (eq code :ok))
       (mv code fn2-checkpoint-compaction fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases))
      (fn2-checkpoint-compaction (fn2-checkpoint-compaction-put 0
       (phase *fn2-checkpoint-compaction-phase-sources*) (source-started 0))))
  (mv :more fn2-checkpoint-compaction fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases)))
(fn2-run-load-frames fn2-checkpoint-compaction-park-source
 (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
  fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
  fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
 ((fn2-checkpoint-compaction 1) (fn2-run-loads 2) (fn2-run-cursors 3) (fn2-checkpoint-summary 4) (fn2-checkpoint-summary-leases 5)))
