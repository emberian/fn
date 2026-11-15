; Static compaction authority adapters for the SAME physical loader. Reads
; remain a separate one-descriptor operation; no parser/hasher/writer is added.
(in-package "ACL2")
(include-book "checkpoint-compaction-source")
(include-book "checkpoint-source-loader")
(fn2-book-layer :c)

(defun fn2-checkpoint-compaction-reader-sourcep
 (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction) (fn2-checkpoint-root1-wfp fn2-checkpoint-root1)
 (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
 (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed)
 (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors))))
 (and (fn2-checkpoint-compaction-current-source-p fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
      (equal (fn2-checkpoint-compaction-configured 0 fn2-checkpoint-compaction) 1)
      (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-source*)
      (member (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction)
       (list *fn2-checkpoint-compaction-phase-seek* *fn2-checkpoint-compaction-phase-empty-seek*))
      (equal (fn2-checkpoint-compaction-source-kind 0 fn2-checkpoint-compaction) 1)
      (equal (fn2-checkpoint-compaction-source-started 0 fn2-checkpoint-compaction) 1)
      (let ((c (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction))
            (kind (fn2-checkpoint-compaction-owner-kind 0 fn2-checkpoint-compaction))
            (owner (fn2-checkpoint-compaction-owner-slot 0 fn2-checkpoint-compaction))
            (gen (fn2-checkpoint-compaction-owner-gen 0 fn2-checkpoint-compaction)))
       (and (fn2-checkpoint-source-reader-attachedp (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction) kind owner gen
             fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-run-loads fn2-run-cursors)
            (equal c (fn2-b-checkpoint-source-cursor-from-rows (fn2-run-loads-rows fn2-run-loads)))
            (fn2-checkpoint-source-cursorp c (fn2-checkpoint-compaction-source-row 0 fn2-checkpoint-compaction)
             kind owner gen fn2-run-cursors fn2-run-installed)))))

(defmacro fn2-checkpoint-compaction-reader-step-mv (code)
 `(mv ,code fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
(defun fn2-checkpoint-compaction-reader-step
 (budget fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases
 fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases
 fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction) (fn2-checkpoint-root1-wfp fn2-checkpoint-root1)
 (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
 (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed)
 (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
 (fn2-checkpoint-summary-sources-wfp fn2-checkpoint-summary-sources) (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases)
 (fn2-boot-config-wfp fn2-boot-config) (fn2-fc-wfp fn2-fc) (fn2-fc-context-wfp fn2-fc-context)
 (fn2-b3-wfp fn2-b3) (fn2-fields-wfp fn2-fields) (fn2-pool-wfp fn2-pool) (fn2-digests-wfp fn2-digests))))
 (b* (((unless (and (posp budget) (<= budget *fn2-commit-unit-bytes*))) (fn2-checkpoint-compaction-reader-step-mv :yield))
      ((unless (fn2-checkpoint-compaction-reader-sourcep fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
                 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors))
       (fn2-checkpoint-compaction-reader-step-mv :source))
      (c (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction))
      (kind (fn2-checkpoint-compaction-owner-kind 0 fn2-checkpoint-compaction))
      (owner (fn2-checkpoint-compaction-owner-slot 0 fn2-checkpoint-compaction))
      (gen (fn2-checkpoint-compaction-owner-gen 0 fn2-checkpoint-compaction))
      ((when (member (fn2-run-loads-phase c fn2-run-loads) (list *fn2-run-load-phase-reserved* *fn2-run-load-phase-ready*)))
       (b* (((mv code fn2-run-loads fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool)
             (fn2-run-load-bind c kind owner gen fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-pool)))
        (fn2-checkpoint-compaction-reader-step-mv code)))
      ((mv code fn2-run-loads fn2-run-cursors fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-run-load-step c budget fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-boot-config
        fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (fn2-checkpoint-compaction-reader-step-mv (if (eq code :ready) :more code))))

(defun fn2-checkpoint-compaction-reader-issue
 (budget fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-run-load-ops fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases
 fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
 fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-run-load-ops fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases
 fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction) (fn2-checkpoint-root1-wfp fn2-checkpoint-root1)
 (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
 (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed)
 (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-run-load-ops-wfp fn2-run-load-ops)
 (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-sources-wfp fn2-checkpoint-summary-sources)
 (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges)
 (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control))))
 (cond ((not (posp budget))
        (mv :yield 0 0 fn2-run-loads fn2-run-load-ops fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
       ((not (fn2-checkpoint-compaction-reader-sourcep fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
              fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors))
        (mv :source 0 0 fn2-run-loads fn2-run-load-ops fn2-pool fn2-ops fn2-control fn2-extents fn2-alloc-edges))
       (t (fn2-run-load-issue (fn2-checkpoint-compaction-cursor 0 fn2-checkpoint-compaction) budget fn2-run-loads fn2-run-load-ops fn2-run-cursors
           fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed
           fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control))))
(fn2-run-load-frames fn2-checkpoint-compaction-reader-step
 (budget fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
  fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases
  fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
  fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases
  fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 ((fn2-run-loads 1) (fn2-run-cursors 2) (fn2-checkpoint-summary 3) (fn2-checkpoint-summary-leases 4)
  (fn2-fc 5) (fn2-fc-context 6) (fn2-b3 7) (fn2-fields 8) (fn2-pool 9) (fn2-digests 10)))
(fn2-run-load-frames fn2-checkpoint-compaction-reader-issue
 (budget fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
  fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-run-load-ops fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases
  fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (fn2-checkpoint-compaction fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
  fn2-overlays fn2-run-installed fn2-run-loads fn2-run-cursors fn2-run-load-ops fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases
  fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 ((fn2-run-loads 3) (fn2-run-load-ops 4) (fn2-pool 5) (fn2-ops 6) (fn2-control 7) (fn2-extents 8) (fn2-alloc-edges 9)))
