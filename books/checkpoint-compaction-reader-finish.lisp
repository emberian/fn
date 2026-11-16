; Actual compaction terminal authority; identical canonical detach mutation.
(in-package "ACL2")
(include-book "checkpoint-compaction-production")
(include-book "checkpoint-source-loader")
(fn2-book-layer :c)

(defun fn2-checkpoint-compaction-reader-finish (token kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot
 fn2-checkpoint-metadata fn2-checkpoint-compaction fn2-checkpoint-metadata-manifest fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-checkpoint-build fn2-checkpoints fn2-overlays fn2-run-installed fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 (declare (xargs :stobjs (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-metadata fn2-checkpoint-compaction fn2-checkpoint-metadata-manifest
 fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-checkpoint-build fn2-checkpoints fn2-overlays fn2-run-installed fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 :guard (and (fn2-checkpoint-root1-wfp fn2-checkpoint-root1) (fn2-checkpoint-windows-wfp fn2-checkpoint-windows) (fn2-csnapshot-wfp fn2-csnapshot)
  (fn2-checkpoint-metadata-wfp fn2-checkpoint-metadata) (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction) (fn2-checkpoint-metadata-manifest-wfp fn2-checkpoint-metadata-manifest)
  (fn2-run-loads-wfp fn2-run-loads) (fn2-run-cursors-wfp fn2-run-cursors) (fn2-checkpoint-summary-wfp fn2-checkpoint-summary)
  (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-pool-wfp fn2-pool) (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed) (fn2-checkpoint-predecessors-wfp fn2-checkpoint-predecessors) (fn2-checkpoint-predecessor-control-wfp fn2-checkpoint-predecessor-control))))
 (b* (((unless (and (fn2-checkpoint-root1-ownerp token kind owner gen fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot)
                    (< 0 (fn2-checkpoint-metadata-rows fn2-checkpoint-metadata)) (< 0 (fn2-checkpoint-compaction-rows fn2-checkpoint-compaction))
                    (< 0 (fn2-checkpoint-metadata-manifest-rows fn2-checkpoint-metadata-manifest))
                    (equal (fn2-checkpoint-root1-phase 0 fn2-checkpoint-root1) *fn2-checkpoint-root1-phase-complete*)
                    (fn2-checkpoint-compaction-produced-p fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
                    (equal (fn2-checkpoint-metadata-held 0 fn2-checkpoint-metadata) 0)
                    (equal (fn2-checkpoint-metadata-manifest-phase 0 fn2-checkpoint-metadata-manifest) *fn2-checkpoint-metadata-manifest-phase-complete*)
                    (equal (fn2-csnapshot-complete 0 fn2-csnapshot) 1)))
       (fn2-checkpoint-source-reader-detach-mv :source))
      ((when (fn2-checkpoint-source-reader-detachedp fn2-run-loads fn2-run-cursors fn2-checkpoint-summary-leases))
       (fn2-checkpoint-source-reader-detach-mv :ok)))
  (fn2-checkpoint-source-reader-detach-owned-body)))
(fn2-run-load-frames fn2-checkpoint-compaction-reader-finish
 (token kind
       owner
       gen
       fn2-checkpoint-root1
       fn2-checkpoint-windows
       fn2-csnapshot
       fn2-checkpoint-metadata
       fn2-checkpoint-compaction
       fn2-checkpoint-metadata-manifest
       fn2-run-loads
       fn2-run-cursors
       fn2-checkpoint-summary
       fn2-checkpoint-summary-leases
       fn2-pool
       fn2-checkpoint-build
       fn2-checkpoints
       fn2-overlays
       fn2-run-installed
       fn2-checkpoint-predecessors
       fn2-checkpoint-predecessor-control)
 (fn2-checkpoint-root1 fn2-checkpoint-windows fn2-csnapshot fn2-checkpoint-metadata fn2-checkpoint-compaction fn2-checkpoint-metadata-manifest fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-leases fn2-pool fn2-checkpoint-build fn2-checkpoints fn2-overlays fn2-run-installed fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 ((fn2-run-loads 1) (fn2-run-cursors 2) (fn2-checkpoint-summary 3) (fn2-checkpoint-summary-leases 4)))
