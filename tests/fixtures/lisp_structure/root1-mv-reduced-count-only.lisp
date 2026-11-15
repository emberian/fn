; Output-count-only reduction control: unchanged37 inputs, 29 returned
; children. This is NOT a proposed runtime write set or a correctness claim
; about dropping children. It exercises30-value work and32-value READ limits.
(defconst *fn2-checkpoint-root1-children*
 '(fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-retained-entry fn2-checkpoint-payload fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-page fn2-checkpoint-page-verified fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths fn2-run-cache fn2-boot-config fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
(defconst *fn2-checkpoint-root1-outputs*
 '(fn2-checkpoint-root1 fn2-checkpoint-windows fn2-checkpoint-metadata fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-checkpoint-retained-entry fn2-checkpoint-payload fn2-checkpoint-semantic fn2-checkpoint-semantic-work fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-checkpoint-construction fn2-extents fn2-alloc-edges fn2-ops fn2-control fn2-checkpoint-refs fn2-checkpoint-bytes fn2-checkpoint-page fn2-checkpoint-page-verified fn2-overlays fn2-overlay-index fn2-run-installed fn2-run-builds fn2-run-writers fn2-run-restarts fn2-run-cursors fn2-run-paths))
(defmacro fn2-checkpoint-root1-mv (code)
 `(mv ,code ,@*fn2-checkpoint-root1-outputs*))
(defmacro fn2-checkpoint-root1-read-mv (code)
 `(mv ,code slot generation ,@*fn2-checkpoint-root1-outputs*))
(defmacro fn2-checkpoint-root1-read-events ()
 (let ((children *fn2-checkpoint-root1-children*)
       (outputs *fn2-checkpoint-root1-outputs*))
  `(progn
    (defun fn2-checkpoint-root1-read (budget kind owner gen ,@children)
     (declare (xargs :stobjs ,children))
     (mv :bounds 0 0 ,@outputs)))))
