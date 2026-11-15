; Source-only actual provider 41a2e1dcd6e347ea45da7e5b1c5e8f6ac0a1b813; never included by an ACL2 book.
; Explicit one-sector issues and exact pre-finish routing. No decode or
; cursor exposure occurs in the host event callback.
(in-package "ACL2")
(include-book "run-physical-source")
(include-book "run-physical-bound-io")
(fn2-book-layer :c)

(defun fn2-run-load-issue (c budget fn2-run-loads fn2-run-load-ops fn2-run-cursors
 fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed
 fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (declare (xargs :stobjs (fn2-run-loads fn2-run-load-ops fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 :guard (and (fn2-run-loads-wfp fn2-run-loads) (fn2-run-load-ops-wfp fn2-run-load-ops) (fn2-run-cursors-wfp fn2-run-cursors)
 (fn2-checkpoint-summary-wfp fn2-checkpoint-summary) (fn2-checkpoint-summary-sources-wfp fn2-checkpoint-summary-sources)
 (fn2-checkpoint-summary-leases-wfp fn2-checkpoint-summary-leases) (fn2-run-installed-wfp fn2-run-installed)
 (fn2-extents-wfp fn2-extents) (fn2-alloc-edges-wfp fn2-alloc-edges) (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control))))
 (cond ((not (posp budget)) (fn2-run-load-issue-mv :yield 0 0))
       ((not (fn2-run-load-sourcep c fn2-run-loads fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed)) (fn2-run-load-issue-mv :source 0 0))
       (t (fn2-run-bound-issue c budget fn2-run-loads fn2-run-load-ops fn2-run-cursors fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control))))



(fn2-run-load-frames fn2-run-load-issue
 (c budget fn2-run-loads fn2-run-load-ops fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 (fn2-run-loads fn2-run-load-ops fn2-run-cursors fn2-checkpoint-summary fn2-checkpoint-summary-sources fn2-checkpoint-summary-leases fn2-run-installed fn2-extents fn2-alloc-edges fn2-pool fn2-ops fn2-control)
 ((fn2-run-loads 3) (fn2-run-load-ops 4) (fn2-pool 5) (fn2-ops 6) (fn2-control 7) (fn2-extents 8) (fn2-alloc-edges 9)))
