; Carried completed-original coverage survives actual old-row retirement.
; This does not reopen construction authority or revalidate dead source rows.
(in-package "ACL2")
(include-book "checkpoint-predecessors")
(fn2-book-layer :c)

(defun fn2-checkpoint-compaction-produced-p
 (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed
 fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed
 fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction) (fn2-checkpoint-build-wfp fn2-checkpoint-build)
 (fn2-csnapshot-wfp fn2-csnapshot) (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays)
 (fn2-run-installed-wfp fn2-run-installed) (fn2-checkpoint-predecessors-wfp fn2-checkpoint-predecessors)
 (fn2-checkpoint-predecessor-control-wfp fn2-checkpoint-predecessor-control))))
 (and (fn2-checkpoint-compaction-cut-ownerp fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
      (equal (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-done*)
      (equal (fn2-checkpoint-compaction-schema-open 0 fn2-checkpoint-compaction) 0)
      (fn2-checkpoint-predecessor-bound-p fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints
       fn2-overlays fn2-run-installed fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control)
      (member (fn2-checkpoint-predecessor-control-phase 0 fn2-checkpoint-predecessor-control)
       (list *fn2-checkpoint-predecessor-phase-complete* *fn2-checkpoint-predecessor-phase-mapping*
             *fn2-checkpoint-predecessor-phase-retiring* *fn2-checkpoint-predecessor-phase-done*))
      (equal (fn2-checkpoint-predecessor-control-completed-originals 0 fn2-checkpoint-predecessor-control)
             (fn2-checkpoint-predecessor-control-count 0 fn2-checkpoint-predecessor-control))))
