; Actual preconstruction eligibility, before a working bundle or B page exists.
; The master owns the bounded prefix counters; this leaf inspects one real row.
(in-package "ACL2")
(include-book "checkpoint-metadata-source")
(fn2-book-layer :c)
(defun fn2-checkpoint-live-fit-step (token kind owner generation section row sources free
 fn2-csnapshot fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-csnapshot fn2-overlays fn2-run-installed)
 :guard (and (fn2-csnapshot-wfp fn2-csnapshot) (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed))))
 (b* (((unless (and (fn2-csnapshot-ownerp token kind owner generation fn2-csnapshot)
    (= (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)))
   (mv :owner row sources free fn2-run-installed))
  ((unless (and (member-equal section '(0 1)) (unsigned-byte-p 32 row)
    (unsigned-byte-p 60 sources) (unsigned-byte-p 32 free)))
   (mv :bounds row sources free fn2-run-installed)))
  (cond
   ((= section 0)
    (cond ((< row (fn2-overlays-rows fn2-overlays))
      (let ((next (+ sources (if (fn2-checkpoint-source-overlay-p row fn2-overlays) 1 0))))
       (if (not (and (unsigned-byte-p 32 (+ 1 row)) (unsigned-byte-p 60 next)))
        (mv :exhausted row sources free fn2-run-installed)
        (mv :more (+ 1 row) next free fn2-run-installed))))
     ((= row (fn2-overlays-rows fn2-overlays)) (mv :runs 0 sources free fn2-run-installed))
     (t (mv :bounds row sources free fn2-run-installed))))
   ((< row (fn2-run-installed-rows fn2-run-installed))
    (let ((next (+ sources (if (fn2-checkpoint-source-run-p row fn2-run-installed) 1 0)))
          (next-free (+ free (if (= (fn2-run-installed-state row fn2-run-installed) *fn2-run-installed-state-free*) 1 0))))
     (if (not (and (unsigned-byte-p 32 (+ 1 row)) (unsigned-byte-p 60 next) (unsigned-byte-p 32 next-free)))
      (mv :exhausted row sources free fn2-run-installed)
      (mv :more (+ 1 row) next next-free fn2-run-installed))))
   ((= row (fn2-run-installed-rows fn2-run-installed))
    ; No candidate, source row, pool lease or allocator obligation changes.
    ; Only a measured shortage can request compaction. Snapshot HELD still
    ; blocks its grant; the master's ordinary abort releases that exact cut.
    (let ((fn2-run-installed (update-fn2-run-installed-adoption-demand
           (if (< free sources) sources 0) fn2-run-installed)))
     (mv (if (< free sources) :no-space :fit) row sources free fn2-run-installed)))
   (t (mv :bounds row sources free fn2-run-installed)))))
(defcost fn2-checkpoint-live-fit-step-op :child fn2-checkpoint-live-fit-step :answers t
 :steps *fn2-work-stage* :bytes 0 :descriptors 0
 :tables (fn2-core-csnapshot fn2-core-overlays fn2-core-run-installed)
 :doc "Count one actual held C source/free run row before construction; shortage requests sealer pressure and ordinary cut release.")
