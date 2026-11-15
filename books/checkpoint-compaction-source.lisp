; Raw row traversal of the actual HELD source set. Selection of a next key
; repeatedly visits this set; the active cursor count does not cap its size.
(in-package "ACL2")
(include-book "checkpoint-compaction-state")
(fn2-book-layer :c)

(defun fn2-checkpoint-compaction-source-tuple (kind row fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-overlays fn2-run-installed)
 :guard (and (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed))))
 (cond ((and (equal kind 0) (fn2-checkpoint-source-overlayp row fn2-overlays))
        (mv :ok (fn2-overlays-schema row fn2-overlays) (fn2-overlays-seq row fn2-overlays)))
       ((and (equal kind 1) (fn2-checkpoint-source-runp row fn2-run-installed))
        (mv :ok (fn2-run-installed-schema row fn2-run-installed) (fn2-run-installed-run row fn2-run-installed)))
       (t (mv :absent 0 0))))

; A candidate source is still the exact live source selected from this cut.
; Physical page identity/hash authentication is the existing cursor loader's
; duty; this predicate supplies no substitute physical readiness assertion.
(defun fn2-checkpoint-compaction-current-source-p
 (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction)
             (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
             (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays)
             (fn2-run-installed-wfp fn2-run-installed))))
 (and (fn2-checkpoint-compaction-ownerp fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
      (member (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction)
       (list *fn2-checkpoint-compaction-phase-seek* *fn2-checkpoint-compaction-phase-compare* *fn2-checkpoint-compaction-phase-copy*))
      (mv-let (code schema order)
       (fn2-checkpoint-compaction-source-tuple
        (fn2-checkpoint-compaction-source-kind 0 fn2-checkpoint-compaction)
        (fn2-checkpoint-compaction-source-row 0 fn2-checkpoint-compaction) fn2-overlays fn2-run-installed)
       (and (eq code :ok)
            (equal schema (fn2-checkpoint-compaction-schema 0 fn2-checkpoint-compaction))
            (equal order (fn2-checkpoint-compaction-source-order 0 fn2-checkpoint-compaction))))))

; One inspected row or one table-boundary transition per positive grant.
; Schema completion is derived from the full raw scan, never a member count.
; A matching source suspends in SEEK; only the actual merge continuation may
; return to SOURCES after seek/compare/rehome has consumed its authenticated view.
(defun fn2-checkpoint-compaction-source-step
 (budget fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction)
             (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
             (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays)
             (fn2-run-installed-wfp fn2-run-installed))))
 (b* (((unless (posp budget)) (mv :yield fn2-checkpoint-compaction))
      ((unless (fn2-checkpoint-compaction-ownerp fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed))
       (mv :snapshot fn2-checkpoint-compaction))
      (phase (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction))
      ((unless (member phase (list *fn2-checkpoint-compaction-phase-schema* *fn2-checkpoint-compaction-phase-sources*)))
       (mv :phase fn2-checkpoint-compaction))
      (kind (fn2-checkpoint-compaction-scan-kind 0 fn2-checkpoint-compaction))
      (row (fn2-checkpoint-compaction-scan-row 0 fn2-checkpoint-compaction))
      ((unless (<= kind 1)) (mv :invariant fn2-checkpoint-compaction))
      (limit (if (equal kind 0) (fn2-overlays-rows fn2-overlays) (fn2-run-installed-rows fn2-run-installed)))
      ((unless (<= row limit)) (mv :invariant fn2-checkpoint-compaction))
      ((when (equal row limit))
       (cond
        ((equal kind 0)
         (let ((fn2-checkpoint-compaction (fn2-checkpoint-compaction-put 0 (scan-kind 1) (scan-row 0))))
          (mv :more fn2-checkpoint-compaction)))
        ((equal phase *fn2-checkpoint-compaction-phase-schema*)
         (if (equal (fn2-checkpoint-compaction-schema-found 0 fn2-checkpoint-compaction) 0)
          (let ((fn2-checkpoint-compaction (fn2-checkpoint-compaction-set-phase 0 *fn2-checkpoint-compaction-phase-done* fn2-checkpoint-compaction)))
           (mv :done fn2-checkpoint-compaction))
          (let ((fn2-checkpoint-compaction (fn2-checkpoint-compaction-put 0
           (phase *fn2-checkpoint-compaction-phase-sources*) (scan-kind 0) (scan-row 0) (best 0) (has-lower 0))))
           (mv :schema fn2-checkpoint-compaction))))
        (t (let ((fn2-checkpoint-compaction (fn2-checkpoint-compaction-set-phase 0
             (if (equal (fn2-checkpoint-compaction-best 0 fn2-checkpoint-compaction) 0)
              *fn2-checkpoint-compaction-phase-schema-done* *fn2-checkpoint-compaction-phase-selected*) fn2-checkpoint-compaction)))
             (mv :scan-complete fn2-checkpoint-compaction)))))
      ((unless (unsigned-byte-p 32 (+ 1 row))) (mv :exhausted fn2-checkpoint-compaction))
      ((mv code schema order) (fn2-checkpoint-compaction-source-tuple kind row fn2-overlays fn2-run-installed))
      (fn2-checkpoint-compaction (fn2-checkpoint-compaction-set-scan-row 0 (+ 1 row) fn2-checkpoint-compaction))
      ((unless (eq code :ok)) (mv :more fn2-checkpoint-compaction))
      ((when (equal phase *fn2-checkpoint-compaction-phase-schema*))
       (let ((fn2-checkpoint-compaction
        (if (and (or (equal (fn2-checkpoint-compaction-has-last-schema 0 fn2-checkpoint-compaction) 0)
                     (< (fn2-checkpoint-compaction-last-schema 0 fn2-checkpoint-compaction) schema))
                 (or (equal (fn2-checkpoint-compaction-schema-found 0 fn2-checkpoint-compaction) 0)
                     (< schema (fn2-checkpoint-compaction-schema 0 fn2-checkpoint-compaction))))
         (fn2-checkpoint-compaction-put 0 (schema schema) (schema-found 1)) fn2-checkpoint-compaction)))
        (mv :more fn2-checkpoint-compaction)))
      ((unless (equal schema (fn2-checkpoint-compaction-schema 0 fn2-checkpoint-compaction)))
       (mv :more fn2-checkpoint-compaction))
      (fn2-checkpoint-compaction (fn2-checkpoint-compaction-put 0
       (phase *fn2-checkpoint-compaction-phase-seek*) (source-kind kind) (source-row row) (source-order order))))
  (mv :source fn2-checkpoint-compaction)))
