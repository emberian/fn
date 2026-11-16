; One HELD-cut compaction continuation. Source count bounds profile resources;
; it never bounds entries, output pages or the number of resumed source scans.
(in-package "ACL2")
(include-book "checkpoint-metadata-source")
(include-book "checkpoint-build-state")
(fn2-book-layer :c)

; The C assembly supplies these actual codec-derived widths. Working geometry
; stays below the assembly and reserves the canonical page representation bound.
(assert-event (<= *fn2-run-layout-max-key-octets* *fn2-format-page-size*))
(assert-event (<= *fn2-run-layout-max-entry-bytes* *fn2-format-page-size*))

(defcolumns fn2-checkpoint-compaction
 ((phase (:enum fn2-checkpoint-compaction-phase
   (:idle :schema :empty-seek :empty-end :sources :seek :compare :equal-lower :source-end :copy :park :selected :retention :append :lower-copy :schema-done :done :uncertain)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (candidate :u32) (overlay-rows :u32) (run-rows :u32)
  (scan-kind :u8) (scan-row :u32)
  (schema :u60) (schema-found :bool) (has-last-schema :bool) (last-schema :u60)
  (empty-headers :u60) (schema-open :bool) (output-rank :u60) (source-kind :u8) (source-row :u32) (source-order :u60)
  (best :bool) (best-kind :u8) (best-row :u32) (best-order :u60)
  (lower-round :u60) (has-lower :bool) (lower-slot :u32) (lower-gen :u60)
  (configured :bool) (cursor :u32) (reader-base :u32)
  (entry-base :u32) (lower-base :u32) (input-base :u32)
  (best-slot :u32) (best-gen :u60)
  (source-started :bool) (source-position :u32)
  (source-okind :u8) (source-oslot :u32) (source-ogen :u60)
  (copy-field :u32) (copy-offset :u32) (copy-end :u32)))

; The cut tuple survives publication/retirement. Construction additionally
; requires BUILDING/await-roots, so this split cannot authorize source reads
; from a published carrier merely because its old tuple still matches.
(defun fn2-checkpoint-compaction-cut-ownerp
 (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction)
             (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
             (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays)
             (fn2-run-installed-wfp fn2-run-installed))))
 (and (< 0 (fn2-checkpoint-compaction-rows fn2-checkpoint-compaction))
      (< 0 (fn2-checkpoint-build-rows fn2-checkpoint-build))
      (not (equal (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction)
                  *fn2-checkpoint-compaction-phase-idle*))
      (fn2-checkpoint-build-ownerp
       (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-kind 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-slot 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-gen 0 fn2-checkpoint-compaction)
       fn2-checkpoint-build fn2-csnapshot)
      (equal (fn2-checkpoint-compaction-candidate 0 fn2-checkpoint-compaction)
             (fn2-checkpoint-build-candidate 0 fn2-checkpoint-build))
      (fn2-checkpoint-builder-claimp
       (fn2-checkpoint-compaction-candidate 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-kind 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-slot 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-gen 0 fn2-checkpoint-compaction) fn2-checkpoints)
      (equal (fn2-checkpoint-compaction-overlay-rows 0 fn2-checkpoint-compaction) (fn2-overlays-rows fn2-overlays))
      (equal (fn2-checkpoint-compaction-run-rows 0 fn2-checkpoint-compaction) (fn2-run-installed-rows fn2-run-installed))))

(defun fn2-checkpoint-compaction-ownerp
 (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction)
             (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
             (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays)
             (fn2-run-installed-wfp fn2-run-installed))))
 (and (fn2-checkpoint-compaction-cut-ownerp
       fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
      (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-await-roots*)
      (fn2-checkpoint-builder-ownerp
       (fn2-checkpoint-compaction-candidate 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-kind 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-slot 0 fn2-checkpoint-compaction)
       (fn2-checkpoint-compaction-owner-gen 0 fn2-checkpoint-compaction) fn2-checkpoints)))

(defun fn2-checkpoint-compaction-begin
 (token kind owner generation fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints fn2-overlays fn2-run-installed)
 :guard (and (fn2-checkpoint-compaction-wfp fn2-checkpoint-compaction)
             (fn2-checkpoint-build-wfp fn2-checkpoint-build) (fn2-csnapshot-wfp fn2-csnapshot)
             (fn2-checkpoints-wfp fn2-checkpoints) (fn2-overlays-wfp fn2-overlays)
             (fn2-run-installed-wfp fn2-run-installed))))
 (b* (((unless (and (< 0 (fn2-checkpoint-compaction-rows fn2-checkpoint-compaction))
                    (< 0 (fn2-checkpoint-build-rows fn2-checkpoint-build))
                    (fn2-checkpoint-build-ownerp token kind owner generation fn2-checkpoint-build fn2-csnapshot)
                    (equal (fn2-checkpoint-build-phase 0 fn2-checkpoint-build) *fn2-checkpoint-build-phase-await-roots*)
                    (or (equal (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-idle*)
                        (and (equal (fn2-checkpoint-compaction-phase 0 fn2-checkpoint-compaction) *fn2-checkpoint-compaction-phase-done*)
                             (not (equal token (fn2-checkpoint-compaction-token 0 fn2-checkpoint-compaction)))))
                    (unsigned-byte-p 32 (fn2-overlays-rows fn2-overlays))
                    (unsigned-byte-p 32 (fn2-run-installed-rows fn2-run-installed))))
       (mv :snapshot fn2-checkpoint-compaction))
      (c (fn2-checkpoint-build-candidate 0 fn2-checkpoint-build))
      ((unless (fn2-checkpoint-builder-ownerp c token kind owner generation fn2-checkpoints))
       (mv :candidate fn2-checkpoint-compaction))
      (fn2-checkpoint-compaction (fn2-checkpoint-compaction-put 0
       (phase *fn2-checkpoint-compaction-phase-schema*) (token token)
       (owner-kind kind) (owner-slot owner) (owner-gen generation) (candidate c)
       (overlay-rows (fn2-overlays-rows fn2-overlays)) (run-rows (fn2-run-installed-rows fn2-run-installed))
       (scan-kind 0) (scan-row 0) (schema-found 0) (has-last-schema 0)
       (empty-headers 0) (schema-open 0) (output-rank 0) (lower-round 0) (configured 0) (best 0) (has-lower 0) (source-started 0) (copy-field 0) (copy-offset 0) (copy-end 0))))
  (mv :more fn2-checkpoint-compaction)))
