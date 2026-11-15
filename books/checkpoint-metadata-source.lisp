; Ordered enumeration of the actual held C set. Repeated bounded row scans
; cost O(N^2) comparisons for N resident sources; no source list is allocated.
(in-package "ACL2")
(include-book "checkpoint-construction-owner")
(include-book "runs-served")
(fn2-book-layer :c)

(defcolumns fn2-checkpoint-source
 ((phase (:enum fn2-checkpoint-source-phase (:idle :scan :selected :done :uncertain)))
  (token :u60) (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (scan-kind :u8) (scan-row :u32) (found :bool) (has-last :bool) (rank :u60)
  (schema :u60) (kind :u8) (order :u60) (row :u32)
  (last-schema :u60) (last-kind :u8) (last-order :u60) (last-row :u32)))

; Kinds follow the held reader API: overlay0, installed-run1. The served
; range fold prefers overlays, then greater SEQ/RUN. On an equal order it
; retains the first source visited by range-pick: the smaller resident row.
; Thus reverse row order is the increasing-run-key order for tied sources.
(defun fn2-checkpoint-source-beforep (schema kind order row s2 k2 o2 r2)
 (declare (xargs :guard (and (natp schema) (natp kind) (natp order) (natp row)
                            (natp s2) (natp k2) (natp o2) (natp r2))))
 (or (< schema s2)
     (and (equal schema s2)
          (or (< k2 kind)
              (and (equal kind k2)
                   (or (< order o2) (and (equal order o2) (< r2 row))))))))

(defun fn2-checkpoint-source-ownerp (fn2-checkpoint-source fn2-csnapshot)
 (declare (xargs :stobjs (fn2-checkpoint-source fn2-csnapshot)
  :guard (and (fn2-checkpoint-source-wfp fn2-checkpoint-source) (fn2-csnapshot-wfp fn2-csnapshot))))
 (and (< 0 (fn2-checkpoint-source-rows fn2-checkpoint-source))
      (fn2-csnapshot-ownerp (fn2-checkpoint-source-token 0 fn2-checkpoint-source)
       (fn2-checkpoint-source-owner-kind 0 fn2-checkpoint-source)
       (fn2-checkpoint-source-owner-slot 0 fn2-checkpoint-source)
       (fn2-checkpoint-source-owner-gen 0 fn2-checkpoint-source) fn2-csnapshot)
      (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)))

(defun fn2-checkpoint-source-begin (token kind slot gen fn2-checkpoint-source fn2-csnapshot)
 (declare (xargs :stobjs (fn2-checkpoint-source fn2-csnapshot)
  :guard (and (fn2-checkpoint-source-wfp fn2-checkpoint-source) (fn2-csnapshot-wfp fn2-csnapshot))))
 (b* (((unless (and (< 0 (fn2-checkpoint-source-rows fn2-checkpoint-source))
                     (fn2-csnapshot-ownerp token kind slot gen fn2-csnapshot)
                     (equal (fn2-csnapshot-phase 0 fn2-csnapshot) *fn2-csnapshot-phase-held*)
                     (or (equal (fn2-checkpoint-source-phase 0 fn2-checkpoint-source)
                                *fn2-checkpoint-source-phase-idle*)
                         (and (equal (fn2-checkpoint-source-phase 0 fn2-checkpoint-source)
                                     *fn2-checkpoint-source-phase-done*)
                              (not (equal token (fn2-checkpoint-source-token 0 fn2-checkpoint-source)))))))
       (mv :snapshot fn2-checkpoint-source))
      (fn2-checkpoint-source (fn2-checkpoint-source-put 0
       (phase *fn2-checkpoint-source-phase-scan*) (token token) (owner-kind kind) (owner-slot slot) (owner-gen gen)
       (scan-kind 0) (scan-row 0) (found 0) (has-last 0) (rank 0))))
  (mv :ok fn2-checkpoint-source)))

(defun fn2-checkpoint-source-consider (schema kind order row fn2-checkpoint-source)
 (declare (xargs :stobjs fn2-checkpoint-source
  :guard (and (fn2-checkpoint-source-wfp fn2-checkpoint-source)
              (< 0 (fn2-checkpoint-source-rows fn2-checkpoint-source))
              (unsigned-byte-p 60 schema) (unsigned-byte-p 8 kind) (unsigned-byte-p 60 order) (unsigned-byte-p 32 row))))
 (if (and (or (equal (fn2-checkpoint-source-has-last 0 fn2-checkpoint-source) 0)
              (fn2-checkpoint-source-beforep
               (fn2-checkpoint-source-last-schema 0 fn2-checkpoint-source)
               (fn2-checkpoint-source-last-kind 0 fn2-checkpoint-source)
               (fn2-checkpoint-source-last-order 0 fn2-checkpoint-source)
               (fn2-checkpoint-source-last-row 0 fn2-checkpoint-source) schema kind order row))
          (or (equal (fn2-checkpoint-source-found 0 fn2-checkpoint-source) 0)
              (fn2-checkpoint-source-beforep schema kind order row
               (fn2-checkpoint-source-schema 0 fn2-checkpoint-source)
               (fn2-checkpoint-source-kind 0 fn2-checkpoint-source)
               (fn2-checkpoint-source-order 0 fn2-checkpoint-source)
               (fn2-checkpoint-source-row 0 fn2-checkpoint-source))))
     (fn2-checkpoint-source-put 0 (found 1) (schema schema) (kind kind) (order order) (row row))
   fn2-checkpoint-source))

; One row per call, including dead and empty rows (which add no entries). DONE comes only after the complete
; second scan finds no source beyond the last emitted tuple. It never follows
; from a caller-supplied count or a generic ready/complete operation.
 ; Shared actual source eligibility: capacity admission and ordered selection
; count precisely the same nonempty source rows at the held cut.
(defun fn2-checkpoint-source-overlay-p (row fn2-overlays)
 (declare (xargs :stobjs fn2-overlays :guard (fn2-overlays-wfp fn2-overlays)))
 (and (natp row) (< row (fn2-overlays-rows fn2-overlays))
      (posp (fn2-overlays-count row fn2-overlays))
      (member-equal (fn2-overlays-phase row fn2-overlays)
       (list *fn2-overlay-phase-active* *fn2-overlay-phase-frozen*))))
(defun fn2-checkpoint-source-run-p (row fn2-run-installed)
 (declare (xargs :stobjs fn2-run-installed :guard (fn2-run-installed-wfp fn2-run-installed)))
 (and (natp row) (< row (fn2-run-installed-rows fn2-run-installed))
      (posp (fn2-run-installed-entries row fn2-run-installed))
      (= (fn2-run-installed-state row fn2-run-installed) *fn2-run-installed-state-live*)))

(defun fn2-checkpoint-source-step (budget fn2-checkpoint-source fn2-csnapshot fn2-overlays fn2-run-installed)
 (declare (xargs :stobjs (fn2-checkpoint-source fn2-csnapshot fn2-overlays fn2-run-installed)
  :guard (and (fn2-checkpoint-source-wfp fn2-checkpoint-source) (fn2-csnapshot-wfp fn2-csnapshot)
              (fn2-overlays-wfp fn2-overlays) (fn2-run-installed-wfp fn2-run-installed))))
 (b* (((unless (and (natp budget) (< 0 budget))) (mv :yield fn2-checkpoint-source))
      ((unless (and (fn2-checkpoint-source-ownerp fn2-checkpoint-source fn2-csnapshot)
                     (equal (fn2-checkpoint-source-phase 0 fn2-checkpoint-source)
                            *fn2-checkpoint-source-phase-scan*)))
       (mv :snapshot fn2-checkpoint-source))
      (kind (fn2-checkpoint-source-scan-kind 0 fn2-checkpoint-source))
      (row (fn2-checkpoint-source-scan-row 0 fn2-checkpoint-source)))
  (cond
   ((and (equal kind 0) (< row (fn2-overlays-rows fn2-overlays)))
    (if (not (unsigned-byte-p 32 (+ 1 row))) (mv :bounds fn2-checkpoint-source)
     (let* ((fn2-checkpoint-source
             (if (fn2-checkpoint-source-overlay-p row fn2-overlays)
                 (fn2-checkpoint-source-consider (fn2-overlays-schema row fn2-overlays) 0
                  (fn2-overlays-seq row fn2-overlays) row fn2-checkpoint-source) fn2-checkpoint-source))
            (fn2-checkpoint-source (fn2-checkpoint-source-set-scan-row 0 (+ 1 row) fn2-checkpoint-source)))
      (mv :more fn2-checkpoint-source))))
   ((equal kind 0)
    (let ((fn2-checkpoint-source (fn2-checkpoint-source-put 0 (scan-kind 1) (scan-row 0))))
     (mv :more fn2-checkpoint-source)))
   ((< row (fn2-run-installed-rows fn2-run-installed))
    (if (not (unsigned-byte-p 32 (+ 1 row))) (mv :bounds fn2-checkpoint-source)
     (let* ((fn2-checkpoint-source
             (if (fn2-checkpoint-source-run-p row fn2-run-installed)
                 (fn2-checkpoint-source-consider (fn2-run-installed-schema row fn2-run-installed) 1
                  (fn2-run-installed-run row fn2-run-installed) row fn2-checkpoint-source) fn2-checkpoint-source))
            (fn2-checkpoint-source (fn2-checkpoint-source-set-scan-row 0 (+ 1 row) fn2-checkpoint-source)))
      (mv :more fn2-checkpoint-source))))
   ((equal (fn2-checkpoint-source-found 0 fn2-checkpoint-source) 0)
    (let ((fn2-checkpoint-source (fn2-checkpoint-source-set-phase 0 *fn2-checkpoint-source-phase-done* fn2-checkpoint-source)))
     (mv :done fn2-checkpoint-source)))
   ((not (unsigned-byte-p 60 (+ 1 (fn2-checkpoint-source-rank 0 fn2-checkpoint-source))))
    (mv :exhausted fn2-checkpoint-source))
   (t (let ((fn2-checkpoint-source (fn2-checkpoint-source-put 0
        (phase *fn2-checkpoint-source-phase-selected*) (has-last 1)
        (rank (+ 1 (fn2-checkpoint-source-rank 0 fn2-checkpoint-source)))
        (last-schema (fn2-checkpoint-source-schema 0 fn2-checkpoint-source))
        (last-kind (fn2-checkpoint-source-kind 0 fn2-checkpoint-source))
        (last-order (fn2-checkpoint-source-order 0 fn2-checkpoint-source))
        (last-row (fn2-checkpoint-source-row 0 fn2-checkpoint-source)))))
       (mv :source fn2-checkpoint-source))))))

(defun fn2-checkpoint-source-selectedp (token kind slot gen source-kind row fn2-checkpoint-source fn2-csnapshot)
 (declare (xargs :stobjs (fn2-checkpoint-source fn2-csnapshot)
  :guard (and (fn2-checkpoint-source-wfp fn2-checkpoint-source) (fn2-csnapshot-wfp fn2-csnapshot))))
 (and (fn2-checkpoint-source-ownerp fn2-checkpoint-source fn2-csnapshot)
      (equal (fn2-checkpoint-source-phase 0 fn2-checkpoint-source) *fn2-checkpoint-source-phase-selected*)
      (equal (fn2-checkpoint-source-token 0 fn2-checkpoint-source) token)
      (equal (fn2-checkpoint-source-owner-kind 0 fn2-checkpoint-source) kind)
      (equal (fn2-checkpoint-source-owner-slot 0 fn2-checkpoint-source) slot)
      (equal (fn2-checkpoint-source-owner-gen 0 fn2-checkpoint-source) gen)
      (equal (fn2-checkpoint-source-kind 0 fn2-checkpoint-source) source-kind)
      (equal (fn2-checkpoint-source-row 0 fn2-checkpoint-source) row)
      (posp (fn2-checkpoint-source-rank 0 fn2-checkpoint-source))))
