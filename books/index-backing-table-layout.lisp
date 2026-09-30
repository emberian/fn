; Prepare a distinct unpublished table. Every entry is subsequently reinserted
; through the builder, so old leased table chunks are never mutated or copied
; by a flat resize. The page constructor gate remains a separate obligation.
(in-package "ACL2")
(logic)
(include-book "index-page-debt-transfer")

(defun fn-ipa-table-layout-begin (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (pages (fn-omk-at 5 builder)) (count (fn-omk-at 6 builder))
        (generation (fn-omk-at 2 builder)))
  (cond
   ((zp fuel) (mv :yield fuel fn-index-backing))
   ((not (and (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 1 builder) :table-layout)
              (fn-ibp-generation-tokenp generation) (posp pages) (natp count)
              (<= count (* 1024 pages))
              (null (fn-ibp-page-pending fn-index-backing))))
    (mv :recovery-required fuel fn-index-backing))
   (t
    (let* ((target (if (>= (+ 1 count) (* 1024 pages)) (* 2 pages) pages))
           (next (update-nth 1 :table-depth
                  (update-nth 5 target
                   (update-nth 9 nil
                    (update-nth 11 (fn-omk-at 1 generation)
                     (update-nth 18 '(:table-depth 0 1) builder))))))
           (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
     (mv :table-depth (- fuel 1) fn-index-backing))))))

; Width/depth construction is itself resumable; no INTEGER-LENGTH or loop
; hides profile-sized work in the begin action. Width is representation size,
; not a new data limit. Profile admission must fund the selected target pages.
(defun fn-ipa-table-depth-one (fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let* ((builder (fn-ibp-builder fn-index-backing))
        (cursor (fn-omk-at 18 builder)) (depth (fn-omk-at 1 cursor))
        (width (fn-omk-at 2 cursor)) (pages (fn-omk-at 5 builder)))
  (cond
   ((zp fuel) (mv :yield fuel fn-index-backing))
   ((not (and (fn-omk-widthp builder 20) (true-listp builder)
              (eq (fn-omk-at 1 builder) :table-depth)
              (eq (fn-omk-at 0 cursor) :table-depth)
              (natp depth) (posp width) (posp pages)))
    (mv :recovery-required fuel fn-index-backing))
   (t
    (let* ((done (>= width pages))
           (next (if done
                     (update-nth 1 :layout
                      (update-nth 10 depth
                       (update-nth 18 '(:page-request :table 0 nil) builder)))
                   (update-nth 18 (list :table-depth (+ 1 depth) (* 2 width)) builder)))
           (fn-index-backing (update-fn-ibp-builder next fn-index-backing)))
     (mv (if done :page-request :table-depth) (- fuel 1) fn-index-backing))))))
