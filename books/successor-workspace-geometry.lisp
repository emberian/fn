; Pure layout arithmetic shared by allocation admission and C's static schema
; inventory. A guard reservation is not an entry write footprint.
(in-package "ACL2")
(include-book "format-base")
(fn2-book-layer :b)
(defun fn2-successor-block-fields (fields values)
 (declare (xargs :guard (and (natp fields) (natp values))))
 (+ (* 3 (nfix fields)) (nfix values) 1))
(defconst *fn2-successor-post-fixed-slots* 8)
(defconst *fn2-successor-post-slots* 29)
(defconst *fn2-successor-post-groups*
 (floor (- *fn2-successor-post-slots* *fn2-successor-post-fixed-slots*) 3))
;; One current ARTICLE version comparison and replacement, plus the report
;; and count change for each accepted placement. The shared-group case
;; consumes one of its existing filing slots for the combined count fold.
(defconst *fn2-successor-withdrawal-slots* (+ 2 (* 2 *fn2-successor-post-groups*)))
(defconst *fn2-successor-scalar-mask-width* 32)

(defun fn2-successor-required-fields (fields values slots entry-guard reader-fields)
 (declare (xargs :guard (and (natp fields) (natp values) (natp slots) (natp entry-guard) (natp reader-fields))))
 (let ((block (fn2-successor-block-fields fields values)))
  (max (+ (* (nfix slots) block) 4 (nfix entry-guard) (nfix reader-fields))
       (+ (* (nfix (- (nfix slots) 1)) block) (nfix entry-guard)))))
(defun fn2-successor-scratch-bytes (octets)
 (declare (xargs :guard (natp octets)))
 (* *fn2-format-sector-size* (max 1 (ceiling (nfix octets) *fn2-format-sector-size*))))
(defthm fn2-successor-block-fields-covers-regions
 (implies (and (natp fields) (natp values))
  (and (<= fields (* 2 fields))
       (<= (* 2 fields) (* 3 fields))
       (< (+ (* 3 fields) values) (fn2-successor-block-fields fields values))))
 :hints (("Goal" :in-theory (enable fn2-successor-block-fields))))
