; P2 full-table probe cursor. This is a migration foundation, not an activated
; served reader. A candidate is only a tag match; the catalog must compare the
; exact Message-ID and carry the winning sequence until :done. No candidate
; list is materialized. The remaining fuel is returned across candidate hits.
(in-package "ACL2")
(include-book "msgid-pages-exec")

(defconst *fn-mpr-slot-quantum* (* 2 *fn-mpxt-page-slots*))

(defun fn-mpr-cursorp (cursor pages)
  (declare (xargs :guard t))
  (and (true-listp cursor) (equal (len cursor) 3)
       (natp pages) (posp pages)
       (natp (nth 0 cursor)) (< (nth 0 cursor) pages)
       (natp (nth 1 cursor)) (<= (nth 1 cursor) pages)
       (natp (nth 2 cursor)) (< (nth 2 cursor) *fn-mpxt-page-slots*)))

(defun fn-mpr-start (tag fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (natp tag)))
  (let ((pages (fn-mpxt-pages fn-mpxt)))
    (and (posp pages) (list (fn-mpx-home tag pages) pages 0))))

(defun fn-mpr-advance (cursor pages)
  (declare (xargs :guard (fn-mpr-cursorp cursor pages)))
  (let ((page (nth 0 cursor)) (left (nth 1 cursor)) (slot (nth 2 cursor)))
    (if (equal left 0)
        cursor
      (if (< (+ 1 slot) *fn-mpxt-page-slots*)
          (list page left (+ 1 slot))
        (list (fn-mpxt-next page pages) (- left 1) 0)))))

(defthm fn-mpr-advance-preserves-cursorp
  (implies (fn-mpr-cursorp cursor pages)
           (fn-mpr-cursorp (fn-mpr-advance cursor pages) pages))
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp fn-mpr-advance))))

; One tick consumes at most two pages' worth of slots. :done on an empty
; slot is sound only under the maintained no-hole/probe-coverage invariant;
; that invariant and the actual placement/growth migration are still owed.
(defun fn-mpr-next (tag cursor fuel fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix fuel)
                  :guard (and (natp tag) (fn-mpxt-wfp fn-mpxt)
                              (fn-mpr-cursorp cursor (fn-mpxt-pages fn-mpxt))
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :done cursor nil fuel))
        ((zp fuel) (mv :yield cursor nil 0))
        (t
         (let* ((page (nth 0 cursor)) (slot (nth 2 cursor))
                (found-tag (fn-mpxt-tag-at page slot fn-mpxt))
                (next (fn-mpr-advance cursor (fn-mpxt-pages fn-mpxt))))
           (cond ((equal found-tag 0) (mv :done cursor nil (- fuel 1)))
                 ((equal found-tag tag)
                  (let ((encoded-seq (fn-mpxt-seq-at page slot fn-mpxt)))
                    (if (zp encoded-seq)
                        (mv :recovery-required cursor nil (- fuel 1))
                      (mv :candidate next (- encoded-seq 1) (- fuel 1)))))
                 (t (fn-mpr-next tag next (- fuel 1) fn-mpxt)))))))

(verify-guards fn-mpr-next
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))

; The same circular slot order for placement. :full means the funded table
; has wrapped, rather than that a two-page scheduling quantum was exhausted.
; The caller must bind this cursor to one table generation while it yields.
(defun fn-mpr-place (tag seq cursor fuel fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix fuel)
                  :guard (and (posp tag) (< tag *fn-mpxt-word-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*)
                              (fn-mpxt-wfp fn-mpxt)
                              (fn-mpr-cursorp cursor (fn-mpxt-pages fn-mpxt))
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :full cursor fuel fn-mpxt))
        ((zp fuel) (mv :yield cursor 0 fn-mpxt))
        (t
         (let* ((page (nth 0 cursor)) (slot (nth 2 cursor))
                (next (fn-mpr-advance cursor (fn-mpxt-pages fn-mpxt))))
           (if (equal (fn-mpxt-tag-at page slot fn-mpxt) 0)
               (let ((fn-mpxt (fn-mpxt-write-slot page slot tag seq fn-mpxt)))
                 (mv :placed next (- fuel 1) fn-mpxt))
             (fn-mpr-place tag seq next (- fuel 1) fn-mpxt))))))

(verify-guards fn-mpr-place
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))
