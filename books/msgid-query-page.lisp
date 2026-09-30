; One borrowed immutable page tick of the operational Message-ID iterator.
; Page transition returns to the provider's bounded directory continuation.
(in-package "ACL2")
(include-book "msgid-probe-layout")

(defun fn-mpl-page-next (tag cursor fuel pages page-index page-words)
  (declare (xargs :measure (nfix fuel)
                  :guard (and (natp tag) (fn-mpr-cursorp cursor pages)
                              (natp page-index) (< page-index pages)
                              (true-listp page-words)
                              (natp fuel) (<= fuel *fn-mpr-slot-quantum*))
                  :verify-guards nil))
  (cond ((equal (nth 1 cursor) 0) (mv :done cursor nil fuel))
        ((zp fuel) (mv :yield cursor nil 0))
        ((not (equal (nth 0 cursor) page-index))
         (mv :next-page cursor nil fuel))
        (t
         (let* ((slot (nth 2 cursor))
                (found-tag (fn-mpl-tag-at 0 slot page-words))
                (next (fn-mpr-advance cursor pages)))
           (cond ((equal found-tag 0) (mv :done cursor nil (- fuel 1)))
                 ((equal found-tag tag)
                  (let ((encoded-seq (fn-mpl-seq-at 0 slot page-words)))
                    (if (zp encoded-seq)
                        (mv :recovery-required cursor nil (- fuel 1))
                      (mv :candidate next (- encoded-seq 1) (- fuel 1)))))
                 (t (fn-mpl-page-next tag next (- fuel 1) pages page-index page-words)))))))

(verify-guards fn-mpl-page-next
  :hints (("Goal" :in-theory (enable fn-mpr-cursorp))))

(in-theory (disable fn-mpl-page-next))
