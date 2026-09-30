; Actual existing numbered article selection, no second locator.
; Definitions and original guard event moved verbatim.
(in-package "ACL2")
(include-book "catalog-row-article")
(include-book "catalog-number-read")

(defun fn-scat-number-article (group n v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil))
  (let ((seq (fn-cnx-view-seq group n v fn-cat)))
    (if seq (fn-cat-row-article seq fn-arena fn-cat) nil)))

(local
 (defthm fn-ssa-selected-sequence-in-bounds
  (implies (fn-cnx-view-seq group n v fn-cat)
   (and (natp (fn-cnx-view-seq group n v fn-cat))
        (< (fn-cnx-view-seq group n v fn-cat) (fn-cat-count fn-cat))))
  :hints (("Goal" :in-theory
   (e/d (fn-cnx-view-seq) (fn-cat-group-number fn-cat-visible-at fn-cat-count-is-len))))))

(verify-guards fn-scat-number-article)

(defun fn-scat-available-article (group n v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp v)
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))))
  (if (and (posp n) (<= n *fn-nntp-max-article-number*))
      (let ((article (fn-scat-number-article group n v fn-arena fn-cat)))
        (if (and article (fn-nntp-article-idp article)) article nil))
    nil))

(local
 (defthm fn-ssa-nth-outside-list
  (implies (and (natp i) (<= (len xs) i)) (equal (nth i xs) nil))
  :hints (("Goal" :induct (nth i xs) :in-theory (enable nth len)))))

; Semantic bridge of the ACTUAL old selected getter to the same retained row.
; This is proof vocabulary; no locator is executed twice on a served path.
(defthm fn-scat-available-article-has-actual-selected-source
 (let* ((seq (fn-cnx-view-seq group number v fn-cat))
        (row (fn-cat-at seq fn-cat)) (h (fn-record-payload row)))
  (implies (and (posp number) (<= number *fn-nntp-max-article-number*)
                seq (fn-nntp-article-idp (fn-cat-row-article seq fn-arena fn-cat))
                (natp h))
   (equal (fn-nntp-article-bytes
            (fn-scat-available-article group number v fn-arena fn-cat) fn-arena)
          (nth h fn-arena))))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-scat-available-article fn-scat-number-article
         fn-nntp-article-bytes fn-nntp-payload-bytes fn-arena-count-is-len)
       (fn-cnx-view-seq fn-cat-row-article fn-cat-at fn-record-payload
        fn-nntp-article-idp)))))
