; Exact old range decomposition, used by the maintained controller boundary.
(in-package "ACL2")
(include-book "served-range-source")

(defthm fn-ovw-lines-current-number-unfolds
 (let* ((seq (fn-cnx-view-seq group k v fn-cat))
        (row (fn-cat-at seq fn-cat))
        (article (fn-scat-available-article group k v fn-arena fn-cat)))
  (implies (and (natp k) (natp hi) (<= k hi)
                (natp seq) (< seq (fn-cat-count fn-cat))
                (equal (fn-held-number-in group row) k)
                (posp k) (<= k *fn-nntp-max-article-number*)
                (fn-scat-msgid-idp (fn-record-msgid row)))
   (equal (fn-ovw-lines group k hi v fn-arena fn-cat)
    (if (and (consp article)
             (not (fn-nntp-article-tombstonep article fn-arena))
             (fn-nov-okp (fn-nov-overview article fn-arena)))
        (cons (fn-nov-line k (fn-nov-overview article fn-arena))
              (fn-ovw-lines group (+ 1 k) hi v fn-arena fn-cat))
      (fn-ovw-lines group (+ 1 k) hi v fn-arena fn-cat)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :expand ((fn-cnx-range-aux group k hi v fn-cat)
           (:free (rest) (fn-scat-range-keep group
                          (cons (fn-cnx-view-seq group k v fn-cat) rest) fn-cat))
           (:free (rest) (fn-nov-lines-for-numbers-cat group (cons k rest)
                           v fn-arena fn-cat)))
  :in-theory (e/d (fn-ovw-lines)
   (fn-cnx-view-seq fn-cnx-range-aux fn-scat-range-keep
    fn-cat-at fn-cat-count fn-held-number-in fn-scat-msgid-idp
    fn-record-msgid fn-scat-available-article fn-nov-line fn-nov-overview
    fn-nntp-article-tombstonep fn-nov-okp fn-nov-lines-for-numbers-cat)))))
