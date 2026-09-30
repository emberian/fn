; Exact existing row/article representation boundary extracted unchanged.
(in-package "ACL2")
(include-book "catalog-handles")
(include-book "nntp-session")

(defun fn-cat-row-article (seq fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (natp seq) (< seq (fn-cat-count fn-cat))
                              (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat))
                  :verify-guards nil)
           (ignorable fn-arena))
  (let ((h (fn-cat-at seq fn-cat)))
    (fn-make-article (fn-record-msgid h)
                     (fn-record-payload h)
                     (fn-record-groups h)
                     (fn-held-numbers h)
                     t
                     (fn-record-stamp h))))

(verify-guards fn-cat-row-article
  :hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len fn-cat-at-is-nth)
           :use ((:instance fn-cat-handles-inp-at (n (fn-cat-count fn-cat)) (seq seq))))))

(defthm fn-cat-row-article-msgid
  (equal (fn-article-msgid (fn-cat-row-article seq fn-arena fn-cat))
         (fn-record-msgid (fn-cat-at seq fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-row-article))))

(defthm fn-cat-row-article-memberships
  (equal (fn-article-memberships (fn-cat-row-article seq fn-arena fn-cat))
         (fn-held-numbers (fn-cat-at seq fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-row-article))))

(defthm fn-cat-row-article-payload
  (equal (fn-article-payload (fn-cat-row-article seq fn-arena fn-cat))
         (fn-record-payload (fn-cat-at seq fn-cat)))
  :hints (("Goal" :in-theory (enable fn-cat-row-article))))
