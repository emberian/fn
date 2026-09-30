; The existing number lookup, separated from its archive-refinement proof.
(in-package "ACL2")
(include-book "catalog")

(defun fn-cnx-view-seq (group n v fn-cat)
  (declare (xargs :stobjs fn-cat :guard (natp v)
                  :guard-hints (("Goal" :in-theory (disable fn-cat-p-is-rowsp fn-cat-count-is-len
                                                            fn-cat-at-is-nth fn-cat-group-number-is-number-seq)))))
  (let ((s (fn-cat-group-number group n fn-cat)))
    (if (and (natp s) (< s (fn-cat-count fn-cat)) (fn-cat-visible-at s v fn-cat))
        s
      nil)))

