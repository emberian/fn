; Existing relation/model events extracted verbatim for a narrow proof boundary.
(in-package "ACL2")
(include-book "catalog-record")
(include-book "nntp-session")

(defun fn-scol-row-okp (row fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (or (not (fn-hf-nov (fn-held-facts row)))
      (equal (fn-held-facts row)
             (fn-held-facts-of (fn-nntp-payload-bytes (fn-record-payload row) fn-arena)))))

(defun fn-scol-rows-okp (rows fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (if (consp rows)
      (and (fn-scol-row-okp (car rows) fn-arena)
           (fn-scol-rows-okp (cdr rows) fn-arena))
    t))

(defun-nx fn-scol-okp (fn-arena fn-cat)
  (and (fn-arena-p fn-arena)
       (fn-scol-rows-okp fn-cat fn-arena)))

(defthm fn-scol-rows-okp-nth
  (implies (and (fn-scol-rows-okp rows fn-arena)
                (natp seq) (< seq (len rows)))
           (fn-scol-row-okp (nth seq rows) fn-arena))
  :hints (("Goal" :in-theory (disable fn-scol-row-okp))))
