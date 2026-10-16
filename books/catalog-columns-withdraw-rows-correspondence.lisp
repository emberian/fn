; Lift the row update through the catalog's structural correspondence.
(in-package "ACL2")
(include-book "catalog-columns-withdraw-row-correspondence")

(defthm fn-lbc-rows-corr-past-set-withdrawal
 (implies (and (fn-lbc-p fn-lbc-v) (natp i) (< i (fn-lbc-count fn-lbc-v))
               (natp start) (< i start) (<= (+ start (len rows)) (fn-lbc-count fn-lbc-v))
               (fn-lbc-rows-corr start rows pm fn-lbc-v log))
  (fn-lbc-rows-corr start rows pm (fn-lbc-set-withdrawal i version by fn-lbc-v) log))
 :hints (("Goal" :induct (fn-lbc-rows-corr start rows pm fn-lbc-v log)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbc-rows-corr fn-lbc-row-corr-other-of-set-withdrawal len natp nfix)))))

(local (defun-nx fn-lbcwdr-update-induct (rows n start pm)
 (declare (xargs :measure (acl2-count rows) :verify-guards nil))
 (if (and (consp rows) (posp n))
  (fn-lbcwdr-update-induct (cdr rows) (- n 1) (+ 1 (nfix start))
   (max (nfix pm) (nfix (fn-record-stamp (car rows))))) nil)))

(defthm fn-lbc-rows-corr-of-set-withdrawal
 (implies (and (fn-lbc-p fn-lbc-v) (natp start) (natp n) (< n (len rows))
               (<= (+ start (len rows)) (fn-lbc-count fn-lbc-v))
               (fn-cat-rowsp rows) (natp version) (natp by)
               (fn-lbc-rows-corr start rows pm fn-lbc-v log))
  (fn-lbc-rows-corr start
   (update-nth n (fn-held-with-withdrawn (nth n rows) (cons version by)) rows) pm
   (fn-lbc-set-withdrawal (+ start n) version by fn-lbc-v) log))
 :hints (("Goal" :induct (fn-lbcwdr-update-induct rows n start pm)
  :in-theory (union-theories (theory 'ground-zero)
   '(fn-lbcwdr-update-induct fn-lbc-rows-corr fn-lbc-row-corr-of-set-withdrawal
     fn-lbc-row-corr-other-of-set-withdrawal fn-lbc-rows-corr-past-set-withdrawal
     fn-lbcwd-logical-stamp-of-withdrawal-by-definition fn-cat-rowsp
     update-nth nth len natp posp nfix)))))
