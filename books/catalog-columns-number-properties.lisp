; Total-domain number-table refinement for the resident selector.
(in-package "ACL2")
(include-book "catalog-columns-projections")
(include-book "catalog-columns-number-correspondence")



(local (defthm fn-lbr11-number-seq-bounds-general
 (implies (and (natp base) (fn-cat-number-seq group number rows base))
  (and (natp (fn-cat-number-seq group number rows base))
       (<= base (fn-cat-number-seq group number rows base))
       (< (fn-cat-number-seq group number rows base) (+ base (len rows)))))
 :hints (("Goal" :induct (fn-cat-number-seq group number rows base)
 :in-theory (union-theories (theory 'ground-zero) '(fn-cat-number-seq natp))))))

(local (defthm fn-lbr11-number-seq-bounds-zero
 (implies (fn-cat-number-seq group number rows 0)
  (and (natp (fn-cat-number-seq group number rows 0))
       (< (fn-cat-number-seq group number rows 0) (len rows))))
 :hints (("Goal" :use ((:instance fn-lbr11-number-seq-bounds-general (base 0)))
 :in-theory (union-theories (theory 'ground-zero) '(natp))))))

(defthm fn-lbc-visible-implies-index-bounds
 (implies (fn-lbc-visiblep i v fn-lbc) (and (natp i) (< i (fn-lbc-count fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-visiblep)))))

(defthm fn-lbc-number-visible-is-walk
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log)
               (fn-cnx-freshp rows) number)
  (equal (let ((i (fn-lbc-number-get group number fn-lbc)))
           (if (and (natp i) (fn-lbc-visiblep i v fn-lbc)) i nil))
         (fn-cat-view-number-find group number (len rows) v rows)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-cnx-view-seq-is-walk (fn-cat rows) (n number)))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-cnx-view-seq fn-cat-visible-at-is-visiblep fn-cat-group-number-is-number-seq fn-cat-count-is-len
    fn-lbc-number-get-is-abstract fn-lbr11-number-seq-bounds-zero
    fn-lbc-visible-is-row-visible-total-version natp)))))
