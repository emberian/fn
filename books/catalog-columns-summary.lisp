; LB2 resident summary equals the abstract recomputation.
(in-package "ACL2")
(include-book "catalog-columns-guards")

(local (defthm fn-lbp-number-group-absent-assoc
 (implies (not (member-equal group (fn-lbc-number-group-keys numbers)))
          (equal (fn-cat-assoc group numbers) nil))
 :hints (("Goal" :induct (fn-lbc-number-group-keys numbers)
          :in-theory (enable fn-lbc-number-group-keys fn-cat-assoc)))))

(local (defthm fn-lbr10-member-of-union
 (iff (member-equal a (union-equal x y))
      (or (member-equal a x) (member-equal a y)))
 :hints (("Goal" :induct (union-equal x y) :in-theory (enable union-equal)))))

(local (defthm fn-lbp-row-group-absent-high-zero
 (implies (not (member-equal group (fn-lbc-row-group-keys rows)))
          (equal (fn-cat-group-high group rows) 0))
 :hints (("Goal" :induct (fn-lbc-row-group-keys rows)
          :in-theory (e/d (fn-lbc-row-group-keys fn-cat-group-high fn-held-number-in)
                          (fn-lbc-number-group-keys fn-cat-assoc))))))

(local (defthm fn-lbp-row-group-absent-summary-zero
 (implies (not (member-equal group (fn-lbc-row-group-keys rows)))
  (equal (list (fn-cat$a-group-live-count group rows) (fn-cat$a-group-live-low group rows)
               (fn-cat$a-group-live-high group rows) (fn-cat$a-group-next group rows))
         '(0 0 0 1)))
 :hints (("Goal" :in-theory (e/d (fn-cat$a-group-live-count fn-cat$a-group-live-low
  fn-cat$a-group-live-high fn-cat$a-group-next fn-cat-live-count-from fn-cat-live-first fn-cat-live-last)
  (fn-lbc-row-group-keys fn-cat-group-high fn-cat-live-numberp))))))

(local (defthm fn-lbp-summary-corr-member
 (implies (and (fn-lbc-summaries-corr groups rows fn-lbc) (member-equal group groups))
  (equal (fn-lbc-live-summary group fn-lbc)
         (list (fn-cat$a-group-live-count group rows) (fn-cat$a-group-live-low group rows)
               (fn-cat$a-group-live-high group rows) (fn-cat$a-group-next group rows))))
 :hints (("Goal" :induct (fn-lbc-summaries-corr groups rows fn-lbc)
 :in-theory (e/d (fn-lbc-summaries-corr)
  (fn-lbc-live-summary fn-cat$a-group-live-count fn-cat$a-group-live-low fn-cat$a-group-live-high fn-cat$a-group-next))))))

(local (defthm fn-lbr10-summary-cells-lookup
 (implies (and (fn-lbc-summary-cells-corr keys table rows)
               (assoc-equal (cons (list :summary group) field) keys)
               (member-equal field '(1 2 3 4)))
  (equal (cdr (assoc-equal (cons (list :summary group) field) table))
         (case field
          (1 (fn-cat$a-group-live-count group rows))
          (2 (fn-cat$a-group-live-low group rows))
          (3 (fn-cat$a-group-live-high group rows))
          (4 (fn-cat$a-group-next group rows)))))
 :hints (("Goal" :induct (fn-lbc-summary-cells-corr keys table rows)
 :in-theory (e/d (fn-lbc-summary-cells-corr assoc-equal)
 (fn-cat$a-group-live-count fn-cat$a-group-live-low fn-cat$a-group-live-high fn-cat$a-group-next))))))

(local (defthm fn-lbr10-hons-assoc-is-assoc-for-cons-key
 (implies (consp key) (equal (hons-assoc-equal key table) (assoc-equal key table)))
 :hints (("Goal" :induct (hons-assoc-equal key table)
 :in-theory (enable hons-assoc-equal assoc-equal)))))

(local (defthm fn-lbr10-absent-group-summary-word
 (implies (and (fn-lbc-tables-corr fn-lbc rows)
               (not (member-equal group (fn-lbc-row-group-keys rows)))
               (member-equal field '(1 2 3 4)))
  (equal (fn-lbc-summary-word group field fn-lbc) (if (equal field 4) 1 0)))
 :hints (("Goal" :cases ((assoc-equal (cons (list :summary group) field)
                                    (nth 1 (nth *fn-lbc-number-store* fn-lbc))))
 :use ((:instance fn-lbp-row-group-absent-summary-zero)
       (:instance fn-lbr10-summary-cells-lookup
        (keys (nth 1 (nth *fn-lbc-number-store* fn-lbc)))
        (table (nth 1 (nth *fn-lbc-number-store* fn-lbc)))))
 :in-theory (e/d (fn-lbc-tables-corr fn-lbc-summary-word fn-lbc-number-store fn-dmap-get fn-dmap$a-get)
 (fn-lbp-row-group-absent-summary-zero fn-lbr10-summary-cells-lookup
  fn-lbc-summary-cells-corr fn-lbc-number-cells-corr fn-lbc-row-group-keys
  fn-cat$a-group-live-count fn-cat$a-group-live-low fn-cat$a-group-live-high fn-cat$a-group-next))))))

(defthm fn-lbc-live-summary-is-recomputed
  (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-lbc-corr fn-lbc rows log))
           (equal (fn-lbc-live-summary group fn-lbc)
                  (list (fn-cat$a-group-live-count group rows)
                        (fn-cat$a-group-live-low group rows)
                        (fn-cat$a-group-live-high group rows)
                        (fn-cat$a-group-next group rows))))
 :hints (("Goal" :cases ((member-equal group (fn-lbc-row-group-keys rows)))
 :use ((:instance fn-lbp-summary-corr-member (groups (fn-lbc-row-group-keys rows)))
       (:instance fn-lbp-row-group-absent-summary-zero))
 :in-theory (e/d (fn-lbc-corr fn-lbc-live-summary)
  (fn-lbc-p fn-cat$ap fn-lbc-count fn-lbc-row-group-keys fn-lbc-tables-corr
   fn-lbc-summaries-corr fn-lbc-summary-word fn-lbc-rows-corr fn-lbc-slots-corr
   fn-lbc-number-rows-covered fn-cat$a-group-live-count fn-cat$a-group-live-low
   fn-cat$a-group-live-high fn-cat$a-group-next fn-lbp-summary-corr-member
   fn-lbp-row-group-absent-summary-zero)))))
