; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-open-summary-correspondence")

(local (defthm fn-lbsol-0
 (implies (not (member-equal group (fn-lbc-number-group-keys numbers)))
          (equal (fn-cat-assoc group numbers) nil))
 :hints (("Goal" :induct (fn-lbc-number-group-keys numbers)
          :in-theory (enable fn-lbc-number-group-keys fn-cat-assoc)))))

(local (defthm fn-lbsol-1
 (iff (member-equal a (union-equal x y))
      (or (member-equal a x) (member-equal a y)))
 :hints (("Goal" :induct (union-equal x y) :in-theory (enable union-equal)))))

(local (defthm fn-lbsol-2
 (implies (not (member-equal group (fn-lbc-row-group-keys rows)))
          (equal (fn-cat-group-high group rows) 0))
 :hints (("Goal" :induct (fn-lbc-row-group-keys rows)
          :in-theory (e/d (fn-lbc-row-group-keys fn-cat-group-high fn-held-number-in)
                          (fn-lbc-number-group-keys fn-cat-assoc))))))

(local (defthm fn-lbsol-3
 (implies (not (member-equal group (fn-lbc-row-group-keys rows)))
  (equal (list (fn-cat$a-group-live-count group rows) (fn-cat$a-group-live-low group rows)
               (fn-cat$a-group-live-high group rows) (fn-cat$a-group-next group rows))
         '(0 0 0 1)))
 :hints (("Goal" :in-theory (e/d (fn-cat$a-group-live-count fn-cat$a-group-live-low
  fn-cat$a-group-live-high fn-cat$a-group-next fn-cat-live-count-from fn-cat-live-first fn-cat-live-last)
  (fn-lbc-row-group-keys fn-cat-group-high fn-cat-live-numberp))))))

(defthm fn-lbc-summary-word-of-clear-columns
 (equal (fn-lbc-summary-word group field (fn-lbc-clear-columns fn-lbc)) (if (equal field 4) 1 0))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-lbc-number-store-of-clear-columns))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-word fn-lbc-number-store fn-dmap-get fn-dmap$a-get nth hons-assoc-equal assoc-equal)))))

(defthm fn-lbc-summary-field-1-of-open-rebuild
 (equal (fn-lbc-summary-word group 1 (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat$a-group-live-count group rows))
 :hints (("Goal" :do-not-induct t :cases ((member-equal group (fn-lbc-row-group-keys rows)))
 :use ((:instance fn-lbsol-3))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-field-1-of-open-rebuild-member fn-lbc-open-rebuild
 fn-lbc-summary-word-of-index-slots fn-lbc-summary-word-of-reserve-slots
 fn-lbc-summary-word-of-summary-groups-update fn-lbc-summary-field-1-of-rebuild-summaries
 fn-lbc-summary-word-of-rebuild-rows fn-lbc-summary-word-of-clear-columns)))))

(defthm fn-lbc-summary-field-2-of-open-rebuild
 (equal (fn-lbc-summary-word group 2 (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat$a-group-live-low group rows))
 :hints (("Goal" :do-not-induct t :cases ((member-equal group (fn-lbc-row-group-keys rows)))
 :use ((:instance fn-lbsol-3))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-field-2-of-open-rebuild-member fn-lbc-open-rebuild
 fn-lbc-summary-word-of-index-slots fn-lbc-summary-word-of-reserve-slots
 fn-lbc-summary-word-of-summary-groups-update fn-lbc-summary-field-2-of-rebuild-summaries
 fn-lbc-summary-word-of-rebuild-rows fn-lbc-summary-word-of-clear-columns)))))

(defthm fn-lbc-summary-field-3-of-open-rebuild
 (equal (fn-lbc-summary-word group 3 (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat$a-group-live-high group rows))
 :hints (("Goal" :do-not-induct t :cases ((member-equal group (fn-lbc-row-group-keys rows)))
 :use ((:instance fn-lbsol-3))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-field-3-of-open-rebuild-member fn-lbc-open-rebuild
 fn-lbc-summary-word-of-index-slots fn-lbc-summary-word-of-reserve-slots
 fn-lbc-summary-word-of-summary-groups-update fn-lbc-summary-field-3-of-rebuild-summaries
 fn-lbc-summary-word-of-rebuild-rows fn-lbc-summary-word-of-clear-columns)))))

(defthm fn-lbc-summary-field-4-of-open-rebuild
 (equal (fn-lbc-summary-word group 4 (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat$a-group-next group rows))
 :hints (("Goal" :do-not-induct t :cases ((member-equal group (fn-lbc-row-group-keys rows)))
 :use ((:instance fn-lbsol-3))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-field-4-of-open-rebuild-member fn-lbc-open-rebuild
 fn-lbc-summary-word-of-index-slots fn-lbc-summary-word-of-reserve-slots
 fn-lbc-summary-word-of-summary-groups-update fn-lbc-summary-field-4-of-rebuild-summaries
 fn-lbc-summary-word-of-rebuild-rows fn-lbc-summary-word-of-clear-columns)))))

(defthm fn-lbc-live-summary-of-open-rebuild
 (equal (fn-lbc-live-summary group (fn-lbc-open-rebuild rows log fn-lbc))
  (list (fn-cat$a-group-live-count group rows) (fn-cat$a-group-live-low group rows)
        (fn-cat$a-group-live-high group rows) (fn-cat$a-group-next group rows)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-live-summary fn-lbc-summary-field-1-of-open-rebuild fn-lbc-summary-field-2-of-open-rebuild
 fn-lbc-summary-field-3-of-open-rebuild fn-lbc-summary-field-4-of-open-rebuild)))))
