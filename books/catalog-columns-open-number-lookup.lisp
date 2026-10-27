; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-table-lane-frames")

(defthm fn-lbc-number-get-of-open-rebuild
 (implies (fn-cat-rowsp rows)
 (equal (fn-lbc-number-get group number (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat-number-seq group number rows 0)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lbc-number-get-of-index-slots fn-lbc-number-get-of-reserve-slots
 fn-lbc-number-get-of-summary-groups-update fn-lbc-number-get-of-rebuild-summaries
 fn-lbc-number-get-of-rebuild-rows fn-lbc-number-get-of-clear-columns fn-lbc-count-of-clear-columns)))))

(defthm fn-lbc-number-keys-covered-of-open-rebuild
 (implies (fn-cat-rowsp rows)
 (fn-lbc-number-keys-covered numbers rows (fn-lbc-open-rebuild rows log fn-lbc)))
 :hints (("Goal" :induct (len numbers)
 :in-theory (union-theories (theory 'minimal-theory)
 '(len fn-lbc-number-keys-covered fn-lbc-number-get-of-open-rebuild)))))

(defthm fn-lbc-number-rows-covered-of-open-rebuild
 (implies (fn-cat-rowsp rows)
 (fn-lbc-number-rows-covered rest rows (fn-lbc-open-rebuild rows log fn-lbc)))
 :hints (("Goal" :induct (len rest)
 :in-theory (union-theories (theory 'minimal-theory)
 '(len fn-lbc-number-rows-covered fn-lbc-number-keys-covered-of-open-rebuild)))))
