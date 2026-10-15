; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-locator-resolution")
(include-book "catalog-columns-properties")

(defthm fn-lc-locator-resolves-from-catalog-corr
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-held-listp rows)
 (fn-lbc-corr fn-lbc rows log) (natp i) (< i (fn-lbc-count fn-lbc)))
 (fn-lc-locator-resolves fn-lbc i log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-corresponding-row-at-index)
 (:instance fn-lbc-corresponding-row-locator-resolves (row (nth i rows))
 (pm (fn-lbc-value i :prefix-max fn-lbc)))
 (:instance fn-held-p-of-nth-of-held-listp (xs rows))
 (:instance fn-cat-rowp-of-nth-of-rowsp (xs rows)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-corr fn-cat$ap)))))

(defthm fn-lc-resolve-from-catalog-corr
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-held-listp rows)
 (fn-lbc-corr fn-lbc rows log) (natp i))
 (fn-lc-resolve-from i fn-lbc log))
 :hints (("Goal" :induct (fn-lc-resolve-from i fn-lbc log)
 :expand ((fn-lc-resolve-from i fn-lbc log))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lc-resolve-from fn-lc-count fn-lc-locator-resolves-from-catalog-corr natp)))))

(defthm fn-lc-locators-resolve-from-catalog-corr
 (implies (and (fn-lbc-p fn-lbc) (fn-cat$ap rows) (fn-held-listp rows)
 (fn-lbc-corr fn-lbc rows log))
 (fn-lc-locators-resolve fn-lbc log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lc-resolve-from-catalog-corr (i 0)))
 :in-theory (union-theories (theory 'ground-zero) '(fn-lc-locators-resolve)))))
