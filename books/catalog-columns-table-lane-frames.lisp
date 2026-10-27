; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-number-rebuild-readback")

(defthm fn-lbc-summary-word-of-number-put-first
 (equal (fn-lbc-summary-word read-group read-field (fn-lbc-number-put-first group number i fn-lbc))
        (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-number-put-first fn-lbc-summary-word fn-lbc-number-store update-fn-lbc-number-store
 fn-dm-nth-update-nth fn-dmap-get-of-put fn-dm-lanep)))))

(defthm fn-lbc-number-get-of-summary-put
 (equal (fn-lbc-number-get read-group read-number (fn-lbc-summary-put group values field fn-lbc))
        (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :induct (fn-lbc-summary-put group values field fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-put fn-lbc-number-get fn-lbc-number-store update-fn-lbc-number-store
 fn-dm-nth-update-nth fn-dmap-get-of-put fn-dm-lanep)))))

(defthm fn-lbc-summary-word-of-number-put-row-seen
 (equal (fn-lbc-summary-word read-group read-field (fn-lbc-number-put-row-seen numbers seen i fn-lbc)) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :induct (fn-lbc-number-put-row-seen numbers seen i fn-lbc) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-number-put-row-seen fn-lbc-summary-word-of-number-put-first)))))

(defthm fn-lbc-summary-word-of-number-put-row
 (equal (fn-lbc-summary-word read-group read-field (fn-lbc-number-put-row numbers i fn-lbc)) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-number-put-row fn-lbc-summary-word-of-number-put-row-seen)))))

(defthm fn-lbc-summary-word-of-rebuild-rows
 (equal (fn-lbc-summary-word read-group read-field (fn-lbc-rebuild-rows rows log fn-lbc)) (fn-lbc-summary-word read-group read-field fn-lbc))
 :hints (("Goal" :induct (fn-lbc-rebuild-rows rows log fn-lbc) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-rebuild-rows fn-lbc-summary-word-of-append-row fn-lbc-summary-word-of-number-put-row)))))

(defthm fn-lbc-number-get-of-rebuild-summaries
 (equal (fn-lbc-number-get read-group read-number (fn-lbc-rebuild-summaries groups rows fn-lbc)) (fn-lbc-number-get read-group read-number fn-lbc))
 :hints (("Goal" :induct (fn-lbc-rebuild-summaries groups rows fn-lbc) :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-rebuild-summaries fn-lbc-number-get-of-summary-put)))))
