; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-summary-readback")

(defthm fn-lbc-summary-field-1-of-open-rebuild-member
 (implies (member-equal group (fn-lbc-row-group-keys rows))
 (equal (fn-lbc-summary-word group 1 (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat$a-group-live-count group rows)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lbc-summary-word-of-index-slots fn-lbc-summary-word-of-reserve-slots
 fn-lbc-summary-word-of-summary-groups-update fn-lbc-summary-field-1-of-rebuild-summaries)))))

(defthm fn-lbc-summary-field-2-of-open-rebuild-member
 (implies (member-equal group (fn-lbc-row-group-keys rows))
 (equal (fn-lbc-summary-word group 2 (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat$a-group-live-low group rows)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lbc-summary-word-of-index-slots fn-lbc-summary-word-of-reserve-slots
 fn-lbc-summary-word-of-summary-groups-update fn-lbc-summary-field-2-of-rebuild-summaries)))))

(defthm fn-lbc-summary-field-3-of-open-rebuild-member
 (implies (member-equal group (fn-lbc-row-group-keys rows))
 (equal (fn-lbc-summary-word group 3 (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat$a-group-live-high group rows)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lbc-summary-word-of-index-slots fn-lbc-summary-word-of-reserve-slots
 fn-lbc-summary-word-of-summary-groups-update fn-lbc-summary-field-3-of-rebuild-summaries)))))

(defthm fn-lbc-summary-field-4-of-open-rebuild-member
 (implies (member-equal group (fn-lbc-row-group-keys rows))
 (equal (fn-lbc-summary-word group 4 (fn-lbc-open-rebuild rows log fn-lbc))
        (fn-cat$a-group-next group rows)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-open-rebuild fn-lbc-summary-word-of-index-slots fn-lbc-summary-word-of-reserve-slots
 fn-lbc-summary-word-of-summary-groups-update fn-lbc-summary-field-4-of-rebuild-summaries)))))

(defthm fn-lbc-live-summary-of-open-rebuild-member
 (implies (member-equal group (fn-lbc-row-group-keys rows))
 (equal (fn-lbc-live-summary group (fn-lbc-open-rebuild rows log fn-lbc))
  (list (fn-cat$a-group-live-count group rows) (fn-cat$a-group-live-low group rows)
        (fn-cat$a-group-live-high group rows) (fn-cat$a-group-next group rows))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-live-summary fn-lbc-summary-field-1-of-open-rebuild-member
 fn-lbc-summary-field-2-of-open-rebuild-member fn-lbc-summary-field-3-of-open-rebuild-member
 fn-lbc-summary-field-4-of-open-rebuild-member)))))

(local (defthm fn-lbsoc-member-cons
 (iff (member-equal query (cons key rest)) (or (equal query key) (member-equal query rest)))
 :hints (("Goal" :in-theory (enable member-equal)))))

(local (defthm fn-lbsoc-subset-cons
 (implies (subsetp-equal xs ys) (subsetp-equal xs (cons item ys)))
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal fn-lbsoc-member-cons))))))

(local (defthm fn-lbsoc-member-head
 (implies (consp xs) (member-equal (car xs) xs))
 :hints (("Goal" :in-theory (enable member-equal)))))

(local (defthm fn-lbsoc-subset-self
 (subsetp-equal xs xs)
 :hints (("Goal" :induct (len xs) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal fn-lbsoc-subset-cons fn-lbsoc-member-head))))))

(defthm fn-lbc-summaries-corr-for-open-rebuild
 (implies (subsetp-equal groups (fn-lbc-row-group-keys rows))
 (fn-lbc-summaries-corr groups rows (fn-lbc-open-rebuild rows log fn-lbc)))
 :hints (("Goal" :induct (len groups) :in-theory (union-theories (theory 'ground-zero)
 '(len subsetp-equal fn-lbc-summaries-corr fn-lbc-live-summary-of-open-rebuild-member)))))

(defthm fn-lbc-summaries-corr-of-open-rebuild
 (fn-lbc-summaries-corr (fn-lbc-row-group-keys rows) rows (fn-lbc-open-rebuild rows log fn-lbc))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbc-summaries-corr-for-open-rebuild (groups (fn-lbc-row-group-keys rows))))
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbsoc-subset-self)))))
