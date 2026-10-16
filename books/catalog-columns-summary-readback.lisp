; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-number-cell-correspondence")

(local (defthm fn-lbsrb-count-natural
 (natp (fn-cat-live-count-from group k top rows)) :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-cat-live-count-from group k top rows) :in-theory (union-theories (theory 'ground-zero) '(fn-cat-live-count-from))))))

(local (defthm fn-lbsrb-first-natural
 (natp (fn-cat-live-first group k top rows)) :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-cat-live-first group k top rows) :in-theory (union-theories (theory 'ground-zero) '(fn-cat-live-first))))))

(local (defthm fn-lbsrb-last-natural
 (natp (fn-cat-live-last group k rows)) :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-cat-live-last group k rows) :in-theory (union-theories (theory 'ground-zero) '(fn-cat-live-last posp))))))

(local (defthm fn-lbsrb-high-natural
 (natp (fn-cat-group-high group rows)) :rule-classes :type-prescription
 :hints (("Goal" :induct (fn-cat-group-high group rows) :in-theory (union-theories (theory 'ground-zero) '(fn-cat-group-high nfix max))))))

(defthm fn-lbc-summary-reference-values-natural
 (and (natp (fn-cat$a-group-live-count group rows)) (natp (fn-cat$a-group-live-low group rows))
      (natp (fn-cat$a-group-live-high group rows)) (natp (fn-cat$a-group-next group rows)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-cat$a-group-live-count fn-cat$a-group-live-low fn-cat$a-group-live-high fn-cat$a-group-next
 (:type-prescription fn-lbsrb-count-natural) (:type-prescription fn-lbsrb-first-natural)
 (:type-prescription fn-lbsrb-last-natural) (:type-prescription fn-lbsrb-high-natural))))))

(defthm fn-lbc-summary-word-of-four-cells
 (equal (fn-lbc-summary-word read-group read-field
          (fn-lbc-summary-put group (list count low high next) 1 fn-lbc))
  (if (equal read-group group)
   (case read-field (1 (if count count 0)) (2 (if low low 0))
                    (3 (if high high 0)) (4 (if next next 1))
                    (otherwise (fn-lbc-summary-word read-group read-field fn-lbc)))
   (fn-lbc-summary-word read-group read-field fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-put fn-lbc-summary-word fn-lbc-number-store update-fn-lbc-number-store
 fn-dm-nth-update-nth fn-dmap-get-of-put fn-dm-lanep)))))

(local (defthm fn-lbsrb-member-cons
 (iff (member-equal group (cons first rest)) (or (equal group first) (member-equal group rest)))
 :hints (("Goal" :in-theory (enable member-equal)))))

(defthm fn-lbc-summary-field-1-of-rebuild-summaries
 (equal (fn-lbc-summary-word read-group 1 (fn-lbc-rebuild-summaries groups rows fn-lbc))
        (if (member-equal read-group groups) (fn-cat$a-group-live-count read-group rows)
            (fn-lbc-summary-word read-group 1 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-summaries groups rows fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-summaries fn-lbc-summary-word-of-four-cells fn-lbc-summary-reference-values-natural
 fn-lbsrb-member-cons)))))

(defthm fn-lbc-summary-field-2-of-rebuild-summaries
 (equal (fn-lbc-summary-word read-group 2 (fn-lbc-rebuild-summaries groups rows fn-lbc))
        (if (member-equal read-group groups) (fn-cat$a-group-live-low read-group rows)
            (fn-lbc-summary-word read-group 2 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-summaries groups rows fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-summaries fn-lbc-summary-word-of-four-cells fn-lbc-summary-reference-values-natural
 fn-lbsrb-member-cons)))))

(defthm fn-lbc-summary-field-3-of-rebuild-summaries
 (equal (fn-lbc-summary-word read-group 3 (fn-lbc-rebuild-summaries groups rows fn-lbc))
        (if (member-equal read-group groups) (fn-cat$a-group-live-high read-group rows)
            (fn-lbc-summary-word read-group 3 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-summaries groups rows fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-summaries fn-lbc-summary-word-of-four-cells fn-lbc-summary-reference-values-natural
 fn-lbsrb-member-cons)))))

(defthm fn-lbc-summary-field-4-of-rebuild-summaries
 (equal (fn-lbc-summary-word read-group 4 (fn-lbc-rebuild-summaries groups rows fn-lbc))
        (if (member-equal read-group groups) (fn-cat$a-group-next read-group rows)
            (fn-lbc-summary-word read-group 4 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-summaries groups rows fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-rebuild-summaries fn-lbc-summary-word-of-four-cells fn-lbc-summary-reference-values-natural
 fn-lbsrb-member-cons)))))
