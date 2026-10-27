; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-rebuild-rows-correspondence")

(local (defthm fn-lbcst-true-listp-update
 (implies (true-listp xs) (true-listp (update-nth i value xs)))
 :hints (("Goal" :induct (update-nth i value xs) :in-theory (enable update-nth true-listp)))))

(defthm fn-lbc-p-of-update-msgid-store
 (implies (and (fn-lbc-p fn-lbc) (fn-lbc-msgid-octetsp value)) (fn-lbc-p (update-fn-lbc-msgid-store value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbc-p update-fn-lbc-msgid-store fn-lbc-msgid-storep fn-dm-nth-update-nth
 fn-dm-len-update-nth fn-lbcst-true-listp-update length)))))

(defthm fn-lbc-p-of-update-overview-store
 (implies (and (fn-lbc-p fn-lbc) (fn-lbc-overview-octetsp value)) (fn-lbc-p (update-fn-lbc-overview-store value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbc-p update-fn-lbc-overview-store fn-lbc-overview-storep fn-dm-nth-update-nth
 fn-dm-len-update-nth fn-lbcst-true-listp-update length)))))

(defthm fn-lbc-p-of-update-number-store
 (implies (and (fn-lbc-p fn-lbc) (fn-dmapp value)) (fn-lbc-p (update-fn-lbc-number-store value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbc-p update-fn-lbc-number-store fn-lbc-number-storep fn-dm-nth-update-nth
 fn-dm-len-update-nth fn-lbcst-true-listp-update length)))))

(defthm fn-lbc-p-of-update-directory-store
 (implies (and (fn-lbc-p fn-lbc) (fn-lbc-directoryp value)) (fn-lbc-p (update-fn-lbc-directory-store value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbc-p update-fn-lbc-directory-store fn-lbc-directory-storep fn-dm-nth-update-nth
 fn-dm-len-update-nth fn-lbcst-true-listp-update length)))))

(defthm fn-lbc-p-of-update-membership-store
 (implies (and (fn-lbc-p fn-lbc) (fn-lbc-membershipsp value)) (fn-lbc-p (update-fn-lbc-membership-store value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbc-p update-fn-lbc-membership-store fn-lbc-membership-storep fn-dm-nth-update-nth
 fn-dm-len-update-nth fn-lbcst-true-listp-update length)))))

(defthm fn-lbc-p-of-update-nov-store
 (implies (and (fn-lbc-p fn-lbc) (fn-lbc-novp value)) (fn-lbc-p (update-fn-lbc-nov-store value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbc-p update-fn-lbc-nov-store fn-lbc-nov-storep fn-dm-nth-update-nth
 fn-dm-len-update-nth fn-lbcst-true-listp-update length)))))

(defthm fn-lbc-p-of-update-summary-groups
 (implies (and (fn-lbc-p fn-lbc) t) (fn-lbc-p (update-fn-lbc-summary-groups value fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lbc-p update-fn-lbc-summary-groups fn-lbc-summary-groupsp fn-dm-nth-update-nth
 fn-dm-len-update-nth fn-lbcst-true-listp-update length)))))
