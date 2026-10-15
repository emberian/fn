; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-nov-readback")

(local (defthm fn-lbms-count-by-store
 (equal (fn-lbc-membership-record-count fn-lbc) (len (nth *fn-lbc-membership-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-membership-record-count fn-lbc-membership-store fn-lbc-memberships-count-is-len))))))

(local (defthm fn-lbms-len-append-one
 (equal (len (append xs (list x))) (+ 1 (len xs)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(local (defthm fn-lbms-nth-append-at-length
 (equal (nth (len xs) (append xs (list x))) x)
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len nth)))))

(local (defthm fn-lbms-u64-when-representable
 (implies (unsigned-byte-p 64 x) (equal (fn-lbc-u64 x) x))
 :hints (("Goal" :in-theory (enable fn-lbc-u64)))))

(local (defthm fn-lbms-nfix-when-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbms-range-of-membership-store-update
 (implies (and (natp off) (natp n))
  (equal (fn-lbc-overview-pool-range off n (update-nth *fn-lbc-membership-store* value fn-lbc))
         (fn-lbc-overview-pool-range off n fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-overview-pool-range-by-store fn-dm-nth-update-nth))))))

(defthm fn-lbc-membership-group-of-append-single-new
 (implies (and (fn-lbc-text-smallp group)
               (unsigned-byte-p 64 (fn-lbc-overview-pool-count fn-lbc))
               (unsigned-byte-p 64 (len (fn-record-string-octets group))))
  (equal (fn-lbc-membership-group (fn-lbc-membership-record-count fn-lbc) (fn-lbc-append-memberships (list (if numbersp (cons group number) group)) numbersp fn-lbc)) group))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-append-memberships fn-lbc-membership-group fn-lbc-membership-store update-fn-lbc-membership-store fn-lbc-memberships-append-is-append fn-lbwf-overview-pool-append-field fn-dm-nth-update-nth fn-lbms-count-by-store fn-lbms-len-append-one fn-lbms-nth-append-at-length fn-lbms-u64-when-representable fn-lbms-nfix-when-natural fn-lbms-range-of-membership-store-update fn-lbc-membership-field-group-start-by-definition fn-lbc-membership-field-group-length-by-definition fn-lbc-overview-pool-range-of-appended-bytes fn-lbc-small-text-byte-round-trip nth (:type-prescription fn-lbc-overview-pool-count-natural))) '((:definition nfix) (:definition true-list-fix) (tau-system))))))

(defthm fn-lbc-membership-number-of-append-single-new
 (equal (fn-lbc-membership-field :number (fn-lbc-membership-record-count fn-lbc) (fn-lbc-append-memberships (list (if numbersp (cons group number) group)) numbersp fn-lbc))
        (if numbersp (fn-lbc-u64 number) 0))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t
  :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-append-memberships fn-lbc-membership-group fn-lbc-membership-store update-fn-lbc-membership-store fn-lbc-memberships-append-is-append fn-lbwf-overview-pool-append-field fn-dm-nth-update-nth fn-lbms-count-by-store fn-lbms-len-append-one fn-lbms-nth-append-at-length fn-lbms-u64-when-representable fn-lbms-nfix-when-natural fn-lbms-range-of-membership-store-update fn-lbc-membership-field-group-start-by-definition fn-lbc-membership-field-group-length-by-definition fn-lbc-overview-pool-range-of-appended-bytes fn-lbc-small-text-byte-round-trip nth (:type-prescription fn-lbc-overview-pool-count-natural) fn-lbc-membership-field-number-by-definition)) '((:definition nfix) (:definition true-list-fix) (tau-system))))))
