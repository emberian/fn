; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-child-append-types")

(defthm fn-lbc-row-store-has-native-type
 (implies (fn-lbc-p fn-lbc) (fn-lbc-rowwordsp (fn-lbc-row-store fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-row-store fn-lbc-row-storep)))))

(defthm fn-lbc-msgid-store-has-native-type
 (implies (fn-lbc-p fn-lbc) (fn-lbc-msgid-octetsp (fn-lbc-msgid-store fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-msgid-store fn-lbc-msgid-storep)))))

(defthm fn-lbc-overview-store-has-native-type
 (implies (fn-lbc-p fn-lbc) (fn-lbc-overview-octetsp (fn-lbc-overview-store fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-overview-store fn-lbc-overview-storep)))))

(defthm fn-lbc-number-store-has-native-type
 (implies (fn-lbc-p fn-lbc) (fn-dmapp (fn-lbc-number-store fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-number-store fn-lbc-number-storep)))))

(defthm fn-lbc-slot-store-has-native-type
 (implies (fn-lbc-p fn-lbc) (fn-lbc-msgid-slotsp (fn-lbc-slot-store fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-slot-store fn-lbc-slot-storep)))))

(defthm fn-lbc-directory-store-has-native-type
 (implies (fn-lbc-p fn-lbc) (fn-lbc-directoryp (fn-lbc-directory-store fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-directory-store fn-lbc-directory-storep)))))

(defthm fn-lbc-membership-store-has-native-type
 (implies (fn-lbc-p fn-lbc) (fn-lbc-membershipsp (fn-lbc-membership-store fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-membership-store fn-lbc-membership-storep)))))

(defthm fn-lbc-nov-store-has-native-type
 (implies (fn-lbc-p fn-lbc) (fn-lbc-novp (fn-lbc-nov-store fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-p fn-lbc-nov-store fn-lbc-nov-storep)))))

(local (defthm fn-lbcht-octet-cell-type
 (implies (fn-cbor-octetp byte) (adt-rec-p '((:u8)) (list byte)))
 :hints (("Goal" :in-theory (enable adt-rec-p adt-val-okp fn-cbor-octetp unsigned-byte-p integer-range-p)))))

(defthm fn-lbc-p-of-msgid-pool-append
 (implies (and (fn-lbc-p fn-lbc) (fn-cbor-octet-listp bytes))
 (fn-lbc-p (fn-lbc-msgid-pool-append bytes fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-msgid-pool-append bytes fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-msgid-pool-append fn-cbor-octet-listp fn-lbcht-octet-cell-type
 fn-lbc-msgid-octetsp-of-append fn-lbc-msgid-store-has-native-type
 fn-lbc-p-of-update-msgid-store)))))

(defthm fn-lbc-p-of-overview-pool-append
 (implies (and (fn-lbc-p fn-lbc) (fn-cbor-octet-listp bytes))
 (fn-lbc-p (fn-lbc-overview-pool-append bytes fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-overview-pool-append bytes fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-overview-pool-append fn-cbor-octet-listp fn-lbcht-octet-cell-type
 fn-lbc-overview-octetsp-of-append fn-lbc-overview-store-has-native-type
 fn-lbc-p-of-update-overview-store)))))

(defthm fn-lbc-p-of-number-put-first
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-number-put-first group number i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-number-put-first fn-dmapp-of-put fn-dm-lanep fn-lbc-p-of-update-number-store
 fn-lbc-number-store-has-native-type)))))

(defthm fn-lbc-p-of-number-put-row-seen
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-number-put-row-seen numbers seen i fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-number-put-row-seen numbers seen i fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-number-put-row-seen fn-lbc-p-of-number-put-first)))))

(defthm fn-lbc-p-of-number-put-row
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-number-put-row numbers i fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-number-put-row fn-lbc-p-of-number-put-row-seen)))))

(defthm fn-lbc-p-of-summary-put
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-summary-put group values field fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-summary-put group values field fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-summary-put fn-dmapp-of-put fn-dm-lanep fn-lbc-p-of-update-number-store
 fn-lbc-number-store-has-native-type)))))

(defthm fn-lbc-p-of-rebuild-summaries
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-rebuild-summaries groups rows fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-rebuild-summaries groups rows fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory) '(fn-lbc-rebuild-summaries fn-lbc-p-of-summary-put)))))

(defthm fn-lbc-p-of-reserve-slots
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-reserve-slots n fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-reserve-slots n fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-reserve-slots fn-lbc-msgid-slotsp-of-append fn-lbc-slot-store-has-native-type
 fn-lbc-p-of-update-slot-store adt-rec-p adt-val-okp)))))
