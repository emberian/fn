; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-constructor-helper-types")
(local (include-book "arithmetic-5/top" :dir :system))

(local (defthm fn-lbrpt-string-aux-octets
 (fn-cbor-octet-listp (fn-record-string-octets-aux chars))
 :hints (("Goal" :induct (fn-record-string-octets-aux chars)
 :in-theory (enable fn-record-string-octets-aux fn-cbor-octet-listp fn-cbor-octetp)))))

(defthm fn-lbc-string-octets-are-octets
 (fn-cbor-octet-listp (fn-record-string-octets text))
 :hints (("Goal" :in-theory (set-difference-theories
 (union-theories (theory 'ground-zero)
 '(fn-record-string-octets fn-lbrpt-string-aux-octets fn-cbor-octet-listp))
 '((tau-system))))))

(defthm fn-lbc-u64-has-native-type
 (unsigned-byte-p 64 (fn-lbc-u64 x))
 :hints (("Goal" :in-theory (enable fn-lbc-u64))))

(local (defthm fn-lbrpt-nov-booleans
 (implies (fn-lbc-nov-smallp nov) (and (booleanp (fn-hnov-tomb nov)) (booleanp (fn-hnov-ok nov))))
 :hints (("Goal" :in-theory (enable fn-lbc-nov-smallp fn-hnov-p)))))

(defthm fn-lbc-nov-record-has-native-type
 (implies (fn-lbc-nov-smallp nov)
 (adt-rec-p '((:bool) (:bool) (:u64) (:u64) (:u64) (:u64) (:u64) (:u64) (:u64) (:u64) (:u64) (:u64))
  (cons (fn-hnov-tomb nov) (cons (fn-hnov-ok nov)
    (fn-lbc-nov-spans (fn-lbc-nov-texts nov) offset)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(adt-rec-p adt-val-okp fn-lbc-nov-spans fn-lbc-nov-texts fn-lbrpt-nov-booleans
 fn-lbc-u64-has-native-type)))))

(defthm fn-lbc-membership-record-has-native-type
 (adt-rec-p '((:u64) (:u64) (:u64))
 (list (fn-lbc-u64 start) (fn-lbc-u64 count) (if numbersp (fn-lbc-u64 number) 0)))
 :hints (("Goal" :do-not-induct t :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(adt-rec-p adt-val-okp fn-lbc-u64-has-native-type)) '(unsigned-byte-p)))))

(defthm fn-lbc-p-of-append-nov-texts
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-append-nov-texts texts fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-append-nov-texts texts fn-lbc)
 :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lbc-append-nov-texts fn-lbc-string-octets-are-octets fn-lbc-p-of-overview-pool-append)))))

(defthm fn-lbc-p-of-append-nov
 (implies (and (fn-lbc-p fn-lbc) (fn-lbc-nov-smallp nov))
 (fn-lbc-p (fn-lbc-append-nov nov fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-append-nov fn-lbc-nov-record-has-native-type fn-lbc-p-of-append-nov-texts
 fn-lbc-nov-store-has-native-type fn-lbc-novp-of-append fn-lbc-p-of-update-nov-store)))))

(defthm fn-lbc-p-of-append-memberships
 (implies (fn-lbc-p fn-lbc) (fn-lbc-p (fn-lbc-append-memberships items numbersp fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-append-memberships items numbersp fn-lbc)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-append-memberships fn-lbc-membership-record-has-native-type fn-lbc-p-of-overview-pool-append
 fn-lbc-string-octets-are-octets fn-lbc-membership-store-has-native-type fn-lbc-membershipsp-of-append
 fn-lbc-p-of-update-membership-store)))))
