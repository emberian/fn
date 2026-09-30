; Additive same-parser whole snapshot row carry. No readiness or funding issuer.
(in-package "ACL2")
(include-book "stx-keyring-records")
(include-book "store-tree-size")

(defun fn-stxks-size-at (n sizes)
 (declare (xargs :guard (natp n)))
 (if (zp n) (if (consp sizes) (car sizes) nil)
  (fn-stxks-size-at (1- n) (if (consp sizes) (cdr sizes) nil))))

(defun fn-stxks-row-carry (items profile-size snapshot-size)
 (declare (xargs :guard (and (true-listp items) (fn-stmt-uint-item-p (nth 3 items))
                             (fn-stmt-uint-item-p (nth 4 items))
                             (fn-stmt-uint-item-p (nth 5 items))
                             (fn-stmt-uint-item-p (nth 6 items))
                             (natp profile-size) (natp snapshot-size))
                 :verify-guards nil))
 (fn-scs-spine
  (list (fn-scs-atom (fn-cbor-ag-cdr (nth 3 items)))
        (fn-scs-atom (fn-cbor-ag-cdr (nth 4 items)))
        (fn-scs-atom (fn-cbor-ag-cdr (nth 5 items)))
        (fn-scs-atom (fn-cbor-ag-cdr (nth 6 items)))
        (fn-scs-octets profile-size) (fn-scs-octets snapshot-size))))

(defun fn-stxks-decode (octets)
 (declare (xargs :guard t :verify-guards nil))
 (if (not (fn-cbor-at-mostp octets *fn-stxk-max-octets*))
  (mv (fn-stmt-error :limit) nil)
  (mv-let (decoded sizes)
   (fn-stmt-decode-items-sized-bounded
    9 octets *fn-stxk-max-octets* *fn-stxk-max-snapshot*)
   (if (not (fn-stmt-okp decoded)) (mv decoded nil)
    (let* ((items (fn-stmt-value decoded))
           (result (fn-stxk-of-items items))
           (profile-size (fn-stxks-size-at 7 sizes))
           (snapshot-size (fn-stxks-size-at 8 sizes)))
     (mv result
      (if (and (fn-stmt-okp result) (natp profile-size) (natp snapshot-size))
       (fn-stxks-row-carry items profile-size snapshot-size) nil)))))))

(defthm fn-stxks-first-result-is-public-decoder
 (equal (mv-nth 0 (fn-stxks-decode octets)) (fn-stxk-decode-exact octets))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (e/d (fn-stxks-decode fn-stxk-decode-exact)
   (fn-stxk-of-items fn-stxk-items-p fn-stmt-okp fn-stmt-value fn-cbor-at-mostp
    fn-stxks-row-carry fn-stxks-size-at)))))

(local (defthm fn-stxks-octets-carryp
 (implies (natp n) (fn-scs-carryp (fn-scs-octets n)))
 :hints (("Goal" :in-theory (enable fn-scs-octets fn-scs-carryp fn-scs-atom)))))

(verify-guards fn-stxks-row-carry
 :hints (("Goal" :do-not-induct t :in-theory
  (e/d (fn-stxk-items-p fn-record-uint32p fn-stmt-uint-item-p fn-cbor-ag-cdr fn-scs-carry-listp)
       (fn-scs-atom fn-scs-octets fn-stxe-bounded-octetsp
        fn-stmt-bytes-item-p fn-cbor-octet-listp)))))
(verify-guards fn-stxks-decode)

(local (defun fn-stxks-provenance-induct (n items sizes)
 (if (or (zp n) (atom items)) (list items sizes)
  (fn-stxks-provenance-induct (1- n) (cdr items) (if (consp sizes) (cdr sizes) nil)))))
(local (defthm fn-stxks-provenance-at
 (implies (and (natp n) (fn-stmt-item-sizes-correspondsp items sizes))
  (equal (fn-stxks-size-at n sizes)
         (if (equal (car (nth n items)) :bytes) (len (cdr (nth n items))) nil)))
 :hints (("Goal" :induct (fn-stxks-provenance-induct n items sizes)
          :in-theory (enable fn-stxks-provenance-induct fn-stxks-size-at
                             fn-stmt-item-sizes-correspondsp nth)))))
(local (defthm fn-stxks-cbor-octets-are-store-octets
 (equal (fn-cbor-octet-listp xs) (fn-scc-octet-listp xs))
 :hints (("Goal" :induct (len xs)
          :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp
                             fn-scc-octet-listp fn-scc-octetp)))))
(defthm fn-stxks-row-carry-is-exact
 (implies (and (fn-stxk-items-p items)
               (equal profile-size (len (cdr (nth 7 items))))
               (equal snapshot-size (len (cdr (nth 8 items)))))
  (equal (fn-stxks-row-carry items profile-size snapshot-size)
         (fn-scs-summary (fn-stmt-value (fn-stxk-of-items items)))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-scs-spine-preserves-canonical-size
    (cs (list (fn-scs-atom (cdr (nth 3 items)))
              (fn-scs-atom (cdr (nth 4 items)))
              (fn-scs-atom (cdr (nth 5 items)))
              (fn-scs-atom (cdr (nth 6 items)))
              (fn-scs-octets profile-size) (fn-scs-octets snapshot-size)))
    (xs (list (cdr (nth 3 items)) (cdr (nth 4 items))
              (cdr (nth 5 items)) (cdr (nth 6 items))
              (cdr (nth 7 items)) (cdr (nth 8 items))))))
  :in-theory
  (e/d (fn-stxks-row-carry fn-record-uint32p fn-stxk-items-p fn-stxk-of-items fn-stmt-value
        fn-stmt-ok fn-stxk-make fn-stmt-uint-item-p fn-cbor-ag-cdr
        fn-stxe-bounded-octetsp fn-scs-correspondsp)
       (fn-scs-spine fn-scs-summary fn-scs-atom fn-scs-octets
        fn-cbor-octet-listp fn-stmt-bytes-item-p)))))
(defthm fn-stxks-success-carry-is-whole-row-carry
 (implies (fn-stmt-okp (mv-nth 0 (fn-stxks-decode octets)))
  (equal (mv-nth 1 (fn-stxks-decode octets))
         (fn-scs-summary (fn-stmt-value (mv-nth 0 (fn-stxks-decode octets))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-stmt-sized-result-lengths-correspond
         (fuel 9) (outer-budget *fn-stxk-max-octets*)
         (item-budget *fn-stxk-max-snapshot*)))
  :in-theory
   (e/d (fn-stxks-decode fn-stxk-of-items fn-stmt-okp fn-stmt-value
         fn-stmt-ok fn-stxk-items-p fn-stmt-bytes-item-p fn-cbor-ag-cdr)
        (fn-stxks-row-carry fn-stxks-size-at fn-stmt-item-sizes-correspondsp
         fn-cbor-at-mostp fn-cbor-octet-listp fn-stxk-make fn-scs-summary)))))
