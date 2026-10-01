; Additive concrete sized child parse over unchanged public STXE semantics.
(in-package "ACL2")
(include-book "stx-evidence-records")
(include-book "statement-codec-size-reader")

(local (defthm fn-stxs-concrete-encoding-is-public
 (equal (fn-stmt-encode-items-impl items) (fn-stmt-encode-items items))
 :hints (("Goal" :induct (len items)
          :in-theory (enable fn-stmt-encode-items-impl)))))

(defun fn-stxs-size-at (n sizes)
 (declare (xargs :guard (natp n)))
 (if (zp n) (if (consp sizes) (car sizes) nil)
  (fn-stxs-size-at (1- n) (if (consp sizes) (cdr sizes) nil))))

(defun fn-stxs-decode (octets)
 (declare (xargs :guard t))
 (if (not (fn-cbor-at-mostp octets *fn-stxe-max-octets*))
  (mv (fn-stmt-error :limit) nil)
  (mv-let (decoded sizes)
   (fn-stmt-decode-items-sized-bounded-impl
    11 octets *fn-cbor-max-input* *fn-cbor-max-bytes*)
   (if (not (fn-stmt-okp decoded)) (mv decoded nil)
    (let ((result (fn-stxe-of-items (fn-stmt-value decoded))))
     (mv result (if (fn-stmt-okp result)
       (list (fn-stxs-size-at 6 sizes) (fn-stxs-size-at 8 sizes)
             (fn-stxs-size-at 10 sizes)) nil)))))))

(local (defthm fn-stxs-public-success-is-concrete
 (implies (and (natp fuel) (<= (len octets) *fn-cbor-max-input*)
  (fn-stmt-okp (fn-stmt-decode-items fuel octets))
  (<= (len (fn-stmt-value (fn-stmt-decode-items fuel octets))) fuel))
  (equal (fn-stmt-decode-items-bounded-impl fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*)
         (fn-stmt-ok (fn-stmt-value (fn-stmt-decode-items fuel octets)))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-stmt-impl-decode-items-bounded-of-encode
       (items (fn-stmt-value (fn-stmt-decode-items fuel octets))))
        (:instance fn-stmt-decode-items-bounded-canonical)
        (:instance fn-stmt-decode-items-bounded-items))
  :in-theory (e/d (fn-stmt-decode-items fn-stmt-okp fn-stmt-value)
   (fn-stmt-decode-items-bounded-impl
    fn-stmt-encode-items-impl
    fn-stmt-decode-items-bounded-canonical fn-stmt-decode-items-bounded-items
    ))))))
(local (defthm fn-stxs-concrete-success-is-public
 (implies (and (natp fuel) (<= (len octets) *fn-cbor-max-input*)
  (fn-stmt-okp (fn-stmt-decode-items-bounded-impl fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))
  (<= (len (fn-stmt-value (fn-stmt-decode-items-bounded-impl fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))) fuel))
  (equal (fn-stmt-decode-items fuel octets)
   (fn-stmt-ok (fn-stmt-value (fn-stmt-decode-items-bounded-impl fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*)))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-stmt-decode-items-bounded-of-encode
       (items (fn-stmt-value (fn-stmt-decode-items-bounded-impl fuel octets *fn-cbor-max-input* *fn-cbor-max-bytes*))))
        (:instance fn-stmt-impl-decode-items-bounded-canonical)
        (:instance fn-stmt-impl-decode-items-bounded-items))
  :in-theory (e/d (fn-stmt-decode-items fn-stmt-okp fn-stmt-value)
   (fn-stmt-decode-items-bounded-impl fn-stmt-encode-items-impl
    fn-stmt-decode-items-bounded-of-encode))))))
(local (defthm fn-stxs-at-mostp-bound
 (implies (and (natp n) (fn-cbor-at-mostp xs n)) (<= (len xs) n))
 :hints (("Goal" :induct (fn-cbor-at-mostp xs n)
          :in-theory (enable fn-cbor-at-mostp)))))

(local (defthm fn-stxs-of-items-success-length
 (implies (fn-stmt-okp (fn-stxe-of-items items)) (equal (len items) 11))
 :hints (("Goal" :in-theory (e/d (fn-stxe-of-items fn-stxe-items-p)
  (fn-record-msgidp fn-record-octets-string fn-stxe-make fn-stxe-code-token
   fn-stxe-tokenp fn-stxe-bounded-octetsp))))))
(defthm fn-stxs-decode-ok-is-public
 (equal (fn-stmt-okp (mv-nth 0 (fn-stxs-decode octets)))
        (fn-stmt-okp (fn-stxe-decode-exact octets)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-stxs-public-success-is-concrete (fuel 11))
        (:instance fn-stxs-concrete-success-is-public (fuel 11))
        (:instance fn-stmt-sized-bounded-projection-by-definition
          (fuel 11) (outer-budget *fn-cbor-max-input*) (item-budget *fn-cbor-max-bytes*)))
  :in-theory (e/d (fn-stxs-decode fn-stxe-decode-exact fn-stmt-okp fn-stmt-value fn-stmt-ok)
   (fn-stmt-decode-items-sized-bounded-impl fn-stmt-decode-items-bounded-impl
    fn-stmt-decode-items fn-stxe-of-items fn-cbor-at-mostp)))))
(defthm fn-stxs-decode-success-value-is-public
 (implies (fn-stmt-okp (mv-nth 0 (fn-stxs-decode octets)))
 (equal (fn-stmt-value (mv-nth 0 (fn-stxs-decode octets)))
        (fn-stmt-value (fn-stxe-decode-exact octets))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-stxs-public-success-is-concrete (fuel 11))
        (:instance fn-stxs-concrete-success-is-public (fuel 11))
        (:instance fn-stmt-sized-bounded-projection-by-definition
          (fuel 11) (outer-budget *fn-cbor-max-input*) (item-budget *fn-cbor-max-bytes*)))
  :in-theory (e/d (fn-stxs-decode fn-stxe-decode-exact fn-stmt-okp fn-stmt-value fn-stmt-ok)
   (fn-stmt-decode-items-sized-bounded-impl fn-stmt-decode-items-bounded-impl
    fn-stmt-decode-items fn-stxe-of-items fn-cbor-at-mostp)))))
(local (defun fn-stxe-provenance-induct (n items sizes)
 (if (or (zp n) (atom items)) (list items sizes)
  (fn-stxe-provenance-induct (1- n) (cdr items) (if (consp sizes) (cdr sizes) nil)))))

(local (defthm fn-stxe-provenance-at
 (implies (and (natp n) (fn-stmt-item-sizes-correspondsp items sizes))
  (equal (fn-stxs-size-at n sizes)
         (if (equal (car (nth n items)) :bytes) (len (cdr (nth n items))) nil)))
 :hints (("Goal" :induct (fn-stxe-provenance-induct n items sizes)
          :in-theory (enable fn-stxe-provenance-induct fn-stxs-size-at
                             fn-stmt-item-sizes-correspondsp nth)))))

(local (defthm fn-stxe-octet-chars-length
 (equal (len (fn-record-octets-chars xs)) (len xs))
 :hints (("Goal" :in-theory (enable fn-record-octets-chars)))))

(local (defthm fn-stxe-octet-chars-characters
 (character-listp (fn-record-octets-chars xs))
 :hints (("Goal" :in-theory (enable fn-record-octets-chars)))))

(local (defthm fn-stxe-octets-string-length
 (implies (fn-cbor-octet-listp xs)
          (equal (length (fn-record-octets-string xs)) (len xs)))
 :hints (("Goal" :in-theory (e/d (fn-record-octets-string length)
                                (fn-record-octets-chars))))))
(defthm fn-stxs-success-byte-lengths-correspond
 (implies (fn-stmt-okp (mv-nth 0 (fn-stxs-decode octets)))
  (equal (mv-nth 1 (fn-stxs-decode octets))
         (let ((e (fn-stmt-value (mv-nth 0 (fn-stxs-decode octets)))))
           (list (length (fn-stxe-msgid e))
                 (len (fn-stxe-detail e)) (len (fn-stxe-profile e))))))
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-stmt-sized-bounded-lengths-correspond
                          (fuel 11) (outer-budget *fn-cbor-max-input*)
                          (item-budget *fn-cbor-max-bytes*)))
          :in-theory (e/d (fn-stxs-decode fn-stxe-of-items
                            fn-stxe-items-p fn-stxe-make fn-stxe-msgid
                            fn-stxe-detail fn-stxe-profile fn-stmt-ok fn-stmt-okp
                            fn-stmt-value fn-stmt-bytes-item-p fn-cbor-ag-cdr)
                           (fn-stmt-decode-items-sized-bounded-impl fn-stmt-decode-items-sized-prechecked
                            fn-stmt-decode-items-prechecked fn-stmt-decode-items-bounded-impl
                            fn-stmt-sized-prechecked-projection-by-definition
                            fn-stmt-sized-bounded-lengths-correspond
                            fn-record-octets-string fn-stxs-size-at
                            fn-stmt-item-sizes-correspondsp
                            fn-cbor-octet-listp fn-cbor-at-mostp)))))
