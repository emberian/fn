(in-package "ACL2")

(include-book "statement-codec")

(include-book "cbor-size-reader")

(include-book "statement-size-values")

(local
 (defthm fn-stmt-sized-octet-listp-of-nthcdr
   (implies (fn-cbor-octet-listp xs)
            (fn-cbor-octet-listp (nthcdr n xs)))))

(local
 (defthm fn-stmt-sized-cbor-rest-octets
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-cbor-result-okp (fn-cbor-decode-prechecked octets budget)))
            (fn-cbor-octet-listp
             (fn-cbor-result-rest (fn-cbor-decode-prechecked octets budget))))
   :hints (("Goal" :in-theory
            (e/d (fn-cbor-codec-vocabulary)
                 (fn-cbor-u16-from fn-cbor-u32-from take))))))

(defun fn-stmt-decode-items-sized-prechecked (fuel octets item-budget)
  (declare (xargs :guard (and (natp fuel) (fn-cbor-octet-listp octets)
                              (natp item-budget))
                  :measure (nfix fuel)))
  (if (atom octets)
      (mv (fn-stmt-ok nil) nil)
    (if (zp fuel)
        (mv (fn-stmt-error :too-many-items) nil)
      (mv-let (first size) (fn-cbor-decode-sized-prechecked octets item-budget)
        (if (not (fn-cbor-result-okp first))
            (mv (fn-stmt-error (fn-stmt-value first)) nil)
          (mv-let (tail sizes)
              (fn-stmt-decode-items-sized-prechecked
               (1- fuel) (fn-cbor-result-rest first) item-budget)
            (if (not (fn-stmt-okp tail))
                (mv tail nil)
              (mv (fn-stmt-ok (cons (fn-cbor-result-value first)
                                    (fn-stmt-value tail)))
                  (cons size sizes)))))))))

(defthm fn-stmt-sized-prechecked-projection-by-definition
  (equal (mv-nth 0 (fn-stmt-decode-items-sized-prechecked fuel octets item-budget))
         (fn-stmt-decode-items-prechecked fuel octets item-budget))
  :hints (("Goal" :induct (fn-stmt-decode-items-sized-prechecked fuel octets item-budget)
           :in-theory (e/d (fn-stmt-decode-items-sized-prechecked
                             fn-stmt-decode-items-prechecked)
                            (fn-cbor-decode-sized-prechecked
                             fn-cbor-decode-prechecked)))))

(defun fn-stmt-decode-items-sized-bounded-impl
  (fuel octets outer-budget item-budget)
  (declare (xargs :guard (and (natp fuel) (natp outer-budget)
                              (natp item-budget))))
  (if (not (fn-cbor-at-mostp octets outer-budget))
      (mv (fn-stmt-error :limit) nil)
    (if (not (fn-cbor-octet-listp octets))
        (mv (fn-stmt-error :malformed) nil)
      (fn-stmt-decode-items-sized-prechecked fuel octets item-budget))))

(local
 (defthm fn-stmt-sized-first-item-length
   (implies (and (fn-cbor-octet-listp octets)
                 (fn-cbor-result-okp (fn-cbor-decode-prechecked octets item-budget)))
            (equal (mv-nth 1 (fn-cbor-decode-sized-prechecked octets item-budget))
                   (if (equal (car (fn-cbor-result-value
                                    (fn-cbor-decode-prechecked octets item-budget))) :bytes)
                       (len (cdr (fn-cbor-result-value
                                  (fn-cbor-decode-prechecked octets item-budget)))) nil)))
   :hints (("Goal" :use fn-cbor-sized-item-length-corresponds
            :in-theory (disable fn-cbor-sized-item-length-corresponds
                                fn-cbor-decode-prechecked
                                fn-cbor-decode-sized-prechecked)))))

(defthm fn-stmt-sized-prechecked-lengths-correspond
  (implies (and (fn-cbor-octet-listp octets)
                (fn-stmt-okp
                 (mv-nth 0 (fn-stmt-decode-items-sized-prechecked fuel octets item-budget))))
           (fn-stmt-item-sizes-correspondsp
            (fn-stmt-value
             (mv-nth 0 (fn-stmt-decode-items-sized-prechecked fuel octets item-budget)))
            (mv-nth 1 (fn-stmt-decode-items-sized-prechecked fuel octets item-budget))))
  :hints (("Goal" :induct (fn-stmt-decode-items-sized-prechecked fuel octets item-budget)
           :in-theory
           (e/d (fn-stmt-decode-items-sized-prechecked fn-stmt-item-sizes-correspondsp)
                (fn-stmt-sized-prechecked-projection-by-definition
                 fn-stmt-decode-items-prechecked fn-cbor-decode-prechecked
                 fn-cbor-decode-sized-prechecked)))))

(defthm fn-stmt-sized-bounded-projection-by-definition
  (equal (mv-nth 0 (fn-stmt-decode-items-sized-bounded-impl
                    fuel octets outer-budget item-budget))
         (fn-stmt-decode-items-bounded-impl fuel octets outer-budget item-budget))
  :rule-classes nil
  :hints (("Goal" :use fn-stmt-sized-prechecked-projection-by-definition
           :in-theory
           (e/d (fn-stmt-decode-items-bounded-impl
                 fn-stmt-decode-items-sized-bounded-impl)
                (fn-stmt-sized-prechecked-projection-by-definition
                 fn-stmt-decode-items-prechecked
                 fn-stmt-decode-items-sized-prechecked)))))

(defthm fn-stmt-sized-bounded-lengths-correspond
  (implies (fn-stmt-okp
            (mv-nth 0 (fn-stmt-decode-items-sized-bounded-impl
                       fuel octets outer-budget item-budget)))
           (fn-stmt-item-sizes-correspondsp
            (fn-stmt-value
             (mv-nth 0 (fn-stmt-decode-items-sized-bounded-impl
                        fuel octets outer-budget item-budget)))
            (mv-nth 1 (fn-stmt-decode-items-sized-bounded-impl
                       fuel octets outer-budget item-budget))))
  :hints (("Goal" :use fn-stmt-sized-prechecked-lengths-correspond
           :in-theory
           (e/d (fn-stmt-decode-items-sized-bounded-impl)
                (fn-stmt-sized-prechecked-lengths-correspond
                 fn-stmt-sized-prechecked-projection-by-definition
                 fn-stmt-decode-items-prechecked
                 fn-stmt-value fn-stmt-okp fn-cbor-at-mostp
                 fn-cbor-octet-listp)))))
