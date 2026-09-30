; Exact unchanged decoder semantic functions/support factored from statement-codec.
(in-package "ACL2")
(include-book "cbor")
(include-book "statement-results")

(local (in-theory (enable fn-cbor-codec-vocabulary)))

(local (defthm fn-stmt-reference-octet-listp-of-nthcdr
 (implies (fn-cbor-octet-listp xs)
          (fn-cbor-octet-listp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs)
          :in-theory (enable fn-cbor-octet-listp nthcdr)))))

(defthm fn-stmt-cbor-decode-argument-true-listp
  (true-listp (fn-cbor-decode-argument additional xs)))

(defthm fn-stmt-cbor-decode-unsigned-true-listp
  (true-listp (fn-cbor-decode-unsigned additional tail)))

(defthm fn-stmt-cbor-decode-bytes-true-listp
  (true-listp (fn-cbor-decode-bytes additional tail)))

(defthm fn-stmt-cbor-decode-bounded-true-listp
  (true-listp (fn-cbor-decode-bounded octets input-budget item-budget)))

(defthm fn-stmt-cbor-decode-prechecked-true-listp
  (true-listp (fn-cbor-decode-prechecked octets item-budget)))

(defthm fn-stmt-cbor-decode-true-listp
  (true-listp (fn-cbor-decode octets)))

(defun fn-stmt-decode-prefix-items-prechecked (count octets item-budget)
  (declare (xargs :guard (and (natp count)
                              (fn-cbor-octet-listp octets)
                              (natp item-budget))
                  :measure (nfix count)))
  (if (zp count)
      (fn-stmt-ok2 nil octets)
    (let ((first (fn-cbor-decode-prechecked octets item-budget)))
      (if (not (fn-cbor-result-okp first))
          (fn-stmt-error (fn-stmt-value first))
        (let ((tail (fn-stmt-decode-prefix-items-prechecked
                     (1- count) (fn-cbor-result-rest first) item-budget)))
          (if (not (fn-stmt-okp tail))
              tail
            (fn-stmt-ok2 (cons (fn-cbor-result-value first)
                               (fn-stmt-value tail))
                         (fn-stmt-rest tail))))))))

(defun fn-stmt-decode-items-prechecked (fuel octets item-budget)
  (declare (xargs :guard (and (natp fuel)
                              (fn-cbor-octet-listp octets)
                              (natp item-budget))
                  :measure (nfix fuel)))
  (if (atom octets)
      (fn-stmt-ok nil)
    (if (zp fuel)
        (fn-stmt-error :too-many-items)
      (let ((first (fn-cbor-decode-prechecked octets item-budget)))
        (if (not (fn-cbor-result-okp first))
            (fn-stmt-error (fn-stmt-value first))
          (let ((tail (fn-stmt-decode-items-prechecked
                       (1- fuel) (fn-cbor-result-rest first) item-budget)))
            (if (not (fn-stmt-okp tail))
                tail
              (fn-stmt-ok (cons (fn-cbor-result-value first)
                                (fn-stmt-value tail))))))))))

(defun fn-stmt-decode-items-bounded-impl (fuel octets outer-budget item-budget)
  (declare (xargs :guard (and (natp fuel) (natp outer-budget)
                              (natp item-budget))))
  ; One bounded preflight and octet validation occur before recursive parsing.
  (if (not (fn-cbor-at-mostp octets outer-budget))
      (fn-stmt-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-stmt-error :malformed)
      (fn-stmt-decode-items-prechecked fuel octets item-budget))))

(defun fn-stmt-decode-items-impl (fuel octets)
  (declare (xargs :guard (natp fuel)))
  ; Compatibility wrapper for every pre-existing statement caller.
  (fn-stmt-decode-items-bounded-impl fuel octets
                                *fn-cbor-max-input* *fn-cbor-max-bytes*))

(defun fn-stmt-decode-prefix-items-bounded-impl
  (count octets outer-budget item-budget)
  (declare (xargs :guard (and (natp count) (natp outer-budget)
                              (natp item-budget))))
  (if (not (fn-cbor-at-mostp octets outer-budget))
      (fn-stmt-error :limit)
    (if (not (fn-cbor-octet-listp octets))
        (fn-stmt-error :malformed)
      (fn-stmt-decode-prefix-items-prechecked count octets item-budget))))

(in-theory (disable fn-stmt-decode-prefix-items-prechecked
 fn-stmt-decode-prefix-items-bounded-impl fn-stmt-decode-items-prechecked
 fn-stmt-decode-items-bounded-impl fn-stmt-decode-items-impl))
