; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-log-append-segment")
(include-book "lb-log-model-properties")

(local (defthm fn-lblnt-len-append
 (equal (len (append x y)) (+ (len x) (len y)))
 :hints (("Goal" :induct (len x) :in-theory (enable binary-append len)))))

(local (defthm fn-lblnt-proper-append
 (implies (true-listp y) (true-listp (append x y)))
 :hints (("Goal" :induct (len x) :in-theory (enable binary-append true-listp)))))

(local (defthm fn-lblnt-nat-octets-proper
 (true-listp (fn-lb-log-model-nat-octets n))
 :hints (("Goal" :induct (fn-lb-log-model-nat-octets n)
 :in-theory (enable fn-lb-log-model-nat-octets)))))

(local (defthm fn-lblnt-value-octets-proper
 (true-listp (fn-lb-log-model-value-octets value))
 :hints (("Goal" :induct (fn-lb-log-model-value-octets value)
 :in-theory (enable fn-lb-log-model-value-octets))) :rule-classes :type-prescription))

(defthm fn-lb-log-model-home-frame-true-listp
 (implies (fn-cat-rowp row) (true-listp (fn-lb-log-model-home-frame row)))
 :hints (("Goal" :in-theory (enable fn-lb-log-model-home-frame))))

(defthm fn-lb-log-model-pre-true-listp
 (true-listp (fn-lb-log-model-pre row payload))
 :hints (("Goal" :in-theory (enable fn-lb-log-model-pre))))

(defthm fn-lb-log-next-range-true-listp
 (implies (true-listp payload) (true-listp (fn-lb-log-model-next-range payload)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-next-range fn-la-tombstone-raw fn-lb-log-model-payload-wire-true-listp)))))

(defthm fn-lb-log-next-prefix-true-listp
 (implies (fn-cat-rowp row) (true-listp (fn-lb-log-model-next-prefix row payload)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-next-prefix fn-lblnt-proper-append fn-lb-log-model-home-frame-true-listp)))))

(local (defthm fn-lblnt-row-types
 (implies (fn-cat-rowp row)
 (and (natp (fn-record-payload row)) (fn-record-uint64p (fn-record-sequence row))))
 :hints (("Goal" :in-theory (enable fn-cat-rowp)))))

(local (defthm fn-lblnt-homes-shape
 (and (true-listp (fn-lb-log-model-homes row)) (equal (len (fn-lb-log-model-homes row)) 5))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-lb-log-model-homes car-cons cdr-cons len true-listp (:executable-counterpart binary-+)))))))

(local (defthm fn-lblnt-nth-cons
 (equal (nth i (cons x xs)) (if (zp i) x (nth (- (nfix i) 1) xs)))
 :hints (("Goal" :in-theory (enable nth)))))

(defthm fn-lb-log-next-entry-well-typed
 (implies (and (fn-cat-rowp row) (fn-cbor-octet-listp payload))
 (fn-lb-log-model-entryp (fn-lb-log-model-next-entry row payload segment)))
 :hints (("Goal" :do-not-induct t :in-theory
 (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-entryp fn-lb-log-model-next-entry fn-lb-log-model-next-prefix
 fn-lblnt-len-append fn-lblnt-row-types fn-lblnt-homes-shape fn-lblnt-nth-cons)))))
