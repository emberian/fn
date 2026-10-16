; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-locator-native-types")

(defthm fn-lbc-at-is-corresponding-row
 (implies (and (fn-cat-rowp row) (fn-lbc-row-corr i row pm fn-lbc log))
 (equal (fn-lbc-at i fn-lbc log) row))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-reconstitute-row-is-original))
 :in-theory (set-difference-theories (union-theories (theory 'ground-zero)
 '(fn-lbc-at-by-reconstitution-definition fn-lbc-row-corr fn-cat-rowp)) '((tau-system))))))

(local (defthm fn-lbrlr-wire-proper
 (true-listp (fn-lb-log-model-wire payload startp)) :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :induct (fn-lb-log-model-wire payload startp)
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lb-log-model-wire binary-append true-listp))))))

(local (defthm fn-lbrlr-expected-range-not-bad
 (not (equal (fn-lc-expected-range payload) :bad))
 :hints (("Goal" :do-not-induct t :cases ((equal payload :bad))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lc-expected-range fn-la-payload-wire fn-la-tombstone-raw
 fn-lbrlr-wire-proper true-listp (:executable-counterpart fn-rcl-tombstonep)))))))

(local (defthm fn-lbrlr-home-frame-not-bad
 (implies (fn-cat-rowp row) (not (equal (fn-lb-log-model-home-frame row) :bad)))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lb-log-model-home-frame-is-octets))
 :cases ((equal (fn-lb-log-model-home-frame row) :bad))
 :in-theory (union-theories (theory 'ground-zero) '((:executable-counterpart fn-cbor-octet-listp)))))))

(local (defthm fn-lbrlr-row-corr-read-fields
 (implies (fn-lbc-row-corr i row pm fn-lbc log)
 (let ((a (fn-lbc-loc0 i fn-lbc)) (b (fn-lbc-loc1 i fn-lbc)))
 (and (equal (fn-lc-read-range a b log) (fn-lc-expected-range (fn-lb-log-payload row log)))
      (equal (fn-lc-read-home-frame (fn-lc-home-position a b) log) (fn-lc-expected-home-frame row)))))
 :hints (("Goal" :do-not-induct t :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-row-corr fn-lc-read-range fn-lc-read-home-frame fn-lc-home-position
 fn-lc-expected-range fn-lc-expected-home-frame))))))

(defthm fn-lbc-corresponding-row-locator-resolves
 (implies (and (fn-lbc-p fn-lbc) (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-cat-rowp row) (fn-held-p row) (fn-lbc-row-corr i row pm fn-lbc log))
 (fn-lc-locator-resolves fn-lbc i log))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-lbrlr-row-corr-read-fields))
 :in-theory (union-theories (theory 'ground-zero)
 '(fn-lc-locator-resolves fn-lc-bound-row fn-lbc-at-is-corresponding-row
 fn-lbc-locator-has-native-domain fn-lbrlr-expected-range-not-bad
 fn-lbrlr-home-frame-not-bad fn-lc-expected-home-frame)))))
