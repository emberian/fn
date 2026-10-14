; fn: shared invariant projections and request configuration framing.
(in-package "ACL2")
(include-book "runtime-contract-invariant")

(defthm fn-rtc-invp-has-static-records
  (implies (fn-rtc-invp s)
           (fn-rtc-statics-okp 1 (fn-rtc-nstatic (fn-rtc-config s)) (fn-rtc-slots s)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-invp)))))
(defthm fn-rtc-requests-config-frame
  (equal (fn-rtc-config (mv-nth 0 (fn-rtc-requests reqs id inc s))) (fn-rtc-config s))
  :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
           :in-theory (e/d (fn-rtc-requests fn-rtc-request-config-frame)
                           (mv-nth fn-rtc-request)))))
(in-theory (disable fn-rtc-requests-config-frame))
