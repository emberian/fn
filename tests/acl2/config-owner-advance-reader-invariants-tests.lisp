(in-package "ACL2")
(include-book "../../books/config-owner-advance-reader-invariants")
(include-book "config-owner-advance-invariants-tests")
(include-book "std/testing/must-fail" :dir :system)

(assert-event (fn-ocri-relation *ocl-t-new-open*))
(assert-event (fn-ocri-relation *ocla-t-advanced*))
(assert-event
 (let* ((conn (fn-own-find-conn
               0 (fn-own-conns (fn-ocfg-owner *ocla-t-advanced*)))))
   (and (fn-wire-statep (fn-own-conn-wire conn))
        (fn-sn-verdict-listp (fn-own-conn-verdicts conn))
        (fn-midx-correspondencep
         (fn-own-conn-index conn)
         (fn-state-articles (fn-own-conn-archive conn))))))

; A forged old pin lies outside the strengthened reader relation.  A duplicate
; ID additionally survives an attempted repin and remains outside it.
(assert-event (not (fn-ocri-relation *ocl-t-forged-old-pin*)))
(assert-event
 (not (fn-ocri-relation
       (fn-ocfg-advance *ocla-t-duplicate* 0))))
(local
 (must-fail
  (defthm fn-ocari-advance-without-reader-relation
    (fn-ocri-relation (fn-ocfg-advance oc id))
    :rule-classes nil)))
