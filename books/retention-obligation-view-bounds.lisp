; W9 numeric payload bounds: derive stored count/charge from ledger capacity.
; The supported-profile codec/runtime bound on that capacity is a separate
; producer obligation; this book does not assume all capacities fit a word.
(in-package "ACL2")
(include-book "retention-obligation-view")
(local (include-book "arithmetic/top" :dir :system))

(defthm fn-rov-pin-count-bounded-by-charge
  (implies (fn-retain-obligation-listp pins)
           (<= (len pins) (fn-retain-sum pins)))
  :hints (("Goal" :induct (len pins)
           :in-theory (enable fn-retain-obligationp fn-retain-sum))))

(defthm fn-rov-oracle-count-bounded-by-pins
  (<= (car (fn-vd-oracle-at subject (fn-rov-contribs pins))) (len pins))
  :hints (("Goal" :induct (len pins)
           :in-theory (enable fn-vd-oracle-at fn-rov-contribs fn-rov-contrib))))

(defthm fn-rov-oracle-charge-bounded-by-pins
  (implies (fn-retain-obligation-listp pins)
           (<= (cdr (fn-vd-oracle-at subject (fn-rov-contribs pins)))
               (fn-retain-sum pins)))
  :hints (("Goal" :induct (len pins)
           :in-theory (enable fn-vd-oracle-at fn-rov-contribs fn-rov-contrib
                              fn-retain-obligationp fn-retain-sum))))

(defthm fn-rov-nonstring-subject-is-zero
  (implies (not (stringp subject))
           (equal (fn-rov-subject subject view) '(0 . 0)))
  :hints (("Goal" :in-theory (enable fn-rov-subject fn-vdc-get fn-mxc-lookup
                                     fn-midx-key-chars fn-mxc-get fn-vd-pairp))))

(defthm fn-rov-count-and-charge-fit-ledger-capacity
  (implies (and (fn-retain-statep ledger)
                (fn-rov-correspondp view (fn-retain-pins ledger)))
           (and (<= (fn-rov-count view) (fn-retain-capacity ledger))
                (<= (car (fn-rov-subject subject view)) (fn-retain-capacity ledger))
                (<= (cdr (fn-rov-subject subject view)) (fn-retain-capacity ledger))))
  :hints (("Goal" :cases ((stringp subject))
           :in-theory (e/d (fn-retain-statep)
                           (fn-rov-correspondp fn-rov-subject fn-rov-count
                            fn-retain-sum fn-vd-oracle-at
                            fn-rov-pin-count-bounded-by-charge
                            fn-rov-oracle-count-bounded-by-pins
                            fn-rov-oracle-charge-bounded-by-pins))
           :use ((:instance fn-rov-pin-count-bounded-by-charge (pins (fn-retain-pins ledger)))
                 (:instance fn-rov-oracle-count-bounded-by-pins (pins (fn-retain-pins ledger)))
                 (:instance fn-rov-oracle-charge-bounded-by-pins (pins (fn-retain-pins ledger)))))))

(defthm fn-rov-count-and-charge-are-uint64
  (implies (and (fn-retain-statep ledger)
                (fn-rov-correspondp view (fn-retain-pins ledger))
                (< (fn-retain-capacity ledger) (expt 2 64)))
           (and (unsigned-byte-p 64 (fn-rov-count view))
                (unsigned-byte-p 64 (car (fn-rov-subject subject view)))
                (unsigned-byte-p 64 (cdr (fn-rov-subject subject view)))))
  :hints (("Goal" :use ((:instance fn-rov-count-and-charge-fit-ledger-capacity))
           :in-theory (e/d (unsigned-byte-p integer-range-p fn-rov-subject fn-rov-count)
                           (fn-rov-count-and-charge-fit-ledger-capacity
                            fn-rov-subject-is-oracle fn-vdc-get fn-rov-correspondp)))))
