; Proof-side issuance history through operation completion and recycling.
(in-package "ACL2")
(include-book "ops-issued-count")

; The first column is read as CAR; existing setter frames are stated for NTH.
; Use the bridge explicitly, so no CAR/NTH rewrite loop enters the theory.
(local (defthm fn2-issued-car-as-nth
 (equal (car x) (nth 0 x)) :rule-classes nil))

(defthm fn2-op-recycle-issued-weight
 (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
               (natp i) (< i (fn2-ops-rows fn2-ops)))
  (equal
   (fn2-op-issued-weight (fn2-ops-gen i (mv-nth 1 (fn2-op-recycle slot fn2-ops)))
                         (fn2-ops-phase i (mv-nth 1 (fn2-op-recycle slot fn2-ops))))
   (fn2-op-issued-weight (fn2-ops-gen i fn2-ops) (fn2-ops-phase i fn2-ops))))
 :hints (("Goal" :do-not-induct t
   :use ((:instance fn2-issued-car-as-nth (x (mv-nth 1 (fn2-op-recycle slot fn2-ops))))
         (:instance fn2-ops-gen-natp (i slot))
         (:instance fn2-ops-gen-natp (i i)))
   :in-theory (e/d (fn2-op-recycle fn2-ops-clear-row fn2-op-issued-weight fn2-ops-phase fn2-ops-gen fn2-op-slotp)
    (nth fn2-opsp fn2-ops-wfp fn2-ops-rows fn2-ops-gen-limit
     fn2-ops-free-count fn2-ops-retired-count fn2-ops-free-head)))))

(defthm fn2-op-recycle-issued-count
 (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops)
               (natp n) (<= n (fn2-ops-rows fn2-ops)))
  (equal (fn2-ops-issued-count n (mv-nth 1 (fn2-op-recycle slot fn2-ops)))
         (fn2-ops-issued-count n fn2-ops)))
 :hints (("Goal" :induct (fn2-ops-issued-count n fn2-ops)
   :in-theory (e/d (fn2-ops-issued-count)
    (fn2-op-recycle fn2-op-issued-weight fn2-ops-gen fn2-ops-phase fn2-ops-rows fn2-opsp fn2-ops-wfp)))))

(defthm fn2-op-recycle-issued-rows
 (equal (fn2-ops-rows (mv-nth 1 (fn2-op-recycle slot fn2-ops))) (fn2-ops-rows fn2-ops))
 :hints (("Goal" :in-theory (e/d (fn2-op-recycle fn2-ops-clear-row) (fn2-ops-rows)))))

(make-event
 (value `(defthm fn2-op-recycle-issued-total
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
   ,(fn2-run-issued-claim 0 'fn2-ops '(mv-nth 1 (fn2-op-recycle slot fn2-ops))))
  :hints (("Goal" :in-theory (disable fn2-op-recycle fn2-ops-issued-count fn2-ops-rows fn2-opsp fn2-ops-wfp))))))
(make-event
 (value `(defthm fn2-op-finish-issued-total
  (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
   ,(fn2-run-issued-claim 0 'fn2-ops '(mv-nth 1 (fn2-op-finish slot gen fn2-ops))))
  :hints (("Goal" :in-theory (e/d (fn2-op-finish)
    (fn2-op-recycle fn2-op-phase-code fn2-ops-issued-count fn2-ops-rows fn2-opsp fn2-ops-wfp)))))))
