; Proof-side issuance history through operation completion and recycling.
(in-package "ACL2")
(include-book "ops-issued-count")

; The first column is read as CAR; existing setter frames are stated for NTH.
; Use the bridge explicitly, so no CAR/NTH rewrite loop enters the theory.
(local (defthm fn2-issued-car-as-nth
 (equal (car x) (nth 0 x)) :rule-classes nil))

(local (defthm fn2-issued-car-of-update-nth
 (equal (car (update-nth k v x)) (if (zp k) v (car x)))))

; History reads only the generation and phase columns. One footprint rule
; covers every scalar/payload writer instead of a reader-by-writer matrix.
(defthm fn2-ops-issued-count-scalar-frame
 (implies (and (not (equal (nfix k) *fn2-ops-gen$ai*))
               (not (equal (nfix k) *fn2-ops-phase$ai*)))
  (equal (fn2-ops-issued-count n (update-nth k v fn2-ops))
         (fn2-ops-issued-count n fn2-ops)))
 :hints (("Goal" :induct (fn2-ops-issued-count n fn2-ops)
   :in-theory (e/d (fn2-ops-issued-count fn2-ops-gen fn2-ops-phase)
                   (fn2-op-issued-weight update-nth)))))
(defthm fn2-ops-issued-count-array-frame
 (implies (and (not (equal (nfix k) *fn2-ops-gen$ai*))
               (not (equal (nfix k) *fn2-ops-phase$ai*)))
  (equal (fn2-ops-issued-count n (update-nth-array k i v fn2-ops))
         (fn2-ops-issued-count n fn2-ops)))
 :hints (("Goal" :in-theory (e/d (update-nth-array) (fn2-ops-issued-count update-nth)))))

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

; Moving an already issued incarnation between active phases cannot issue
; it again. The CAR bridge stays local to this footprint proof.
(encapsulate ()
(local (defthm fn2-issued-car-as-nth-rewrite (equal (car x) (nth 0 x))))
(defthm fn2-ops-set-phase-issued-count
 (implies (and (natp slot)
               (not (member-equal phase (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))
               (not (member-equal (fn2-ops-phase slot fn2-ops) (list *fn2-op-phase-free* *fn2-op-phase-reserved*))))
  (equal (fn2-ops-issued-count n (fn2-ops-set-phase slot phase fn2-ops))
         (fn2-ops-issued-count n fn2-ops)))
 :hints (("Goal" :induct (fn2-ops-issued-count n fn2-ops)
   :in-theory (e/d (fn2-ops-issued-count fn2-op-issued-weight fn2-ops-gen fn2-ops-phase)
    (fn2-ops-set-phase nth)))))
)

; ACK preflight establishes issued history even for duplicate ring entries.
; Unlike the queued predicate, this invariant survives earlier ACK steps.
(defun fn2-outbox-issued-prefixp (n index fn2-ops)
 (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
 (if (zp n) t
  (and (not (member-equal (fn2-ops-phase (fn2-ops-out-sloti index fn2-ops) fn2-ops)
                          (list *fn2-op-phase-free* *fn2-op-phase-reserved*)))
       (fn2-outbox-issued-prefixp (- n 1)
        (fn2-ring-next index (fn2-ops-out-slot-length fn2-ops)) fn2-ops))))
(defthm fn2-outbox-prefixp-implies-issued
 (implies (fn2-outbox-prefixp n index fn2-ops)
          (fn2-outbox-issued-prefixp n index fn2-ops))
 :hints (("Goal" :induct (fn2-outbox-prefixp n index fn2-ops)
 :in-theory (e/d (fn2-outbox-prefixp fn2-outbox-issued-prefixp fn2-op-phase-code fn2-op-handle-code)
                 (fn2-ops-phase fn2-ops-gen fn2-ops-out-sloti fn2-ops-out-geni fn2-ops-out-slot-length fn2-ops-out-gen-length)))))
(defthm fn2-outbox-issued-prefixp-set-phase
 (implies (and (natp slot) (fn2-outbox-issued-prefixp n index fn2-ops)
               (not (member-equal phase (list *fn2-op-phase-free* *fn2-op-phase-reserved*))))
          (fn2-outbox-issued-prefixp n index (fn2-ops-set-phase slot phase fn2-ops)))
 :hints (("Goal" :induct (fn2-outbox-issued-prefixp n index fn2-ops)
 :in-theory (e/d (fn2-outbox-issued-prefixp fn2-ops-phase fn2-ops-out-sloti fn2-ops-out-slot-length)
                  (fn2-ops-set-phase nth)))))
(defthm fn2-outbox-issued-prefixp-update-head
 (equal (fn2-outbox-issued-prefixp n index (update-fn2-ops-out-head value fn2-ops))
        (fn2-outbox-issued-prefixp n index fn2-ops))
 :hints (("Goal" :induct (fn2-outbox-issued-prefixp n index fn2-ops)
 :in-theory (enable fn2-outbox-issued-prefixp))))
(defthm fn2-outbox-issued-prefixp-update-queued
 (equal (fn2-outbox-issued-prefixp n index (update-fn2-ops-queued value fn2-ops))
        (fn2-outbox-issued-prefixp n index fn2-ops))
 :hints (("Goal" :induct (fn2-outbox-issued-prefixp n index fn2-ops)
 :in-theory (enable fn2-outbox-issued-prefixp))))
(defthm fn2-issued-count-update-out-head
 (equal (fn2-ops-issued-count n (update-fn2-ops-out-head value fn2-ops))
        (fn2-ops-issued-count n fn2-ops))
 :hints (("Goal" :in-theory (e/d (update-fn2-ops-out-head) (update-nth fn2-ops-issued-count)))))
(defthm fn2-issued-count-update-queued
 (equal (fn2-ops-issued-count n (update-fn2-ops-queued value fn2-ops))
        (fn2-ops-issued-count n fn2-ops))
 :hints (("Goal" :in-theory (e/d (update-fn2-ops-queued) (update-nth fn2-ops-issued-count)))))
(defthm fn2-outbox-issued-head-after-submit
 (equal (fn2-ops-out-head (update-fn2-ops-queued queued (update-fn2-ops-out-head head fn2-ops))) head)
 :hints (("Goal" :in-theory (enable fn2-ops-out-head update-fn2-ops-queued update-fn2-ops-out-head))))
(defthm fn2-outbox-submit-prefix-issued-count
 (implies (fn2-outbox-issued-prefixp n (fn2-ops-out-head fn2-ops) fn2-ops)
  (equal (fn2-ops-issued-count rows (fn2-outbox-submit-prefix n fn2-ops))
         (fn2-ops-issued-count rows fn2-ops)))
 :hints (("Goal" :induct (fn2-outbox-submit-prefix n fn2-ops)
 :in-theory (e/d (fn2-outbox-submit-prefix fn2-outbox-issued-prefixp fn2-op-ack-phase fn2-action-completionp
                  fn2-op-slotp)
  (fn2-outbox-prefixp-implies-issued fn2-ops-kind fn2-ops-issued-count fn2-opsp fn2-ops-wfp fn2-ops-set-phase fn2-ops-phase fn2-ops-rows
   fn2-ops-out-head fn2-ops-queued fn2-ops-out-sloti fn2-ops-out-slot-length update-nth update-fn2-ops-out-head update-fn2-ops-queued fn2-ring-next)))))
(defthm fn2-outbox-ack-issued-count
 (equal (fn2-ops-issued-count rows (mv-nth 1 (fn2-outbox-ack n fn2-ops)))
        (fn2-ops-issued-count rows fn2-ops))
 :hints (("Goal" :in-theory (e/d (fn2-outbox-ack)
  (fn2-ops-issued-count fn2-outbox-prefixp fn2-outbox-issued-prefixp fn2-outbox-submit-prefix
   fn2-ops-queued fn2-ops-out-slot-length fn2-ops-out-head)))))
(make-event
 (value `(defthm fn2-outbox-ack-issued-total
  ,(fn2-run-issued-claim 0 'fn2-ops '(mv-nth 1 (fn2-outbox-ack n fn2-ops))))))

(in-theory (disable fn2-outbox-issued-prefixp))
