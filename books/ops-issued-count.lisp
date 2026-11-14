; Proof-side count of issued operation incarnations. Acknowledge does not
; erase an issue: submitted/done remain issued, and recycling trades the
; issued bit for the next generation. No served function scans this measure.
(in-package "ACL2")
(include-book "ops-heads")

(defun fn2-op-issued-weight (gen phase)
  (declare (xargs :guard t))
  (+ (nfix gen)
     (if (member-equal phase (list *fn2-op-phase-free* *fn2-op-phase-reserved*)) 0 1)))

(defun fn2-ops-issued-count (n fn2-ops)
  (declare (xargs :stobjs fn2-ops :verify-guards nil :measure (nfix n)))
  (if (zp n) 0
    (+ (fn2-op-issued-weight (fn2-ops-gen (- n 1) fn2-ops)
                            (fn2-ops-phase (- n 1) fn2-ops))
       (fn2-ops-issued-count (- n 1) fn2-ops))))

(defthm fn2-ops-issued-count-natural
  (natp (fn2-ops-issued-count n fn2-ops))
  :rule-classes :type-prescription)

(defthm fn2-op-enqueue-issued-weight
  (implies (natp i)
    (equal
      (fn2-op-issued-weight
        (fn2-ops-gen i (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops)))
        (fn2-ops-phase i (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops))))
      (+ (fn2-op-issued-weight (fn2-ops-gen i fn2-ops) (fn2-ops-phase i fn2-ops))
         (if (and (equal i slot) (eq (car (fn2-op-enqueue slot gen fn2-ops)) :ok)) 1 0))))
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn2-env-op-enqueue-heads (o fn2-ops) (s i))
          (:instance fn2-env-op-enqueue-ok-facts (o fn2-ops)))
    :in-theory (e/d (fn2-op-enqueue fn2-op-issued-weight fn2-op-phase-code fn2-op-handle-code fn2-op-slotp)
                    (fn2-ops-gen fn2-ops-phase fn2-ops-out-slot-length fn2-ops-out-gen-length
                     fn2-ops-out-tail fn2-ops-queued fn2-ops-reserved-credits fn2-ring-next unsigned-byte-p)))))

(defthm fn2-op-enqueue-issued-count
  (equal (fn2-ops-issued-count n (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops)))
         (+ (fn2-ops-issued-count n fn2-ops)
            (if (and (natp slot) (< slot (nfix n))
                     (eq (car (fn2-op-enqueue slot gen fn2-ops)) :ok)) 1 0)))
  :hints (("Goal" :induct (fn2-ops-issued-count n fn2-ops)
    :in-theory (e/d (fn2-ops-issued-count) (fn2-op-enqueue fn2-op-issued-weight fn2-ops-gen fn2-ops-phase)))))
