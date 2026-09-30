; W8/P12 reference trace over the actual reserve/refuse subjects.
(in-package "ACL2")
(include-book "../../books/refusal-headroom")
(include-book "../../books/store-observed")

(defconst *rfh-groups* '("fn.test"))
(defconst *rfh-wire*
 (fn-record-make 0 0 0 "<headroom@example>" '(65 66) *rfh-groups*
                 "headroom-pin" "headroom-content" "headroom-release" 2 841000000))
(defconst *rfh-row* (fn-held-plain *rfh-wire* 0))
(defconst *rfh-committed*
 (fn-sn-finish
  (fn-olr-sn-order
   (fn-sn-prepare (fn-olr-sn-reserve (fn-sn-initial *rfh-groups* 10)) *rfh-row*))))

; Productive positive: actual durable completion has a nonempty committed
; record, and twenty subsequent reserve/refuse cycles keep it and advance
; the frontier exactly twenty, without creating another accepted record.
(assert-event
 (and (fn-rfh-ready-p *rfh-committed*)
      (consp (fn-sf-records (fn-sn-files *rfh-committed*)))
      (consp (fn-sf-successes (fn-sn-files *rfh-committed*)))
      (equal (fn-sf-frontier (fn-sn-files *rfh-committed*)) 1)
      (equal (fn-sf-frontier (fn-sn-files (fn-rfh-run 20 *rfh-committed*))) 21)
      (equal (fn-sf-frontier (fn-sn-files (fn-rfh-run 20 *rfh-committed*)))
             (min *fn-sf-max-uint* (+ 20 (fn-sf-frontier (fn-sn-files *rfh-committed*)))))
      (equal (fn-sf-records (fn-sn-files (fn-rfh-run 20 *rfh-committed*)))
             (fn-sf-records (fn-sn-files *rfh-committed*)))
      (equal (fn-sn-groups (fn-rfh-run 20 *rfh-committed*)) (fn-sn-groups *rfh-committed*))
      (equal (fn-sn-capacity (fn-rfh-run 20 *rfh-committed*)) (fn-sn-capacity *rfh-committed*))))

; Replay a valid persisted allocator frontier after known-aborted gaps;
; this is an actual open/recovery path, not a manually altered live Store.
(defun rfh-test-finish-recovery (n s)
 (if (zp n) s
   (rfh-test-finish-recovery (1- n) (fn-sn-io s :recovery-barrier :ok))))
(defconst *rfh-near-open*
 (fn-sn-open-observed *rfh-groups* 10 (- *fn-sf-max-uint* 2) (list *rfh-row*)))
(defconst *rfh-near*
 (rfh-test-finish-recovery *fn-sf-recovery-barrier-count*
                         (fn-sn-open-state *rfh-near-open*)))
(assert-event
 (and (fn-sn-open-okp *rfh-near-open*)
      (fn-rfh-ready-p *rfh-near*)
      (consp (fn-sf-records (fn-sn-files *rfh-near*)))
      (equal (fn-sf-frontier (fn-sn-files (fn-rfh-run 9 *rfh-near*))) *fn-sf-max-uint*)
      (equal (fn-sf-frontier (fn-sn-files (fn-rfh-run 9 *rfh-near*)))
             (min *fn-sf-max-uint* (+ 9 (fn-sf-frontier (fn-sn-files *rfh-near*)))))
      (equal (fn-sf-records (fn-sn-files (fn-rfh-run 9 *rfh-near*)))
             (fn-sf-records (fn-sn-files *rfh-near*)))))

; The actual native allocation predicate has a successor after one burn,
; and refuses exactly after the two remaining identities have been used.
(assert-event
 (and (fn-rfh-ready-p *rfh-near*)
      (fn-bs-frontier-next (fn-sf-frontier (fn-sn-files (fn-rfh-run 1 *rfh-near*))))
      (not (<= (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files *rfh-near*))) 1))
      (not (fn-bs-frontier-next (fn-sf-frontier (fn-sn-files (fn-rfh-run 2 *rfh-near*)))))
      (<= (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files *rfh-near*))) 2)
      (not (fn-bs-frontier-next (fn-sf-frontier (fn-sn-files (fn-rfh-run 9 *rfh-near*)))))
      (<= (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files *rfh-near*))) 9)))

; Ready-state removal for both conditional keystones. This is the reachable
; RESERVED phase, outside the required idle request boundary. An already
; reserved identity cannot be consumed using a different identity.
(defconst *rfh-wrong-phase* (fn-olr-sn-reserve *rfh-near*))
(assert-event
 (and (fn-sn-statep *rfh-wrong-phase*)
      (equal (fn-sf-phase (fn-sn-files *rfh-wrong-phase*)) :reserved)
      (not (fn-rfh-ready-p *rfh-wrong-phase*))
      (not (equal (fn-sf-frontier (fn-sn-files (fn-rfh-run 2 *rfh-wrong-phase*)))
                  (min *fn-sf-max-uint*
                       (+ 2 (fn-sf-frontier (fn-sn-files *rfh-wrong-phase*))))))
      (fn-bs-frontier-next (fn-sf-frontier (fn-sn-files (fn-rfh-run 2 *rfh-wrong-phase*))))
      (<= (- *fn-sf-max-uint* (fn-sf-frontier (fn-sn-files *rfh-wrong-phase*))) 2)))

; Mutation: dropping a nonempty accepted record would violate the actual
; unconditional records/configuration frame, regardless of headroom.
(assert-event
 (and (consp (fn-sf-records (fn-sn-files *rfh-committed*)))
      (not (equal nil (fn-sf-records (fn-sn-files (fn-rfh-run 20 *rfh-committed*)))))))
