; Unproved phase-1c obligations: NEVER load these to ground the witnesses.
(in-package "ACL2")
(include-book "contracts")

; The new operation actually returns a write plan and freezes the second
; appended batch. Partition is carried in pipe-okp; D does not move at append.
(defthm fn-lgk-append-behind-safe
  (implies (fn-lgk-pipe-okp p h)
    (let ((q (fn-lgk-behind-state p unit extent)))
      (and (fn-lgk-pipe-okp q h) (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
           (<= (fn-lgk-pipe-acked q) (fn-lgk-pipe-d q)))))
  :rule-classes nil)
(defthm fn-lgk-pipe-fence-safe
  (implies (fn-lgk-pipe-okp p h)
    (let ((q (fn-lgk-pipe-fence p unit)))
      (and (fn-lgk-pipe-okp q h) (<= (fn-lgk-pipe-d p) (fn-lgk-pipe-d q))
           (<= (fn-lgk-pipe-acked q) (fn-lgk-pipe-d q)))))
  :rule-classes nil)

; KEYSTONE, not the reveal readout: initial coupling and its inductive
; preservation across every proposed composite step, including append-behind,
; physical phase receipts, fence, ACK, view advance, reads, gate picks, failure.
; No invariant of the successor is in the hypothesis or a runtime guard.
(defthm fn-ocp-gc-linkedp-initially
  (implies (fn-ocp-gc-profilep unit extent bmax omax)
           (fn-ocp-gc-linkedp (fn-ocp-gc-init unit extent bmax omax)))
  :rule-classes nil)
(defthm fn-ocp-gc-linkedp-preserved
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-linkedp (fn-ocp-gc-host-step x event)))
  :rule-classes nil)

; COROLLARY over the actual emitted cuts of a STEP, not arbitrary cuts
; assumed durable in linkedp. Native renderer/effect refinement remains owed.
(defthm fn-ocp-gc-reveals-are-durable
  (implies (fn-ocp-gc-linkedp x)
           (fn-ocp-gc-reveals-okp (fn-ocp-gc-host-step x event)))
  :rule-classes nil)
(defthm fn-ocp-gc-failure-fences-both-batches
  (implies (fn-ocp-gc-failure-hyp x)
           (fn-ocp-gc-failure-okp x events))
  :rule-classes nil)
(defthm fn-olr-gc-membership-and-profile-bounds
  (implies (fn-olr-gc-membership-hyp h p record txid count octets bmax omax unit)
           (fn-olr-gc-membership-okp h p record txid count octets bmax omax unit))
  :rule-classes nil)

; Named equations to existing host-called primitives. These are definition /
; refinement lemmas, not keystones. The new dispatcher is NOT in the host yet.
(defthm fn-ocp-gc-event-action-by-definition
  (equal (fn-ocp-gc-event-action s e) (mv-nth 0 (fn-ocp-commit-event s e))))
(defthm fn-ocp-gc-event-state-by-definition
  (equal (fn-ocp-gc-event-state s e) (mv-nth 1 (fn-ocp-commit-event s e))))
(defthm fn-ocp-gc-pick-by-definition
  (equal (fn-ocp-gc-pick s w) (mv-nth 1 (fn-ocp-next s w))))
(defthm fn-lgk-pipe-ack-refines-host-call
  (equal (fn-lgc-of (fn-lgk-pipe-ks (fn-lgk-pipe-ack p n)))
         (fn-lgu-acknowledge (fn-lgc-of (fn-lgk-pipe-ks p)) (nfix n))))
(defthm fn-lgk-behind-promotion-keeps-write-plan
  (implies (fn-lgk-behind-admitsp p unit extent)
    (equal (fn-lgk-behind-effect p unit extent)
           (let ((ks (fn-lgk-pipe-ks (fn-lgk-pipe-fence p unit))))
             (list :write (fn-lgk-frontier ks) (fn-lgk-append-octets ks unit)))))
  :rule-classes nil)
