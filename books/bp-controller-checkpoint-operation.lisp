; Bounded projections of the actual issued checkpoint operation. This is a
; core composition predicate, not a registration/job resource grant.
(in-package "ACL2")
(include-book "bp-node-foundation")
(include-book "bp-handoff-recovery-shape")
(set-verify-guards-eagerness 2)

(defun fn-bpco-issued-checkpoint-p (issued)
 (declare (xargs :guard t))
 (and (fn-bphs-exact-listp issued 6)
      (equal (fn-bpn-nth 0 issued) :bpnf-operation)
      (fn-frame-natp (fn-bpn-nth 1 issued))
      (equal (fn-bpn-nth 2 issued) 0)
      (equal (fn-bpn-nth 3 issued) :checkpoint)
      (fn-frame-natp (fn-bpn-nth 4 issued)) (< 0 (fn-bpn-nth 4 issued))
      (equal (fn-bpn-nth 5 issued) :pending)))
(defun fn-bpco-checkpoint-operation-p (current)
 (declare (xargs :guard t))
 (and (fn-bpco-issued-checkpoint-p (fn-bpnf-issued current))
      (equal (fn-bpn-nth 1 (fn-bpnf-issued current)) (fn-bpnf-epoch current))))
(defun fn-bpco-checkpoint-generation (current)
 (declare (xargs :guard t))
 (fn-bpn-nth 4 (fn-bpnf-issued current)))
(defun fn-bpco-checkpoint-epoch (current)
 (declare (xargs :guard t))
 (fn-bpnf-epoch current))
(defun fn-bpco-checkpoint-operation-id (current)
 (declare (xargs :guard t))
 (fn-bpn-nth 2 (fn-bpnf-issued current)))

; Definition-level constructor/field facts are not keystones or authority.
(defthm fn-bpco-issued-checkpoint-constructor-by-definition
 (implies (and (fn-frame-natp epoch) (fn-frame-natp generation) (< 0 generation))
  (fn-bpco-issued-checkpoint-p
   (fn-bpnf-operation epoch 0 :checkpoint generation :pending)))
 :hints (("Goal" :in-theory (enable fn-bpco-issued-checkpoint-p fn-bpnf-operation))))
(defthm fn-bpco-checkpoint-projections-by-definition
 (implies (fn-bpco-checkpoint-operation-p current)
  (and (fn-frame-natp (fn-bpco-checkpoint-generation current))
       (< 0 (fn-bpco-checkpoint-generation current))
       (fn-frame-natp (fn-bpco-checkpoint-epoch current))
       (equal (fn-bpco-checkpoint-operation-id current) 0)))
 :hints (("Goal" :in-theory (enable fn-bpco-checkpoint-operation-p
  fn-bpco-issued-checkpoint-p fn-bpco-checkpoint-generation
  fn-bpco-checkpoint-epoch fn-bpco-checkpoint-operation-id))))
