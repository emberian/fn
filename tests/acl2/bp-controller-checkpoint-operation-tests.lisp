(in-package "ACL2")
(include-book "../../books/bp-controller-checkpoint-operation")

(defconst *bpco-current*
 (fn-bpnf-state nil nil nil nil nil
   (fn-bpnf-operation 3 0 :checkpoint 4 :pending) nil 3 1))
(assert-event (and (fn-bpco-checkpoint-operation-p *bpco-current*)
 (equal (fn-bpco-checkpoint-epoch *bpco-current*) 3)
 (equal (fn-bpco-checkpoint-generation *bpco-current*) 4)
 (equal (fn-bpco-checkpoint-operation-id *bpco-current*) 0)))
; Different kind/opaque KEY is never compared or inspected as a checkpoint.
(assert-event (not (fn-bpco-checkpoint-operation-p
 (fn-bpnf-state nil nil nil nil nil
  (fn-bpnf-operation 3 0 :deliver '(:opaque-large-key) :pending) nil 3 1))))
; An uncertainty is fenced, not a new writable checkpoint reservation.
(assert-event (not (fn-bpco-checkpoint-operation-p
 (fn-bpnf-state nil nil nil nil nil
  (fn-bpnf-operation 3 0 :checkpoint 4 :uncertain) nil 3 1))))
(assert-event (not (fn-bpco-checkpoint-operation-p
 (fn-bpnf-state nil nil nil nil nil
  (fn-bpnf-operation 2 0 :checkpoint 4 :pending) nil 3 1))))
(assert-event (not (fn-bpco-issued-checkpoint-p
 (fn-bpnf-operation 3 0 :checkpoint :unknown-generation :pending))))
