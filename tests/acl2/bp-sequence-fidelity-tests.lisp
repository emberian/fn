; Ground correspondence witnesses for the host recovery inputs.
(in-package "ACL2")
(include-book "../../books/bp-sequence-fidelity")

(assert-event
 (equal (fn-bpn-sf-host-recover :absent t) '(:ready 0)))
(assert-event
 (equal (fn-bpn-sf-host-recover :absent nil)
        '(:fault :sequence-frontier-missing)))
(assert-event
 (fn-bpn-sequence-recovery-readyp
  (fn-bpn-sf-host-recover '(:valid 0) nil)))
(assert-event
 (equal (fn-bpn-sequence-recovery-frontier
         (fn-bpn-sf-host-recover '(:valid 1) nil))
        1))
(assert-event
 (equal (fn-bpn-sf-host-recover :malformed nil)
        '(:fault :sequence-frontier)))
