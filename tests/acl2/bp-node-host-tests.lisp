; The native BP command's exact mixed article/transport result policy.
(in-package "ACL2")
(include-book "../../host/bp-node-host")

; Reachable mixed evidence: one complete article was refused while the TCPCL
; session ended uncertain.  The process result is uncertain, not refused.
(assert-event
 (equal (fn-bpn-host-run-outcome 0 1 0 :uncertain) :uncertain))

; Each domain can independently raise the run result, while NIL is the native
; command's no-adverse-operational-evidence value.
(assert-event
 (equal (fn-bpn-host-run-outcome 0 0 1 :accepted) :uncertain))
(assert-event
 (equal (fn-bpn-host-run-outcome 0 1 0 :accepted) :refused))
(assert-event
 (equal (fn-bpn-host-run-outcome 1 0 0 nil) :accepted))

; Invalid host evidence fails closed.
(assert-event
 (equal (fn-bpn-host-run-outcome 0 -1 0 :accepted) :uncertain))
