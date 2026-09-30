; Guard qualification for proof-side static premises. No served validator call.
(in-package "ACL2")
(include-book "bp-controller-registry-carry")
(verify-guards fn-bpn-machine-invariantp
  :hints (("Goal"
           :use ((:instance fn-bpn-state-field-types-for-guard (st st)))
           :in-theory (e/d (fn-bpn-machine-u64p)
                           (fn-bpn-machine-statep fn-bpn-machine-recordp)))))
(verify-guards fn-bpnp-step-guard-premisesp)
(verify-guards fn-bpc-row-carryp)
(verify-guards fn-bpc-segment-carry-loop)
(verify-guards fn-bpc-node-carryp)
(verify-guards fn-bpc-registry-carryp)
