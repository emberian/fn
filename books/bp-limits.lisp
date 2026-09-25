; fn: composition of the BP limits present in the executable v0 machine.
;
; The planned family stage slots, stage octets, and explicit header bound are
; not yet machine fields.  This book does not claim their composition.

(in-package "ACL2")

(include-book "bp-adu")
(include-book "bp-fragment")
(include-book "frame-octets")
(include-book "bp-node-machine-codec")

; Current finite machine: an ADU can fit the reassembler, the bundle image
; cap leaves 65534 octets beyond the maximum ADU, the lifecycle record cap
; leaves 3072 beyond an image, and 64 maximum images fit the aggregate byte
; budget.  Encoding overhead still requires an actual image-size check.
(defthm fn-bpn-limits-compose
  (and (equal *fn-bpa-max-octets* *fn-bpf-max-length*)
       (<= *fn-bpa-max-octets* *fn-bpf-max-length*)
       (<= (+ *fn-bpa-max-octets* 65534)
           *fn-bpn-machine-max-job-octets*)
       (<= *fn-bpn-machine-max-job-octets* *fn-frame-max-blob*)
       (<= (+ *fn-bpn-machine-max-job-octets* 3072)
           *fn-bpn-lifecycle-max-payload*)
       (<= (* *fn-bpf-max-fragments*
              *fn-bpn-machine-max-job-octets*)
           *fn-bpn-machine-max-octets*))
  :rule-classes nil)
