; The raised reassembly length composes with the current finite machine caps.
(in-package "ACL2")
(include-book "../../books/bp-limits")

(assert-event (equal *fn-bpa-max-octets* *fn-bpf-max-length*))
(assert-event (equal *fn-bpf-max-length* 65538))
(assert-event (equal *fn-bpn-machine-max-job-octets* 131072))
(assert-event (equal *fn-bpn-lifecycle-max-payload* 134144))
(assert-event (<= (* *fn-bpf-max-fragments*
                     *fn-bpn-machine-max-job-octets*)
                  *fn-bpn-machine-max-octets*))
