; The BP codec widths (PRF-134): each is the profile ceiling 2^24, and the
; old finite-machine values they replaced are below them.
(in-package "ACL2")
(include-book "../../books/bp-limits")

(assert-event (equal *fn-bpa-max-octets* 16777216))
(assert-event (equal *fn-bpa-max-article* (- 16777216 2106)))
(assert-event (equal *fn-bpb-max-data* 16777216))
(assert-event (equal *fn-bpb-max-input* 16777216))
(assert-event (equal *fn-bpnf-max-held-image* 16777216))
(assert-event (equal *fn-bpn-lifecycle-max-payload* (+ 16777216 3072)))
; Unchanged: the capped reference reassembler and the sender job image.
(assert-event (equal *fn-bpf-max-length* 65538))
(assert-event (equal *fn-bpn-machine-max-job-octets* 131072))
; The widths are above every value the old machine used.
(assert-event (< 65538 *fn-bpa-max-octets*))
(assert-event (< 1048576 *fn-bpb-max-input*))
(assert-event (< 131072 *fn-bpnf-max-held-image*))
(assert-event (<= (* *fn-bpf-max-fragments*
                     *fn-bpn-machine-max-job-octets*)
                  *fn-bpn-machine-max-octets*))
