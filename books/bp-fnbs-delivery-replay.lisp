; Kind 7 (a committed application result) has authority only for the
; earlier exact kind-5 row it identifies.  The ordered kind-5/7 fold that
; lived here was retired (Q3a, PKT-298): the served recovery fold is
; `fn-bpnf-family-replay-rows' (books/bp-fnbs-family-replay.lisp).
(in-package "ACL2")
(include-book "bp-fnbs-delivery-codec")
(include-book "bp-fnbs-replay")
(include-book "bp-app-handoff")
(set-verify-guards-eagerness 0)

(defthm fn-bpah-kind-seven-without-kind-five-faults
  (implies (fn-bpah-delivery-recordp record)
           (equal (fn-bpah-apply-delivery record nil)
                  (mv nil nil nil))))
