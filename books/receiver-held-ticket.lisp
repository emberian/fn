; Internal adoption getter. This never lends an idle/live/another fill ticket.
; The actual current committed request must still match the retained custody
; recipient/source in the pre-adoption producer.
(in-package "ACL2")
(include-book "receiver-turn-controller")

(defun fn-owner-rx-turn-custody-ticket
 (fn-rx-provider fn-receiver-turn fn-page-read-pool)
 (declare (xargs :stobjs (fn-rx-provider fn-receiver-turn fn-page-read-pool)))
 (let ((ticket (fn-rxt-ticket fn-receiver-turn)))
  (if (and (eq (fn-rxt-phase fn-receiver-turn) :transferred)
           (null (fn-rxp-capacity fn-rx-provider))
           (fn-rxt-owned-claim-p ticket fn-rx-provider fn-receiver-turn fn-page-read-pool))
      ticket nil)))
