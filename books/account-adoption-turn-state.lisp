; Actual sole owner account-turn custody. This is not canonical history APR.
; Internal writers are invoked only by the funded typed account producer and
; its fenced collector; no native setter or supplied row export is provided.
(in-package "ACL2")
(include-book "account-adoption-turn")

(defun fn-owner-account-turn-current (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-account-turn-current state)
      (f-get-global 'fn-owner-account-turn-current state)))

(defun fn-owner-account-turn-keep (current state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-account-turn-current current state))

; Readout alone is not a grant. The host-called allocating entry additionally
; consumes the actual installed operation issuer's SAME reserved BODY receipt.
(defun fn-owner-account-turn-receipt (state)
 (declare (xargs :stobjs state :guard t))
 (let* ((current (fn-owner-account-turn-current state))
        (token (fn-cp-nth 1 current)))
  (if (and (fn-act-livep token current)
           (eq (fn-cp-nth 2 current) :reserved))
      (mv :account-turn-reserved token)
    (mv :account-turn-unavailable nil))))

; Any raw escape with :promoting or a live unknown stage is recovery, not a
; second issue, reapplication of pool counters, refund or implicit job clear.
(defun fn-owner-account-turn-fence (state)
 (declare (xargs :stobjs state :guard t))
 (let* ((current (fn-owner-account-turn-current state))
        (token (fn-cp-nth 1 current)))
  (mv-let (word next) (fn-act-uncertain token current)
   (let ((state (fn-owner-account-turn-keep next state)))
    (mv word state)))))

(in-theory (disable fn-owner-account-turn-current fn-owner-account-turn-keep
                    fn-owner-account-turn-receipt fn-owner-account-turn-fence))
