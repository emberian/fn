; Sole retained account completion output. Only the actual durable completion
; hook writes it; no native tuple setter or :durable/status atom is authority.
(in-package "ACL2")
(include-book "state-globals")

(defun fn-owner-account-durable-outcome (state)
 (declare (xargs :stobjs state :guard t))
 (and (boundp-global 'fn-owner-account-durable-outcome state)
      (f-get-global 'fn-owner-account-durable-outcome state)))

; The actual last-alias/typed-turn collector owns clearing this slot. A read
; or successful durable publication does not establish that lifetime boundary.
(in-theory (disable fn-owner-account-durable-outcome))
