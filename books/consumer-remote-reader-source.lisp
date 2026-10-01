; Exact fixed-field coordinate for the high consumer reader. This is semantic
; source data, NOT an issuer, native grant, or complete publisher invariant.
(in-package "ACL2")
(include-book "consumer-remote-dispatch")
(include-book "consumer-remote-semantic-state")

; Also bind operation and consumer ID: account coordinates alone cannot bind
; two consumers owned by the same account, or a changed operation at a wake.
(defun fn-crr-source-key (token source ingress cp generation count g record-ceiling)
 (declare (xargs :guard t))
 (list :remote-reader-source token (fn-hhc-at 1 source) (fn-hhc-at 2 source)
       (fn-hhc-at 3 source) (fn-hhc-at 8 source)
       (fn-hhc-at 7 source) (fn-cp-nth 2 (fn-cp-nth 1 ingress)) (fn-cp-nth 2 ingress)
       (fn-cp-nth 1 (fn-cp-nth 1 ingress)) (fn-cp-nth 4 (fn-cp-nth 1 ingress)) g record-ceiling
       (fn-crx-coordinate ingress cp generation count)))

; The authoritative producer is the actual atomic canonical10/CP7/metadata5/
; root collector, not the account candidate-input/job source. That reader
; association is not installed yet. A raw tuple or sidecar shape cannot mint
; it. Replace this unavailable readout only with that real maintained source.
(defun fn-owner-remote-reader-activation-status (state)
 (declare (xargs :stobjs state :guard t))
 (mv '(:unavailable :consumer-current-publication) state))

(in-theory (disable fn-crr-source-key fn-owner-remote-reader-activation-status))
