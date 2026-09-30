; One process-local saved authority proposal. Reset/unstage must clear it;
; stale process epochs and stage lineage are checked by the core consumer.
(in-package "ACL2")
(include-book "consumer-config-authority")
(include-book "state-globals")

(defun fn-owner-authority-proposal (state)
  (declare (xargs :stobjs state :guard t))
  (and (boundp-global 'fn-owner-authority-proposal state)
       (f-get-global 'fn-owner-authority-proposal state)))

(defun fn-owner-authority-proposal-clear (state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-authority-proposal nil state))

(defun fn-owner-authority-proposal-capture (epoch cp record approved state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-owner-authority-proposal
                (fn-cca-proposal epoch cp record approved) state))

; Clear on every consumption, including mismatch. A repeated completion must
; recover; it cannot apply another authority bump or reuse a stale proposal.
(defun fn-owner-authority-proposal-consume (epoch cp record state)
  (declare (xargs :stobjs state :guard t))
  (let* ((one (fn-cca-consume (fn-owner-authority-proposal state)
                             epoch cp record))
         (state (fn-owner-authority-proposal-clear state)))
    (mv one state)))

(defthm fn-owner-authority-proposal-consume-clears
  (null (fn-owner-authority-proposal
          (mv-nth 1 (fn-owner-authority-proposal-consume epoch cp record state))))
  :hints (("Goal" :in-theory
           (enable fn-owner-authority-proposal-consume
                   fn-owner-authority-proposal-clear fn-owner-authority-proposal))))
