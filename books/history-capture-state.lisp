; Actual retained custody lives in owner STATE; identities/charge use SAME PRL.
; No caller-created source tuple or metadata predicate grants installation.
(in-package "ACL2")
(include-book "history-capture-custody")
(include-book "owner-canonical-epoch")
(include-book "page-read-pool-state")
(defun fn-owner-history-capture-slot (state)
 (declare (xargs :stobjs state :guard t))
 (if (boundp-global 'fn-owner-history-capture state)
     (f-get-global 'fn-owner-history-capture state) nil))
(defun fn-owner-history-keep-capture (slot state)
 (declare (xargs :stobjs state :guard t))
 (f-put-global 'fn-owner-history-capture slot state))
(defun fn-owner-history-reset-status (state)
 (declare (xargs :stobjs state :guard t))
 (fn-hhc-reset-status (fn-owner-history-capture-slot state)))
(defun fn-owner-history-recheck (token state)
 (declare (xargs :stobjs state :guard t))
 (fn-hhc-recheck (fn-owner-history-capture-slot state) token
                 (fn-owner-canonical-epoch state)))
(defun fn-owner-history-read-plan (token ordinal state)
 (declare (xargs :stobjs state :guard t))
 (fn-hhc-read-plan (fn-owner-history-capture-slot state) token
                  (fn-owner-canonical-epoch state) ordinal))
 ; Cancellation retains the source and charge; it does not refund or unblock reset.
(defun fn-owner-history-cancel (token state)
 (declare (xargs :stobjs state :guard t))
 (fn-owner-history-keep-capture
  (fn-hhc-cancel (fn-owner-history-capture-slot state) token) state))
; INTERNAL terminal producer splice. Only the actual remote/checkpoint return
; producer, after joining every borrowed alias and native callback receipt,
; may invoke it. Clearing these STATE references is not that join proof.
(defun fn-owner-history-quiesce-terminal (token state)
 (declare (xargs :stobjs state :guard t))
 (if (not (fn-hhc-matches (fn-owner-history-capture-slot state) token)) state
  (let* ((state (f-put-global 'fn-owner-history-read nil state))
         (state (fn-owner-history-keep-capture
                 (fn-hhc-quiesce (fn-owner-history-capture-slot state) token) state)))
   state)))
; INTERNAL qualified constructor splice, not the host request boundary.
; Source must be obtained from fn-owner-history-source under owner->pool.
(defun fn-owner-history-capture-issued (source demand fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
 (mv-let (word descriptor ledger slot)
  (fn-hhc-admit (fn-owner-page-read-ledger fn-page-read-pool)
                (fn-owner-history-capture-slot state)
                (fn-owner-canonical-epoch state) source demand)
  (if (not (eq word :captured)) (mv word nil fn-page-read-pool state)
   (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool))
          (state (fn-owner-history-keep-capture slot state)))
    (mv word descriptor fn-page-read-pool state)))))
; INTERNAL only after actual terminal-return producer quiesces the owned row.
(defun fn-owner-history-release-issued (token fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t))
 (mv-let (word ledger slot)
  (fn-hhc-release (fn-owner-page-read-ledger fn-page-read-pool)
                  (fn-owner-history-capture-slot state) token)
  (if (not (eq word :released)) (mv word fn-page-read-pool state)
   (let* ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool))
          (state (fn-owner-history-keep-capture slot state)))
    (mv word fn-page-read-pool state)))))
