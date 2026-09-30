; Same-pass sized SSR completion; replay authority and metadata availability
; remain separate. Original context is already retained by the actual issuer.
(in-package "ACL2")
(include-book "recovery-source-host")

(defun fn-owner-recovery-source-observe-sized
    (token original-context actual-fold fields status state)
  (declare (xargs :stobjs state :mode :program))
  ; Exactly one public observation, never a refreshed current-token retry.
  (mv-let (erp word state)
          (fn-owner-recovery-source-observe token original-context actual-fold state)
    (if (or erp (not (and (fn-omk-widthp word 2)
                          (eq (fn-omk-at 0 word) :counted))))
        (mv erp word state)
      (let* ((carried (and (eq status :carried) (fn-scs-fixed-carriesp 6 fields)))
             (state (f-put-global
                     'fn-owner-recovery-sized-pending
                     (list (fn-omk-at 1 word) (if carried fields nil)
                           (if carried :carried :unavailable)
                           (fn-owner-canonical-epoch state)
                           (fn-store-sco-recovery-source-generation-value state))
                     state)))
        (mv nil word state)))))

; Final installation consumes this exact pending record internally. The
; caller supplies its frozen token, never fields or a new current token.
(defun fn-owner-recovery-source-sized-readout (token state)
  (declare (xargs :stobjs state :mode :program))
  (let ((pending (fn-owner-recovery-global 'fn-owner-recovery-sized-pending state))
        (c (fn-owner-recovery-global 'fn-owner-recovery-source state))
        (epoch (fn-owner-canonical-epoch state))
        (generation (fn-store-sco-recovery-source-generation-value state)))
    (if (and (fn-rsa-metap (fn-store-sco-recovery-source-value state))
             (fn-rsa-currentp c token epoch generation)
             (fn-omk-widthp pending 5)
             (equal (fn-omk-at 0 pending) token)
             (equal (fn-omk-at 3 pending) epoch)
             (equal (fn-omk-at 4 pending) generation)
             (eq (fn-omk-at 2 pending) :carried)
             (fn-scs-fixed-carriesp 6 (fn-omk-at 1 pending)))
        (value (list :ready token (fn-omk-at 1 pending)))
      (value '(:unavailable :recovery-carries)))))
