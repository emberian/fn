; Program-mode boundary for the experimental sender BP loop.
(in-package "ACL2")
(include-book "../books/bp-outbound")

; Acl2WorkflowReplay loads host/workflow-host.lisp first and installs the
; fn-workflow-state global.  This wrapper is also program-mode and is loaded by
; LD; it is deliberately not a certified logical book.

; Read-only projection for the callback that WorkflowJournal invokes only after
; its bridge.take_submit gate has consumed the one-shot external-action permit.
; Building bytes is not a second permission gate and does not mutate effects.
(defun fn-bpo-host-request-adu (work-id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((workflow (f-get-global 'fn-workflow-state state))
         (work (fn-bp-find-work work-id (fn-bp-state-works workflow)))
         (attempt (fn-bp-work-attempt work))
         (attempt-id (fn-bp-attempt-id attempt))
         (attempt-generation (fn-bp-attempt-generation attempt))
         (result
         (fn-bpo-request-adu
          workflow
          work-id attempt-id attempt-generation)))
    (value (if (fn-bpo-result-okp result)
               (fn-bpo-result-value result)
             nil))))

; Return a fixed local :receipt-intent record suitable for the existing
; workflow journal preflight/publication path.  This call is read-only: only
; that existing path may publish and apply the intent.
(defun fn-bpo-host-receipt-record
  (receipt-octets txid generation policy-authorizedp state)
  (declare (xargs :stobjs state :mode :program))
  (let ((result
         (fn-bpo-receipt-intent-record
          (f-get-global 'fn-workflow-state state)
          txid generation receipt-octets policy-authorizedp)))
    (value (if (fn-bpo-result-okp result)
               (fn-bpo-result-value result)
             nil))))

(defun fn-bpo-host-receipt-validp
  (receipt-octets txid generation policy-authorizedp state)
  (declare (xargs :stobjs state :mode :program))
  (value
   (if (fn-bpo-result-okp
        (fn-bpo-receipt-intent-record
         (f-get-global 'fn-workflow-state state)
         txid generation receipt-octets policy-authorizedp))
       t nil)))

; The Python bridge can obtain each validated text value as an octet list and
; construct its fixed FNWF dictionary without parsing a printed Lisp string or
; duplicating any receipt-field selection rule.
(defun fn-bpo-host-receipt-field-octets
  (index receipt-octets txid generation policy-authorizedp state)
  (declare (xargs :stobjs state :mode :program))
  (let ((result
         (fn-bpo-receipt-intent-record
          (f-get-global 'fn-workflow-state state)
          txid generation receipt-octets policy-authorizedp)))
    (if (or (not (natp index))
            (not (< index 9))
            (not (fn-bpo-result-okp result)))
        (value nil)
      (value
       (fn-record-string-octets
        (fn-bp-journal-nth
         (+ 3 index) (fn-bpo-result-value result)))))))
