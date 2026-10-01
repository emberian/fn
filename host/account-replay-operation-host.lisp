; Same actual operation selector, with genuine replay custody before escape.
(in-package "ACL2")
(include-book "account-adoption-host")
(include-book "../books/account-replay-source")
(defun fn-owner-account-adoption-tick-with-replay
 (slot nonce fn-allocation-turn-slots fn-history-backing fn-page-read-pool state)
 (declare (xargs :stobjs (fn-allocation-turn-slots fn-history-backing fn-page-read-pool state)
                 :mode :program :guard (boundp-global 'fn-owner state)))
 (if (and (fn-owner-account-replay-source state)
          (not (fn-owner-account-replay-currentp fn-history-backing state)))
     (mv :unavailable :account-replay-source-stale
         fn-allocation-turn-slots fn-history-backing fn-page-read-pool state)
 (mv-let (word result fn-allocation-turn-slots fn-page-read-pool state)
  (fn-owner-account-adoption-tick slot nonce fn-allocation-turn-slots fn-page-read-pool state)
  (let* ((holder (fn-owner-account-adoption-operation state))
         (selection (fn-cp-nth 3 holder))
         (op (fn-cp-nth 4 (fn-cp-nth 1 selection))))
   (cond
    ((and (eq word :publish) (eq (fn-cp-nth 0 op) :authority-begin))
     (mv-let (held count fn-history-backing fn-page-read-pool state)
      (fn-owner-account-replay-begin fn-history-backing fn-page-read-pool state)
      (if (and (eq held :account-replay-retained)
               (equal count (fn-cp-nth 7 holder)))
          (mv word result fn-allocation-turn-slots fn-history-backing fn-page-read-pool state)
       ; Selection/receipt and any ambiguous capture remain held. Do not
       ; emit begin or rerun its selector while its custody is unavailable.
       (mv :unavailable :account-begin-replay-source
           fn-allocation-turn-slots fn-history-backing fn-page-read-pool state))))
    ((and (member-eq word '(:publish :configure))
          (not (fn-owner-account-replay-source state)))
     (mv :unavailable :account-replay-source-missing
         fn-allocation-turn-slots fn-history-backing fn-page-read-pool state))
    (t (mv word result fn-allocation-turn-slots fn-history-backing fn-page-read-pool state))))))
)
(definterface fn-owner-account-adoption-tick-with-replay :class :program)
