; Shared custody return is reachable only after the actual terminal holder
; consumes a genuine physical callback completion. No public Boolean/receipt
; is accepted. Current source reports unavailable and retains all custody.
(in-package "ACL2")
(include-book "consumer-remote-terminal-state")
(include-book "history-source-capture")

(defun fn-owner-remote-scan-release (token fn-history-backing fn-page-read-pool state)
 (declare (xargs :stobjs (fn-history-backing fn-page-read-pool state) :guard t))
 (if (not (fn-hhc-matches (fn-owner-history-capture-slot state) token))
     (mv '(:refused :remote-history-token) fn-history-backing fn-page-read-pool state)
  (mv-let (terminal state) (fn-owner-remote-scan-terminal token state)
   (if (not (eq (fn-cp-nth 0 terminal) :remote-quiesced))
       (mv terminal fn-history-backing fn-page-read-pool state)
    (let ((state (fn-owner-history-quiesce-terminal token state)))
     (mv-let (released fn-history-backing fn-page-read-pool state)
      (fn-owner-history-release token fn-history-backing fn-page-read-pool state)
      (mv (if (eq released :released)
              (list :remote-returned (fn-cp-nth 2 terminal))
            (list :recovery-required :remote-history-return released))
          fn-history-backing fn-page-read-pool state)))))))

(in-theory (disable fn-owner-remote-scan-release))
