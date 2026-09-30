; Actual readonly-current INITIAL history-reader entry. Native code receives
; the exact cursor/binding/token before creating or retaining private state.
(in-package "ACL2")
(include-book "snapshot-initial-host")
(include-book "../books/snapshot-initial-reader")
(defun fn-owner-recovery-initial-reader-begin
 (source maintenance page-source root-ticket fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :mode :program))
 (if (not (fn-owner-recovery-initial-livep source maintenance fn-page-read-pool state))
     (mv nil '(:retained :initial-reader-current) fn-page-read-pool state)
   (mv-let (word token cursor binding next)
    (fn-snir-begin (fn-owner-page-read-ledger fn-page-read-pool)
                   source maintenance page-source root-ticket)
    (if (not (eq word :reader))
        (mv nil word fn-page-read-pool state)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger next fn-page-read-pool)))
       (mv nil (list :reader token cursor binding root-ticket)
           fn-page-read-pool state))))))
; No release entry accepts a page-closed/status/host-joined flag. The actual
; private reader/digest/root aliases and constructor turn need their real
; runtime terminal observation; this role remains held until that exists.
