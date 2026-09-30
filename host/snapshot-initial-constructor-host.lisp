; Actual constructor-entry custody. INITIAL already owns the operation;
; this transition grants no bytes and is not an allocator turn receipt.
(in-package "ACL2")
(include-book "snapshot-initial-host")
(defun fn-owner-recovery-initial-constructor-begin (source maintenance fn-page-read-pool state)
  (declare (xargs :stobjs (fn-page-read-pool state) :mode :program))
  (if (not (fn-owner-recovery-initial-livep source maintenance fn-page-read-pool state))
      (mv nil '(:retained :initial-constructor-source) fn-page-read-pool state)
    (let ((token (list :initial-constructor maintenance source)))
      (mv-let (word next)
        (fn-sni-role-claim (fn-owner-page-read-ledger fn-page-read-pool)
                          maintenance source :allocation-turn token)
        (if (not (eq word :claimed))
            (mv nil (list :retained word) fn-page-read-pool state)
          (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger next fn-page-read-pool)))
            (mv nil (list :entered token) fn-page-read-pool state)))))))
; There is deliberately no constructor-return wrapper accepting a host
; success/joined flag. The installed runtime epilogue must produce the real
; creator/caller/collector retirement observation before RoleReturn exists.
