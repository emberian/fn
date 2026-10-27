; Persistent physical workers carry one exact resource binding until the
; worker relinquishes its result and the owner settles that I/O incarnation.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/page-read-executor")
(include-book "../books/page-read-direct") ; the unfunded cold line (host/native/extent.lisp)

(defun fn-owner-page-executor-acquire (worker token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word worker1 ledger)
    (fn-pxe-acquire (fn-owner-page-read-ledger fn-page-read-pool) worker token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool))))

(definterface fn-owner-page-executor-acquire :class :common-lisp-compliant
  :keystones ((fn-pxe-acquired-token-cannot-own-a-second-worker :via fn-pxe-acquire)))

(defun fn-owner-page-executor-commit (worker io token cachedp fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word worker1 ledger)
    (fn-pxe-commit worker io token (fn-owner-page-read-ledger fn-page-read-pool) cachedp)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word worker1 fn-page-read-pool))))

(definterface fn-owner-page-executor-commit :class :common-lisp-compliant
  :keystones ((fn-pxe-commit-requires-returned-settled-exact-job :via fn-pxe-commit)))
