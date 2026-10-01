; Persistent physical workers carry one exact resource binding until the
; worker relinquishes its result and the owner settles that I/O incarnation.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/page-read-executor")

(include-book "../books/page-read-bindings-publish")

; Source availability is selected by the actual owner, before any legacy
; binding scan. These legacy scan bodies cannot receive a positive installed
; family until their bounded continuation replaces them.
(defun fn-owner-page-executor-acquire (worker token fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t :verify-guards nil))
 (mv-let (source-word source) (fn-owner-runtime-operation-source :page-read-acquire fn-page-read-pool state)
  (declare (ignore source))
  (if (not (eq source-word :runtime-operation-available))
   (mv source-word worker fn-page-read-pool)
   (let ((revision (fn-owner-page-read-binding-revision fn-page-read-pool)))
    (mv-let (word worker1 ledger) (fn-pxe-acquire (fn-owner-page-read-ledger fn-page-read-pool) worker token)
     (if (not (equal word :assigned)) (mv word worker1 fn-page-read-pool)
      (mv-let (publication fn-page-read-pool) (fn-owner-page-read-bindings-publish ledger revision fn-page-read-pool state)
       (if (eq publication :published) (mv word worker1 fn-page-read-pool)
        (mv publication worker fn-page-read-pool)))))))))

(defun fn-owner-page-executor-commit (worker io token cachedp fn-page-read-pool state)
 (declare (xargs :stobjs (fn-page-read-pool state) :guard t :verify-guards nil))
 (mv-let (source-word source) (fn-owner-runtime-operation-source :page-read-commit fn-page-read-pool state)
  (declare (ignore source))
  (if (not (eq source-word :runtime-operation-available))
   (mv source-word worker fn-page-read-pool)
   (let ((revision (fn-owner-page-read-binding-revision fn-page-read-pool)))
    (mv-let (word worker1 ledger) (fn-pxe-commit worker io token (fn-owner-page-read-ledger fn-page-read-pool) cachedp)
     (if (not (equal word :committed)) (mv word worker1 fn-page-read-pool)
      (mv-let (publication fn-page-read-pool) (fn-owner-page-read-bindings-publish ledger revision fn-page-read-pool state)
       (if (eq publication :published) (mv word worker1 fn-page-read-pool)
        (mv publication worker fn-page-read-pool)))))))))

; Current source producer is closed. This complete actual entry boundary
; guarantees refusal before the legacy scan and preserves worker and pool.
; It must be replaced with the qualified bounded subject before availability.
(defthm fn-owner-page-executor-acquire-source-unavailable-keeps-authority
 (equal (mv-list 3 (fn-owner-page-executor-acquire worker token fn-page-read-pool state))
        (list :runtime-operation-unavailable worker fn-page-read-pool))
 :hints (("Goal" :in-theory (enable fn-owner-page-executor-acquire fn-owner-runtime-operation-source))))
(defthm fn-owner-page-executor-commit-source-unavailable-keeps-authority
 (equal (mv-list 3 (fn-owner-page-executor-commit worker io token cachedp fn-page-read-pool state))
        (list :runtime-operation-unavailable worker fn-page-read-pool))
 :hints (("Goal" :in-theory (enable fn-owner-page-executor-commit fn-owner-runtime-operation-source))))
