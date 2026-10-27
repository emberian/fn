; Exact window resource ownership; demand comes from the selected runtime
; allocator model. Native window activation awaits the authenticated stream.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/page-window-lease")

(defun fn-owner-page-window-admit (descriptor demand fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
      (mv :read-resources-unavailable nil fn-page-read-pool)
    (mv-let (word token ledger)
      (fn-prw-admit (fn-owner-page-read-ledger fn-page-read-pool) descriptor demand)
      (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
        (mv word token fn-page-read-pool)))))

(defun fn-owner-page-window-return (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger) (fn-prw-return (fn-owner-page-read-ledger fn-page-read-pool) token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word fn-page-read-pool))))

(defun fn-owner-page-window-release (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger) (fn-prw-release (fn-owner-page-read-ledger fn-page-read-pool) token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word fn-page-read-pool))))
