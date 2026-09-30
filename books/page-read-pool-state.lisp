; The ONE shared pool type and exact scalar ledger projection/update seam.
; No reset or identity restart; installation/lifetime lives in host adapter.
(in-package "ACL2")
(include-book "page-read-ledger")

(defstobj fn-page-read-pool
  (fn-prp-data :initially nil)
  (fn-prp-mode :initially :uninitialized)
  (fn-prp-incoming-slot :initially nil)
  :inline t)

(defun fn-owner-page-read-ledger (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-prl-nth 0 (fn-prp-data fn-page-read-pool)))

(defun fn-owner-page-read-keep-ledger (ledger fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let ((data (fn-prp-data fn-page-read-pool)))
    (update-fn-prp-data (list ledger (fn-prl-nth 1 data) (fn-prl-nth 2 data)
                              (fn-prl-nth 3 data) (fn-prl-nth 4 data)) fn-page-read-pool)))
