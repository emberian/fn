; The ONE shared pool type and exact scalar ledger projection/update seam.
; No reset or identity restart; installation/lifetime lives in host adapter.
(in-package "ACL2")
(include-book "page-read-ledger")

(defstobj fn-page-read-pool
  (fn-prp-data :initially nil)
  (fn-prp-mode :initially :uninitialized)
  (fn-prp-incoming-slot :initially nil)
  ;; One process-wide allocation epoch in the SAME existing pool. Scalars
  ;; are checked against the installed profile/runtime immediate domain by
  ;; the epoch core; these type guards are not installation authority.
  (fn-prp-alloc-installation :initially nil)
  (fn-prp-alloc-mode :initially :uninstalled)
  (fn-prp-alloc-epoch :type (integer 0 *) :initially 0)
  (fn-prp-alloc-occupied :type (integer 0 *) :initially 0)
  (fn-prp-alloc-allocated :type (integer 0 *) :initially 0)
  (fn-prp-alloc-active-turns :type (integer 0 *) :initially 0)
  (fn-prp-alloc-gc-nonce :initially nil)
  :inline t)

(defun fn-owner-page-read-ledger (fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-prl-nth 0 (fn-prp-data fn-page-read-pool)))

(defun fn-prp-metadata-tail (n data)
  (declare (xargs :guard (natp n)))
  (if (zp n) data
    (fn-prp-metadata-tail (1- n) (if (consp data) (cdr data) nil))))

(defun fn-owner-page-read-keep-ledger (ledger fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (let ((data (fn-prp-data fn-page-read-pool)))
    (update-fn-prp-data
      (append (list ledger (fn-prl-nth 1 data) (fn-prl-nth 2 data)
                    (fn-prl-nth 3 data) (fn-prl-nth 4 data))
              (fn-prp-metadata-tail 5 data)) fn-page-read-pool)))
