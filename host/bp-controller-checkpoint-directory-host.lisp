; Internal SAME-pool commit adapter. No public supplied-demand allocator.
(in-package "ACL2")
(include-book "../books/bp-controller-checkpoint-directory-fuel")
(include-book "../books/page-read-pool-state")
(defun fn-owner-bp-checkpoint-reserve (controller demand fuel fn-bp-controller-registry fn-page-read-pool)
  (declare (xargs :stobjs (fn-bp-controller-registry fn-page-read-pool)
                  :guard (natp fuel)))
  (cond ((not (eq (fn-prp-mode fn-page-read-pool) :served))
         (mv :checkpoint-pool-unavailable nil fuel fn-bp-controller-registry fn-page-read-pool))
        ((< fuel (* 2 (+ 1 (fn-bpcr-depth fn-bp-controller-registry))))
         (mv :yield nil fuel fn-bp-controller-registry fn-page-read-pool))
        (t
         (mv-let (word token ledger left fn-bp-controller-registry)
           (fn-bpcc-directory-job controller nil :prepare demand
             (fn-owner-page-read-ledger fn-page-read-pool) fuel fn-bp-controller-registry)
           (if (not (eq word :checkpoint-prepared))
               (mv word nil left fn-bp-controller-registry fn-page-read-pool)
             (let ((fn-page-read-pool
                    (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
               (mv-let (word answer ignored-ledger left fn-bp-controller-registry)
                 (fn-bpcc-directory-job controller token :publish nil ledger left fn-bp-controller-registry)
                 (declare (ignore ignored-ledger))
                 (mv word answer left fn-bp-controller-registry fn-page-read-pool))))))))
(verify-guards fn-owner-bp-checkpoint-reserve
  :hints (("Goal" :in-theory (disable fn-bpcc-directory-job))))
; Cleanup derives any retained token from CURRENT, including an escaped issue.
; The shared pool is unchanged: cancellation is not settlement.
(defun fn-owner-bp-checkpoint-fence-current (controller fuel fn-bp-controller-registry fn-page-read-pool)
  (declare (xargs :stobjs (fn-bp-controller-registry fn-page-read-pool)
                  :guard (natp fuel)))
  (mv-let (word ignored ignored-ledger left fn-bp-controller-registry)
    (fn-bpcc-directory-job controller nil :fence-current nil
      (fn-owner-page-read-ledger fn-page-read-pool) fuel fn-bp-controller-registry)
    (declare (ignore ignored ignored-ledger))
    (mv word left fn-bp-controller-registry fn-page-read-pool)))
(verify-guards fn-owner-bp-checkpoint-fence-current)
