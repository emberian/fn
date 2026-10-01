; Staged SAME-pool RX installation. The actual factory must reserve before
; creating one fresh provider, and fence unknown allocation outcomes.
; Supplied demand is internal algebra, not a qualified constructor census.
(in-package "ACL2")
(include-book "../books/receiver-provider")
(include-book "../books/page-read-pool-state")
(defun fn-owner-rx-capacity-reserve (instance demand fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool :guard t))
  (if (not (eq (fn-prp-mode fn-page-read-pool) :served))
      (mv :receiver-pool-unavailable nil fn-page-read-pool)
    (mv-let (word token ledger)
      (fn-bca-admit :rx-capacity (list instance 4096) demand
                    (fn-owner-page-read-ledger fn-page-read-pool))
      (if (eq word :admitted)
          (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
            (mv word token fn-page-read-pool))
        (mv word token fn-page-read-pool)))))

; Internal child operation: the actual registered provider supplies BOTH
; children. There is no public carry setter or separately supplied buffer.
(defun fn-rx-capacity-install-children
  (token fn-octets-rx fn-rx-carry fn-page-read-pool)
  (declare (xargs :stobjs (fn-octets-rx fn-rx-carry fn-page-read-pool) :guard t))
  (if (not (and (eq (fn-prl-nth 0 token) :rx-capacity)
                (fn-rxc-uninitializedp fn-rx-carry)))
      (mv :stale-capacity fn-octets-rx fn-rx-carry fn-page-read-pool)
    (mv-let (word ledger1)
      (fn-bca-promote-installed token (fn-owner-page-read-ledger fn-page-read-pool))
      (if (not (eq word :installed))
          (mv word fn-octets-rx fn-rx-carry fn-page-read-pool)
        ; CURRENT reserved row is checked before allocator work. After the
        ; reserve returns, commit installed U BEFORE publishing ready carry.
        ; An escape then leaves unavailable carry and retained installed debt.
        (let* ((fn-octets-rx (fn-octets-rx-reserve 4096 fn-octets-rx))
               (fn-page-read-pool (fn-owner-page-read-keep-ledger ledger1 fn-page-read-pool))
               (fn-rx-carry (update-fn-rxc-token token fn-rx-carry))
               (fn-rx-carry (update-fn-rxc-instance (fn-prl-nth 2 token) fn-rx-carry))
               (fn-rx-carry (update-fn-rxc-capacity 4096 fn-rx-carry)))
          (mv :installed fn-octets-rx fn-rx-carry fn-page-read-pool))))))
(defun fn-owner-rx-capacity-install (token fn-rx-provider fn-page-read-pool)
  (declare (xargs :stobjs (fn-rx-provider fn-page-read-pool) :guard t))
  (if (not (eq (fn-prp-mode fn-page-read-pool) :served))
      (mv :receiver-pool-unavailable fn-rx-provider fn-page-read-pool)
    (stobj-let ((fn-octets-rx (fn-rxp-octets fn-rx-provider))
                (fn-rx-carry (fn-rxp-carry fn-rx-provider)))
      (word fn-octets-rx fn-rx-carry fn-page-read-pool)
      (fn-rx-capacity-install-children token fn-octets-rx fn-rx-carry fn-page-read-pool)
      (mv word fn-rx-provider fn-page-read-pool))))
(verify-guards fn-owner-rx-capacity-reserve)
(verify-guards fn-rx-capacity-install-children)
(verify-guards fn-owner-rx-capacity-install)
