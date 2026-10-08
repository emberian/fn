; Cache installation by the actual off-mutex rebuild and atomic owner swap.
(in-package "ACL2")
(include-book "history-served-cache")
(include-book "owner-recovery-retain")

(defthm fn-owner-orcp-rebuild-cache-bounds
  (let* ((rebuilt (fn-owner-orcp-rebuild e configs frontier max-conns))
         (count (fn-sf-records-count
                 (fn-sn-files (fn-own-store (fn-ocfg-owner (nth 1 rebuilt)))))))
    (implies (not (equal (nth 1 rebuilt) :fault))
             (and (fn-hist-cache-ready-p (nth 3 rebuilt) count t)
                  (fn-hist-cache-ready-p (nth 4 rebuilt) count t)
                  (fn-hist-cache-ready-p (nth 5 rebuilt) count nil))))
  :hints (("Goal" :in-theory (e/d (fn-owner-orcp-rebuild fn-hist-cache-ready-p
                                    fn-sbud-bytes-used)
                                   (fn-ock-recover-extended fn-sf-records)))))

(defthm fn-owner-orcp-swap-installs-cache-bounds
  (implies (and (fn-hist-cache-ready-p (nth 3 rebuilt) count t)
                (fn-hist-cache-ready-p (nth 4 rebuilt) count t)
                (fn-hist-cache-ready-p (nth 5 rebuilt) count nil))
           (fn-owner-history-cache-statep
            count (mv-nth 2 (fn-owner-orcp-swap rebuilt st))))
  :hints (("Goal" :in-theory (e/d (fn-owner-orcp-swap fn-owner-put-credits
                                    fn-owner-history-cache-statep)
                                   (fn-owner-authority-proposal-clear
                                    fn-owner-canonical-reset fn-owner-install-ocfg
                                    fn-owner-retain-carry-put fn-orcp-swapped-ocfg
                                    fn-owner-ocfg fn-owner-credits
                                    fn-hist-cache-ready-p)))))

(defthm fn-owner-recovery-establishes-cache-ready
  (let* ((rebuilt (fn-owner-orcp-rebuild e configs frontier max-conns))
         (count (fn-sf-records-count
                 (fn-sn-files (fn-own-store (fn-ocfg-owner (nth 1 rebuilt)))))))
    (implies (not (equal (nth 1 rebuilt) :fault))
             (fn-owner-history-cache-statep
              count (mv-nth 2 (fn-owner-orcp-swap rebuilt st)))))
  :hints (("Goal"
           :use (fn-owner-orcp-rebuild-cache-bounds
                 (:instance fn-owner-orcp-swap-installs-cache-bounds
                  (rebuilt (fn-owner-orcp-rebuild e configs frontier max-conns))
                  (count (fn-sf-records-count
                          (fn-sn-files
                           (fn-own-store
                            (fn-ocfg-owner
                             (nth 1 (fn-owner-orcp-rebuild e configs frontier max-conns)))))))))
           :in-theory (theory 'minimal-theory))))

; Finishing a committed record changes the owner and retention carry only.
; The history count is unchanged by this read-only stobj argument.
(defthm fn-owner-finish-synced-preserves-history-caches
  (equal (fn-owner-history-cache-statep
          count (mv-nth 2 (fn-owner-finish-synced hist st)))
         (fn-owner-history-cache-statep count st))
  :hints (("Goal" :in-theory
           (union-theories
            '(fn-owner-finish-synced fn-owner-install-ocfg
              fn-owner-retain-carry-put fn-owner-history-cache-statep-of-other-global-put
              mv-nth nth zp car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+)
              (:executable-counterpart unary--)
              (:executable-counterpart member-equal))
            (theory 'minimal-theory)))))
