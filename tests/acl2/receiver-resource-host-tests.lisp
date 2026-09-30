(in-package "ACL2")
(include-book "../../host/receiver-resource-host")
; Source algebra/child-binding fixture, not a selected-runtime budget claim.
(defun rxr-installed-observe (token fn-rx-provider fn-page-read-pool)
  (declare (xargs :stobjs (fn-rx-provider fn-page-read-pool) :guard t))
  (mv-let (word fn-rx-provider fn-page-read-pool)
    (fn-owner-rx-capacity-install token fn-rx-provider fn-page-read-pool)
    (let ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
          (saved-token (fn-rxp-token fn-rx-provider))
          (instance (fn-rxp-instance fn-rx-provider))
          (capacity (fn-rxp-capacity fn-rx-provider)))
      (mv-let (again fn-rx-provider fn-page-read-pool)
        (fn-owner-rx-capacity-install token fn-rx-provider fn-page-read-pool)
        (mv-let (range start end left fn-rx-provider)
          (fn-rxp-fill-range token 16 nil 16 fn-rx-provider)
          (mv (list word saved-token instance capacity
                    (fn-prl-baseline ledger) (fn-prl-nth 1 ledger)
                    (fn-prl-nth 2 ledger) again
                    (equal ledger (fn-owner-page-read-ledger fn-page-read-pool))
                    range start end left)
              fn-rx-provider fn-page-read-pool))))))
(defun rxr-observe ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-page-read-pool
    (mv-let (answer fn-page-read-pool)
      (let* ((fn-page-read-pool
                (fn-owner-page-read-keep-ledger
                  (fn-prl-build '(8192 0 0 0 8) '(0 0 0 0 0) 0 nil '(512 0 0 0 0))
                  fn-page-read-pool))
             (fn-page-read-pool (update-fn-prp-mode :served fn-page-read-pool)))
        (mv-let (word token fn-page-read-pool)
          (fn-owner-rx-capacity-reserve 0 '(4096 0 0 0 1) fn-page-read-pool)
          (if (not (eq word :admitted)) (mv (list word) fn-page-read-pool)
            ; Source order matches the actual factory requirement: issue,
            ; then one fresh constructor, then exact child installation.
            (with-local-stobj fn-rx-provider
              (mv-let (result fn-rx-provider fn-page-read-pool)
                (rxr-installed-observe token fn-rx-provider fn-page-read-pool)
                (mv result fn-page-read-pool))))))
      answer)))
(assert-event
 (equal (rxr-observe)
        '(:installed (:rx-capacity 0 0 4096) 0 4096
          (4608 0 0 0 0) (0 0 0 0 1) 1 :stale-capacity t
          :receive-copy 0 16 0)))
