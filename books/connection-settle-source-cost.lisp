; Complete actual settlement envelope. Registry read/release and alias custody
; remain named unpriced source units; no positive runtime tariff is inferred.
(in-package "ACL2")
(include-book "connection-abort-source-cost")
(defun fn-icsc-settle (token fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool)
  :guard (natp fuel) :verify-guards nil))
 (cond
  ((and (fn-ibp-connection-pending fn-index-backing)
        (not (and (equal (fn-omk-at 1 (fn-ibp-connection-pending fn-index-backing)) token)
                  (eq (fn-omk-at 6 (fn-ibp-connection-pending fn-index-backing)) :abort-ready))))
   (mv (fn-icr-pending-status (fn-ibp-connection-pending fn-index-backing)) fuel
       fn-index-backing fn-page-read-pool (list nil 0 nil nil)))
  ((not (fn-ich-tokenp token))
   (mv :stale fuel fn-index-backing fn-page-read-pool (list nil 0 nil nil)))
  (t
   (let* ((depth (fn-ibp-slot-depth fn-index-backing))
          (needed (* 4 (+ 1 depth)))
          (prefix (list nil 0
                    (list (list :add (list 1 depth))
                          (list :multiply (list 4 (+ 1 depth)))) nil)))
    (if (< fuel needed)
     (mv :yield fuel fn-index-backing fn-page-read-pool prefix)
     (mv-let (word row left) (fn-ibp-connection-read token fuel fn-index-backing)
      (let ((prefix (fn-copsc-join prefix
             (list nil 0 nil (list (list :unpriced-call 'fn-ibp-connection-read
                                  (list token fuel) (list word row left)))))))
       (if (not (eq word :present))
        (mv word left fn-index-backing fn-page-read-pool prefix)
        (mv-let (ready pin grant) (fn-ich-row-release-ready row)
         (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
                (charged (fn-prl-nth 1 ledger))
                (segment (fn-omk-at 2 token)) (local-slot (fn-omk-at 3 token))
                (base (- segment 1)) (scaled (* 64 base))
                (ordinal (+ scaled local-slot))
                (prefix (fn-copsc-join prefix
                 (list nil 0
                  (list (list :subtract (list segment 1))
                        (list :multiply (list 64 base))
                        (list :add (list scaled local-slot)))
                  (list (list :unpriced-call 'fn-ich-row-release-ready
                               (list row) (list ready pin grant)))))))
          (cond
           ((not (eq ready :ready)) (mv ready left fn-index-backing fn-page-read-pool prefix))
           ((not (and (fn-prs-vectorp grant) (fn-prs-vectorp charged)
                      (fn-prs-below grant charged)
                      (< ordinal (fn-ibp-connection-highwater fn-index-backing))))
            (mv :recovery-required left fn-index-backing fn-page-read-pool prefix))
           (t
            (let* ((fn-index-backing
                    (update-fn-ibp-connection-pending
                     (list :connection-reservation token (fn-omk-at 2 row) ordinal
                           :retiring grant :settle-intent pin) fn-index-backing))
                   (prefix (fn-copsc-join prefix (list nil 8 nil '((:constructor :settle-intent 8))))))
             (mv-let (released actual-grant remaining fn-index-backing)
              (fn-ibp-connection-release token (nfix left) fn-index-backing)
              (let ((prefix (fn-copsc-join prefix
                     (list nil 0 nil (list (list :unpriced-call 'fn-ibp-connection-release
                                  (list token (nfix left)) (list released actual-grant remaining)))))))
               (if (not (and (eq released :released) (equal actual-grant grant)))
                (mv :recovery-required remaining fn-index-backing fn-page-read-pool prefix)
                (let* ((release (fn-icac-release charged grant))
                       (fn-page-read-pool
                        (fn-owner-page-read-keep-ledger
                         (fn-prl-build (fn-prl-nth 0 ledger) (fn-atsc-value release)
                          (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)) fn-page-read-pool))
                       (fn-index-backing
                        (update-fn-ibp-connection-free
                         (cons ordinal (fn-ibp-connection-free fn-index-backing)) fn-index-backing))
                       (fn-index-backing (update-fn-ibp-connection-pending nil fn-index-backing)))
                 (mv :released remaining fn-index-backing fn-page-read-pool
                  (fn-copsc-join prefix (fn-copsc-join release
                   (list nil (+ (if (fn-prl-nth 4 ledger) 5 4) 5 1) nil
                    '((:ledger-publication fn-prl-build fn-owner-page-read-keep-ledger)
                      (:constructor :free-cell 1)))))))))))))))))))))))
(defthm fn-icsc-settle-observes-complete-actual-result
 (equal (let ((seen (fn-icsc-settle token fuel backing pool)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen)))
        (fn-icr-settle token fuel backing pool))
 :rule-classes nil
 :hints (("Goal" :in-theory
  (disable fn-ibp-connection-read fn-ibp-connection-release fn-ich-row-release-ready
   fn-prl-build fn-owner-page-read-ledger fn-owner-page-read-keep-ledger
   fn-prs-release-reusable fn-icac-release fn-copsc-join fn-omk-at
   fn-prs-vectorp fn-prs-below fn-ich-tokenp fn-icr-pending-status fn-prl-nth
   fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites))))
(local (defthm fn-icsc-nats-true-list
 (implies (fn-prs-nats-p xs) (true-listp xs))
 :hints (("Goal" :in-theory (enable fn-prs-nats-p)))))
(verify-guards fn-icsc-settle
 :hints (("Goal" :in-theory
  (e/d (fn-prs-vectorp) (fn-ibp-connection-read fn-ibp-connection-release
   fn-ich-row-release-ready fn-owner-page-read-ledger)))))
