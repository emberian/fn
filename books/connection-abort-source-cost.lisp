; Complete actual abort envelope; reusable counter release and charged cancellation
; are observed. Registered close/settle callees remain exact named unpriced units.
(in-package "ACL2")
(include-book "connection-registry-source-cost")
(defun fn-icac-release (charged grant)
 (declare (xargs :guard (and (true-listp charged) (true-listp grant))))
 (list (fn-prs-release-reusable charged grant) 5
  (list (list :subtract (list (nfix (nth 0 charged)) (nfix (nth 0 grant))))
        (list :subtract (list (nfix (nth 1 charged)) (nfix (nth 1 grant))))
        (list :subtract (list (nfix (nth 2 charged)) (nfix (nth 2 grant))))
        (list :subtract (list (nfix (nth 3 charged)) (nfix (nth 3 grant)))))
  '(fn-prs-release-reusable)))
(defthm fn-icac-release-observes-complete-actual-result
 (equal (fn-atsc-value (fn-icac-release charged grant)) (fn-prs-release-reusable charged grant))
 :hints (("Goal" :in-theory (enable fn-atsc-value fn-atsc-at))))
(defun fn-icac-abort (token fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard (natp fuel) :verify-guards nil))
 (let* ((receipt (fn-ibp-connection-pending fn-index-backing))
        (phase (fn-omk-at 6 receipt)) (grant (fn-omk-at 5 receipt)) (ordinal (fn-omk-at 3 receipt))
        (ledger (fn-owner-page-read-ledger fn-page-read-pool)) (charged (fn-prl-nth 1 ledger)))
  (cond
   ((not (and (fn-omk-widthp receipt 8) (fn-ich-tokenp token)
               (eq (fn-omk-at 0 receipt) :connection-reservation) (equal (fn-omk-at 1 receipt) token)))
    (mv :stale fuel fn-index-backing fn-page-read-pool (list nil 0 nil nil)))
   ((eq phase :abort-ready)
    (mv-let (word left fn-index-backing fn-page-read-pool)
     (fn-icr-settle token fuel fn-index-backing fn-page-read-pool)
     (mv word left fn-index-backing fn-page-read-pool
      (list nil 0 nil (list (list :unpriced-call 'fn-icr-settle (list token fuel) (list word left)))))))
   ((not (member-eq phase '(:charged :registered :source-owned)))
    (mv :recovery-required fuel fn-index-backing fn-page-read-pool (list nil 0 nil nil)))
   ((eq phase :charged)
    (if (not (and (fn-prs-vectorp grant) (fn-prs-vectorp charged) (fn-prs-below grant charged)
                   (natp ordinal) (< ordinal (fn-ibp-connection-highwater fn-index-backing))))
        (mv :recovery-required fuel fn-index-backing fn-page-read-pool (list nil 0 nil nil))
      (let* ((released (fn-icac-release charged grant))
             (fn-index-backing (update-fn-ibp-connection-pending
               (fn-icr-keep-phase receipt :settle-intent nil) fn-index-backing))
             (fn-page-read-pool (fn-owner-page-read-keep-ledger
               (fn-prl-build (fn-prl-nth 0 ledger) (fn-atsc-value released)
                             (fn-prl-nth 2 ledger) (fn-prl-nth 3 ledger) (fn-prl-nth 4 ledger)) fn-page-read-pool))
             (fn-index-backing (update-fn-ibp-connection-free
               (cons ordinal (fn-ibp-connection-free fn-index-backing)) fn-index-backing))
             (fn-index-backing (update-fn-ibp-connection-pending nil fn-index-backing)))
       (mv :released fuel fn-index-backing fn-page-read-pool
         (fn-copsc-join released (list nil (+ 8 (if (fn-prl-nth 4 ledger) 5 4) 5 1) nil
               '((:constructor :reservation-phase 8) (:ledger-publication fn-prl-build fn-owner-page-read-keep-ledger) (:constructor :free-cell 1))))))))
   (t (let* ((depth (fn-ibp-slot-depth fn-index-backing))
             (needed (* 5 (+ 1 depth)))
             (preflight (list nil 0 (list (list :add (list 1 depth)) (list :multiply (list 5 (+ 1 depth)))) nil)))
        (if (< fuel needed) (mv :yield fuel fn-index-backing fn-page-read-pool preflight)
         (let ((fn-index-backing (update-fn-ibp-connection-pending
                 (fn-icr-keep-phase receipt :abort-intent (fn-omk-at 7 receipt)) fn-index-backing)))
          (mv-let (closed payload left fn-index-backing)
           (fn-ibp-connection-event token :close (fn-omk-at 2 receipt) nil fuel fn-index-backing)
           (declare (ignore payload))
           (let ((prefix (fn-copsc-join preflight (list nil 8 nil
                  (list (list :unpriced-call 'fn-ibp-connection-event (list token :close (fn-omk-at 2 receipt) nil fuel) (list closed left)))))))
            (if (not (eq closed :closing))
                (mv :recovery-required left fn-index-backing fn-page-read-pool prefix)
             (let ((fn-index-backing (update-fn-ibp-connection-pending
                    (fn-icr-keep-phase receipt :abort-ready (fn-omk-at 7 receipt)) fn-index-backing)))
              (mv-let (word remaining fn-index-backing fn-page-read-pool)
               (fn-icr-settle token (nfix left) fn-index-backing fn-page-read-pool)
               (mv word remaining fn-index-backing fn-page-read-pool
                (fn-copsc-join prefix (list nil 8 nil
                  (list (list :unpriced-call 'fn-icr-settle (list token (nfix left)) (list word remaining)))))))))))))))))
)
(local (defthm fn-icac-settle-four-values
 (and (true-listp (fn-icr-settle token fuel backing pool))
      (equal (len (fn-icr-settle token fuel backing pool)) 4))
 :hints (("Goal" :in-theory (disable fn-ibp-connection-read fn-ibp-connection-release
  fn-ich-row-release-ready fn-prl-build fn-owner-page-read-ledger fn-owner-page-read-keep-ledger
  fn-prs-release-reusable fn-prs-vectorp fn-prs-below fn-omk-at fn-ich-tokenp)))))
(local (defthm fn-icac-consp-positive
 (implies (consp xs) (< 0 (len xs)))
 :rule-classes :linear
 :hints (("Goal" :expand ((len xs))))))
(local (defthm fn-icac-four-values-reconstruct
 (implies (and (true-listp xs) (equal (len xs) 4))
  (equal (list (mv-nth 0 xs) (mv-nth 1 xs) (mv-nth 2 xs) (mv-nth 3 xs)) xs))
 :hints (("Goal" :in-theory (enable mv-nth) :cases ((and (consp xs) (consp (cdr xs)) (consp (cddr xs)) (consp (cdddr xs)) (not (consp (cddddr xs)))))))))
(local (defthm fn-icac-settle-result-reconstruct
 (equal (list (car (fn-icr-settle token fuel backing pool))
              (mv-nth 1 (fn-icr-settle token fuel backing pool))
              (mv-nth 2 (fn-icr-settle token fuel backing pool))
              (mv-nth 3 (fn-icr-settle token fuel backing pool)))
        (fn-icr-settle token fuel backing pool))
 :hints (("Goal" :in-theory (disable fn-icr-settle fn-icac-four-values-reconstruct)
  :use ((:instance fn-icac-four-values-reconstruct (xs (fn-icr-settle token fuel backing pool))))))))
(defthm fn-icac-abort-observes-complete-actual-result
 (equal (let ((seen (fn-icac-abort token fuel backing pool)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen)))
        (fn-icr-abort token fuel backing pool))
 :hints (("Goal" :in-theory (disable fn-icr-settle fn-ibp-connection-event fn-icr-keep-phase
   fn-owner-page-read-ledger fn-prl-build fn-owner-page-read-keep-ledger fn-omk-at fn-omk-widthp fn-ich-tokenp fn-copsc-join
   fn-prl-nth fn-prs-vectorp fn-prs-below fn-icr-pending-status
   fn-icac-release fn-prs-release-reusable fn-atsc-value fn-atsc-cells fn-atsc-ops fn-atsc-sites)))
 :rule-classes nil)
(local (defthm fn-icac-nats-true-list
 (implies (fn-prs-nats-p xs) (true-listp xs))
 :hints (("Goal" :in-theory (enable fn-prs-nats-p)))))
(verify-guards fn-icac-abort
 :hints (("Goal" :in-theory (e/d (fn-prs-vectorp) (fn-icr-settle fn-ibp-connection-event fn-owner-page-read-ledger)))))
