; Exact reserve/register call composition. The existing PRS observer is reused;
; unknown registry/abort callees are retained, never priced by invented numbers.
(in-package "ACL2")
(include-book "connection-start-source-cost")
(local (include-book "arithmetic-5/top" :dir :system))
(local (defthm fn-icrc-fields
 (and (equal (fn-prsc-value (list value cells ops)) value)
      (equal (fn-prsc-cells (list value cells ops)) (nfix cells))
      (equal (fn-prsc-trace (list value cells ops)) ops))
 :hints (("Goal" :in-theory (enable fn-prsc-value fn-prsc-cells fn-prsc-trace fn-prsc-at)))))
(local (defthm fn-icrc-at-mv-nth
 (implies (natp n) (equal (fn-prsc-at n x) (mv-nth n x)))
 :hints (("Goal" :induct (fn-prsc-at n x)))))
(defun fn-icrc-candidate (fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard t))
 (let* ((free (fn-ibp-connection-free fn-index-backing))
        (high (fn-ibp-connection-highwater fn-index-backing))
        (cap (fn-ibp-pool-capacity fn-index-backing))
        (capacity (* 64 cap))
        (trace (list nil 0 (list (list :multiply (list 64 cap)))
                 (list (list 'fn-icr-candidate (list free high cap))))))
  (cond ((consp free)
         (if (and (natp (car free)) (< (car free) high) (< (car free) capacity))
             (mv :recycled (car free) trace) (mv :recovery-required nil trace)))
        (free (mv :recovery-required nil trace))
        ((< high capacity) (mv :fresh high trace))
        (t (mv :unavailable nil trace)))))
(defthm fn-icrc-candidate-observes-complete-result
 (equal (let ((seen (fn-icrc-candidate backing)))
          (list (mv-nth 0 seen) (mv-nth 1 seen)))
        (fn-icr-candidate backing)))
(defun fn-icrc-reserve (id demand fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard t :verify-guards nil))
 (cond ((fn-ibp-connection-pending fn-index-backing)
        (mv (fn-icr-pending-status (fn-ibp-connection-pending fn-index-backing))
            nil fn-index-backing fn-page-read-pool
            (list nil 0 nil (list (list 'fn-icr-pending-status
                    (list (fn-ibp-connection-pending fn-index-backing)))))))
       ((not (and (natp id) (fn-prs-vectorp demand) (equal (fn-prl-nth 4 demand) 1)))
        (mv :unsupported-runtime nil fn-index-backing fn-page-read-pool
            (list nil 0 nil (list (list :reserve-input id demand)))))
       (t
        (mv-let (kind ordinal candidate) (fn-icrc-candidate fn-index-backing)
         (if (not (and (member-eq kind '(:fresh :recycled)) (natp ordinal)))
             (mv kind nil fn-index-backing fn-page-read-pool candidate)
           (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
                  (budget (fn-prl-nth 0 ledger))
                  (issue (fn-prsc-issue budget (fn-prl-baseline ledger) '(0 0 0 0 0)
                          (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger) (fn-prl-nth 4 budget) demand))
                  (result (fn-prsc-value issue))
                  (word (fn-prsc-at 0 result)) (issued (fn-prsc-at 1 result))
                  (charged (fn-prsc-at 2 result))
                  (source (fn-copsc-join candidate
                      (list nil (fn-prsc-cells issue) (fn-prsc-trace issue)
                       (list (list 'fn-prs-issue (list budget (fn-prl-baseline ledger)
                         '(0 0 0 0 0) (fn-prl-nth 1 ledger) (fn-prl-nth 2 ledger)
                         (fn-prl-nth 4 budget) demand)))))))
             (if (not (eq word :admitted))
                 (mv word nil fn-index-backing fn-page-read-pool source)
               (let* ((fn-page-read-pool
                       (fn-owner-page-read-keep-ledger
                         (fn-prl-build budget charged issued (fn-prl-nth 3 ledger)
                                       (fn-prl-baseline ledger)) fn-page-read-pool))
                      (token (list :connection-holder issued
                                  (+ 1 (floor ordinal 64)) (mod ordinal 64)))
                      (receipt (list :connection-reservation token id ordinal kind demand :charged nil))
                      (fn-index-backing
                       (if (eq kind :fresh)
                           (update-fn-ibp-connection-highwater (+ 1 ordinal) fn-index-backing)
                         (update-fn-ibp-connection-free
                           (let ((free (fn-ibp-connection-free fn-index-backing)))
                             (if (consp free) (cdr free) free)) fn-index-backing)))
                      (fn-index-backing (update-fn-ibp-connection-pending receipt fn-index-backing)))
                 (mv :reserved token fn-index-backing fn-page-read-pool
                  (fn-copsc-join source
                   (list nil (+ (if (fn-prl-baseline ledger) 5 4) 5 4 8)
                    (fn-atsc-append
                      (list (list :floor (list ordinal 64))
                            (list :add (list 1 (floor ordinal 64)))
                            (list :mod (list ordinal 64)))
                      (if (eq kind :fresh) (list (list :add (list 1 ordinal))) nil))
                    (list '(:ledger-publication fn-prl-build fn-owner-page-read-keep-ledger)
                          '(:constructor :connection-holder 4)
                          '(:constructor :connection-reservation 8)
                          (list :candidate-publish kind ordinal)))))))))))))
(local (defthm fn-icrc-candidate-fields
 (and (equal (mv-nth 0 (fn-icrc-candidate backing)) (mv-nth 0 (fn-icr-candidate backing)))
      (equal (mv-nth 1 (fn-icrc-candidate backing)) (mv-nth 1 (fn-icr-candidate backing))))
 :hints (("Goal" :use fn-icrc-candidate-observes-complete-result
  :in-theory (disable fn-icrc-candidate fn-icr-candidate)))))
(local (defthm fn-icrc-prsc-value
 (equal (fn-prsc-value (fn-prsc-issue budget used rescue charged next limit demand))
        (fn-prs-issue budget used rescue charged next limit demand))
 :hints (("Goal" :use fn-prsc-issue-observes-complete-actual-result
   :in-theory (disable fn-prsc-issue fn-prs-issue fn-prsc-value)))))
(defthm fn-icrc-reserve-observes-complete-actual-result
 (equal (let ((seen (fn-icrc-reserve id demand backing pool)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen)))
        (fn-icr-reserve id demand backing pool))
 :hints (("Goal" :in-theory
   (disable fn-icrc-candidate fn-icr-candidate fn-prsc-issue fn-prs-issue
            fn-prsc-value fn-prsc-cells fn-prsc-trace fn-copsc-join
            fn-owner-page-read-keep-ledger fn-prl-build fn-owner-page-read-ledger
            fn-prl-nth fn-prl-baseline)))
 :rule-classes nil)
(verify-guards fn-icrc-reserve
 :hints (("Goal" :in-theory (disable fn-prsc-issue fn-prsc-value fn-prsc-cells
                       fn-prsc-trace fn-copsc-join fn-owner-page-read-keep-ledger))))
(defun fn-icrc-register (token fuel fn-index-backing)
 (declare (xargs :stobjs fn-index-backing :guard (natp fuel)))
 (let ((receipt (fn-ibp-connection-pending fn-index-backing)))
  (cond ((not (and (fn-ich-tokenp token)
                   (eq (fn-omk-at 0 receipt) :connection-reservation)
                   (equal (fn-omk-at 1 receipt) token)))
         (mv :stale fuel fn-index-backing (list nil 0 nil '(register-ticket-check))))
        ((eq (fn-omk-at 6 receipt) :registered)
         (mv :registered fuel fn-index-backing (list nil 0 nil '(register-ticket-check))))
        ((not (eq (fn-omk-at 6 receipt) :charged))
         (mv :recovery-required fuel fn-index-backing (list nil 0 nil '(register-ticket-check))))
        (t
         (let ((fn-index-backing (update-fn-ibp-connection-pending
                  (fn-icr-keep-phase receipt :register-intent nil) fn-index-backing)))
          (mv-let (word payload left fn-index-backing)
           (fn-ibp-connection-event token :reserve (fn-omk-at 2 receipt)
                                   (fn-omk-at 5 receipt) fuel fn-index-backing)
           (let ((sites (list (list 'fn-ibp-connection-event
                        (list token :reserve (fn-omk-at 2 receipt) (fn-omk-at 5 receipt) fuel)
                        (list word payload left)))))
            (if (not (eq word :reserved))
                (let ((fn-index-backing (update-fn-ibp-connection-pending receipt fn-index-backing)))
                 (mv word left fn-index-backing (list nil 8 nil sites)))
              (let ((fn-index-backing (update-fn-ibp-connection-pending
                       (fn-icr-keep-phase receipt :registered nil) fn-index-backing)))
               (mv :registered left fn-index-backing (list nil 16 nil sites)))))))))))
(defthm fn-icrc-register-observes-complete-actual-result
 (equal (let ((seen (fn-icrc-register token fuel backing)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen)))
        (fn-icr-register token fuel backing))
 :hints (("Goal" :in-theory (disable fn-ibp-connection-event fn-icr-keep-phase fn-omk-at)))
 :rule-classes nil)
(defun fn-icsc-reserve-register (id demand fuel fn-index-backing fn-page-read-pool)
 (declare (xargs :stobjs (fn-index-backing fn-page-read-pool) :guard (natp fuel) :verify-guards nil))
 (let* ((depth (fn-ibp-slot-depth fn-index-backing))
        (initial (list nil 0 (list (list :floor (list fuel 8)) (list :add (list 1 depth)))
                   (list (list :registration-preflight fuel depth)))))
  (if (< (floor fuel 8) (+ 1 depth))
      (mv :yield nil fuel fn-index-backing fn-page-read-pool initial)
    (mv-let (reserved token fn-index-backing fn-page-read-pool reserve)
     (fn-icrc-reserve id demand fn-index-backing fn-page-read-pool)
     (let ((prefix (fn-copsc-join initial reserve)))
      (if (not (eq reserved :reserved))
          (mv reserved token fuel fn-index-backing fn-page-read-pool prefix)
        (mv-let (registered left fn-index-backing registration)
         (fn-icrc-register token fuel fn-index-backing)
         (let ((source (fn-copsc-join prefix registration)))
          (cond ((and (eq registered :registered)
                       (let ((receipt (fn-ibp-connection-pending fn-index-backing)))
                        (and (eq (fn-omk-at 0 receipt) :connection-reservation)
                             (equal (fn-omk-at 1 receipt) token)
                             (eq (fn-omk-at 6 receipt) :registered))))
                 (mv :reserved token left fn-index-backing fn-page-read-pool source))
                ((member-eq registered '(:unavailable :refused :yield))
                 (mv-let (aborted remaining fn-index-backing fn-page-read-pool)
                  (fn-icr-abort token (nfix left) fn-index-backing fn-page-read-pool)
                  (let ((seen (fn-copsc-join source (list nil 0 nil
                          (list (list 'fn-icr-abort (list token (nfix left)) (list aborted remaining)))))))
                   (if (eq aborted :released)
                       (mv :refused nil remaining fn-index-backing fn-page-read-pool seen)
                     (mv :recovery-required token remaining fn-index-backing fn-page-read-pool seen)))))
                (t (mv :recovery-required token left fn-index-backing fn-page-read-pool source)))))))))))
(local (defthm fn-icsc-reserve-fields
 (and (equal (mv-nth 0 (fn-icrc-reserve id demand backing pool)) (mv-nth 0 (fn-icr-reserve id demand backing pool)))
      (equal (mv-nth 1 (fn-icrc-reserve id demand backing pool)) (mv-nth 1 (fn-icr-reserve id demand backing pool)))
      (equal (mv-nth 2 (fn-icrc-reserve id demand backing pool)) (mv-nth 2 (fn-icr-reserve id demand backing pool)))
      (equal (mv-nth 3 (fn-icrc-reserve id demand backing pool)) (mv-nth 3 (fn-icr-reserve id demand backing pool))))
 :hints (("Goal" :use fn-icrc-reserve-observes-complete-actual-result
  :in-theory (disable fn-icrc-reserve fn-icr-reserve)))))
(local (defthm fn-icsc-register-fields
 (and (equal (mv-nth 0 (fn-icrc-register token fuel backing)) (mv-nth 0 (fn-icr-register token fuel backing)))
      (equal (mv-nth 1 (fn-icrc-register token fuel backing)) (mv-nth 1 (fn-icr-register token fuel backing)))
      (equal (mv-nth 2 (fn-icrc-register token fuel backing)) (mv-nth 2 (fn-icr-register token fuel backing))))
 :hints (("Goal" :use fn-icrc-register-observes-complete-actual-result
  :in-theory (disable fn-icrc-register fn-icr-register)))))
(defthm fn-icsc-reserve-register-observes-complete-actual-result
 (equal (let ((seen (fn-icsc-reserve-register id demand fuel backing pool)))
          (list (mv-nth 0 seen) (mv-nth 1 seen) (mv-nth 2 seen) (mv-nth 3 seen) (mv-nth 4 seen)))
        (fn-ics-reserve-register id demand fuel backing pool))
 :hints (("Goal" :in-theory (disable fn-icrc-reserve fn-icr-reserve fn-icrc-register fn-icr-register
          fn-icr-abort fn-copsc-join fn-omk-at floor)))
 :rule-classes nil)
(verify-guards fn-icsc-reserve-register
 :hints (("Goal" :in-theory (disable fn-icrc-reserve fn-icrc-register fn-icr-abort fn-copsc-join floor))))
(local (defthm fn-icrc-record-fields
 (and (equal (fn-atsc-cells (list value cells ops calls)) (nfix cells))
      (equal (fn-atsc-ops (list value cells ops calls)) ops))
 :hints (("Goal" :in-theory (enable fn-atsc-cells fn-atsc-ops fn-atsc-at)))))
(local (defthm fn-icrc-prsc-admitted-roster
 (implies (equal (fn-prsc-at 0 (fn-prsc-value
                  (fn-prsc-issue budget used rescue charged next limit demand))) :admitted)
  (and (equal (fn-prsc-cells (fn-prsc-issue budget used rescue charged next limit demand)) 30)
       (equal (len (fn-prsc-trace (fn-prsc-issue budget used rescue charged next limit demand))) 31)))
 :hints (("Goal" :use fn-prsc-admitted-issue-source-roster
  :in-theory (disable fn-prsc-issue fn-prs-issue fn-prsc-value fn-prsc-cells fn-prsc-trace)))))
(local (defthm fn-icrc-ledger-baseline-present
 (fn-prl-baseline ledger) :hints (("Goal" :in-theory (enable fn-prl-baseline)))))
(local (defthm fn-icrc-append-length
 (equal (len (fn-atsc-append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (fn-atsc-append a b)))))
(local (defthm fn-icrc-candidate-trace
 (and (equal (fn-atsc-cells (mv-nth 2 (fn-icrc-candidate backing))) 0)
      (equal (len (fn-atsc-ops (mv-nth 2 (fn-icrc-candidate backing)))) 1))
 :hints (("Goal" :in-theory (enable fn-icrc-candidate)))))
(local (defthm fn-icrc-issuer-word-not-reserved
 (not (equal (mv-nth 0 (fn-prs-issue budget used rescue charged next limit demand)) :reserved))
 :hints (("Goal" :in-theory (e/d (fn-prs-issue) (fn-prs-fundedp fn-prs-plus fn-prs-vectorp))))))
(local (defthm fn-icrc-candidate-word-not-reserved
 (not (equal (mv-nth 0 (fn-icrc-candidate backing)) :reserved))
 :hints (("Goal" :in-theory (enable fn-icrc-candidate)))))
(local (defthm fn-icrc-issuer-car-not-reserved
 (not (equal (car (fn-prs-issue budget used rescue charged next limit demand)) :reserved))
 :hints (("Goal" :use fn-icrc-issuer-word-not-reserved
  :in-theory (e/d (mv-nth) (fn-prs-issue fn-icrc-issuer-word-not-reserved))))))
(local (defthm fn-icrc-candidate-car-not-reserved
 (not (equal (car (fn-icrc-candidate backing)) :reserved))
 :hints (("Goal" :use fn-icrc-candidate-word-not-reserved
 :in-theory (e/d (mv-nth) (fn-icrc-candidate fn-icrc-candidate-word-not-reserved fn-icrc-candidate-fields))))))
(defthm fn-icrc-reserved-source-census
 (implies (equal (mv-nth 0 (fn-icrc-reserve id demand backing pool)) :reserved)
  (and (equal (fn-atsc-cells (mv-nth 4 (fn-icrc-reserve id demand backing pool))) 52)
       (equal (len (fn-atsc-ops (mv-nth 4 (fn-icrc-reserve id demand backing pool))))
              (if (equal (mv-nth 0 (fn-icrc-candidate backing)) :fresh) 36 35))))
 :hints (("Goal" :in-theory
  (disable fn-icsc-reserve-fields fn-icrc-candidate-fields fn-icrc-candidate
           fn-prsc-issue fn-prsc-value fn-prsc-cells fn-prsc-trace
           fn-owner-page-read-ledger fn-owner-page-read-keep-ledger fn-prl-nth fn-prl-baseline
           fn-atsc-cells fn-atsc-ops fn-atsc-sites fn-atsc-append)))
 :rule-classes nil)
