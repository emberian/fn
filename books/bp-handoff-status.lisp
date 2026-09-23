; Effective application receipt handoff from the two durable authorities.
; FNBS kind 7 retains :owed; a matching durable outbound FNBS job ends it.
; The receipt ADU argument is the exact FNRJ replay projection supplied by
; the owner caller.  Missing or contradictory evidence leaves it owed.
(in-package "ACL2")
(include-book "bp-app-handoff")

(defun fn-bpah-handoff-carrier-job (st view)
  (declare (xargs :guard t))
  (fn-bpn-find-job
   (list (fn-bpn-nth 5 view) (fn-bpn-nth 6 view) (fn-bpn-nth 7 view))
   (fn-bpn-machine-state-jobs (fn-bpnf-base st))))

(defun fn-bpah-handoff-receipt-id-matchesp (handoff receipt-adu)
  (declare (xargs :guard t))
  (let ((decoded (fn-bpa-decode-exact receipt-adu)))
    (and (fn-bpa-result-okp decoded)
         (fn-bpa-receiptp (fn-bpa-result-message decoded))
         (equal (fn-record-string-octets
                 (fn-bpa-receipt-id (fn-bpa-result-message decoded)))
                (fn-bpn-nth 1 handoff)))))

(defun fn-bpah-handoff-effective-status (st handoff receipt-adu peer)
  (declare (xargs :guard t))
  (if (not (fn-bpnf-handoffp handoff))
      :invalid
    (if (not (equal (fn-bpn-nth 3 handoff) :owed))
        :invalid
      (let ((view (fn-bpah-outbox-view-for st handoff)))
        (if (and view
                 (fn-bpah-handoff-receipt-id-matchesp handoff receipt-adu)
                 (fn-bpah-outbox-job-matchp st view receipt-adu peer))
            (list :handed-off
                  (fn-bpn-job-sequence
                   (fn-bpah-handoff-carrier-job st view)))
          :owed)))))

(defun fn-bpah-handoff-for-view-aux (view handoffs)
  (declare (xargs :guard t :measure (acl2-count handoffs)))
  (if (atom handoffs)
      nil
    (if (and (fn-bpnf-handoffp (car handoffs))
             (equal (fn-bpn-nth 1 (car handoffs)) (fn-bpn-nth 1 view))
             (equal (fn-bpn-nth 2 (car handoffs)) (fn-bpn-nth 2 view)))
        (car handoffs)
      (fn-bpah-handoff-for-view-aux view (cdr handoffs)))))

(defun fn-bpah-handoff-for-view (st view)
  (declare (xargs :guard t))
  (fn-bpah-handoff-for-view-aux view (fn-bpnf-handoffs st)))

; This is the host-called decision.  The host passes the ACL2-selected view
; and FNRJ replay bytes; it does not synthesize or update the handoff row.
(defun fn-bpah-outbox-effective-status (st view receipt-adu peer)
  (declare (xargs :guard t))
  (let ((handoff (fn-bpah-handoff-for-view st view)))
    (if (and (equal (fn-bpn-nth 0 view) :outbox)
             (equal (fn-bpah-outbox-view-for st handoff) view))
        (fn-bpah-handoff-effective-status st handoff receipt-adu peer)
      :invalid)))

(defthm fn-bpah-effective-status-branch
  (implies
   (equal (car (fn-bpah-handoff-effective-status
                st handoff receipt-adu peer)) :handed-off)
   (and (fn-bpnf-handoffp handoff)
        (equal (fn-bpn-nth 3 handoff) :owed)
        (fn-bpah-outbox-view-for st handoff)
        (fn-bpah-handoff-receipt-id-matchesp handoff receipt-adu)
        (fn-bpah-outbox-job-matchp
         st (fn-bpah-outbox-view-for st handoff) receipt-adu peer)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpah-handoff-effective-status)
                           (fn-bpah-outbox-view-for
                            fn-bpah-handoff-receipt-id-matchesp
                            fn-bpah-outbox-job-matchp))))
  :rule-classes nil)

(defthm fn-bpah-job-match-binds-carrier
  (implies
   (fn-bpah-outbox-job-matchp st view receipt-adu peer)
   (let ((job (fn-bpah-handoff-carrier-job st view)))
     (and (fn-bpn-jobp job)
          (equal (fn-bpn-job-peer job) peer)
          (equal (fn-bpb-payload (fn-bpn-job-bundle job)) receipt-adu))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpah-outbox-job-matchp
                            fn-bpah-handoff-carrier-job)
                           (fn-bpn-find-job))))
  :rule-classes nil)

(defthm fn-bpah-effective-handoff-binds-exact-durable-carrier
  (implies
   (equal (car (fn-bpah-handoff-effective-status
                st handoff receipt-adu peer)) :handed-off)
   (let* ((view (fn-bpah-outbox-view-for st handoff))
          (job (fn-bpah-handoff-carrier-job st view)))
     (and (fn-bpnf-handoffp handoff)
          (equal (fn-bpn-nth 3 handoff) :owed)
          (fn-bpn-jobp job)
          (equal (fn-bpn-job-peer job) peer)
          (equal (fn-bpb-payload (fn-bpn-job-bundle job)) receipt-adu)
          (fn-bpah-handoff-receipt-id-matchesp handoff receipt-adu)
          (equal (fn-bpn-nth 1
                  (fn-bpah-handoff-effective-status
                   st handoff receipt-adu peer))
                 (fn-bpn-job-sequence job)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpah-effective-status-branch)
                 (:instance fn-bpah-job-match-binds-carrier
                            (view (fn-bpah-outbox-view-for st handoff))))
           :in-theory (e/d (fn-bpah-handoff-effective-status)
                           (fn-bpah-outbox-view-for
                            fn-bpah-handoff-receipt-id-matchesp
                            fn-bpah-outbox-job-matchp
                            fn-bpah-handoff-carrier-job))))
  :rule-classes nil)

; The caller obtains receipt-adu from FNRJ's replayed state, through
; fn-bprj-receipt-adu.  This corollary names that cross-journal premise rather
; than treating an arbitrary host byte vector as a committed receipt.
(defthm fn-bpah-effective-handoff-binds-fnrj-replay-adu
  (implies
   (and (equal receipt-adu
               (fn-bpr-receipt-adu (fn-bpaj-receiver fnrj) request))
        (equal (car (fn-bpah-handoff-effective-status
                     st handoff receipt-adu peer)) :handed-off))
   (let* ((view (fn-bpah-outbox-view-for st handoff))
          (job (fn-bpah-handoff-carrier-job st view)))
     (and (fn-bpn-jobp job)
          (equal (fn-bpn-job-peer job) peer)
          (equal (fn-bpb-payload (fn-bpn-job-bundle job))
                 (fn-bpr-receipt-adu (fn-bpaj-receiver fnrj) request)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance
                  fn-bpah-effective-handoff-binds-exact-durable-carrier))
           :in-theory nil))
  :rule-classes nil)

(defthm fn-bpah-host-outbox-status-branch
  (implies
   (equal (car (fn-bpah-outbox-effective-status
                st view receipt-adu peer)) :handed-off)
   (let ((handoff (fn-bpah-handoff-for-view st view)))
     (and (equal (fn-bpah-outbox-view-for st handoff) view)
          (equal (car (fn-bpah-handoff-effective-status
                       st handoff receipt-adu peer)) :handed-off))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bpah-outbox-effective-status)
                           (fn-bpah-handoff-for-view
                            fn-bpah-outbox-view-for
                            fn-bpah-handoff-effective-status))))
  :rule-classes nil)

(defthm fn-bpah-host-outbox-status-binds-fnrj-and-carrier
  (implies
   (and (equal receipt-adu
               (fn-bpr-receipt-adu (fn-bpaj-receiver fnrj) request))
        (equal (car (fn-bpah-outbox-effective-status
                     st view receipt-adu peer)) :handed-off))
   (let* ((handoff (fn-bpah-handoff-for-view st view))
          (job (fn-bpah-handoff-carrier-job st view)))
     (and (equal (fn-bpah-outbox-view-for st handoff) view)
          (fn-bpn-jobp job)
          (equal (fn-bpn-job-peer job) peer)
          (equal (fn-bpb-payload (fn-bpn-job-bundle job))
                 (fn-bpr-receipt-adu (fn-bpaj-receiver fnrj) request))
          (fn-bpah-handoff-receipt-id-matchesp handoff receipt-adu))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpah-host-outbox-status-branch)
                 (:instance fn-bpah-effective-handoff-binds-exact-durable-carrier
                            (handoff (fn-bpah-handoff-for-view st view))))
           :in-theory nil))
  :rule-classes nil)

(verify-guards fn-bpah-handoff-carrier-job)
(verify-guards fn-bpah-handoff-receipt-id-matchesp)
(verify-guards fn-bpah-handoff-effective-status)
(verify-guards fn-bpah-handoff-for-view-aux)
(verify-guards fn-bpah-handoff-for-view)
(verify-guards fn-bpah-outbox-effective-status)
