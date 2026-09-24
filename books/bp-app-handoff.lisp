; A3 handoff selection from the single FNBS held list.  This book makes no
; network or Store decision.  Its result is the application work the native
; owner must drive through the existing Store/FNRJ or release join.
(in-package "ACL2")
(include-book "bp-node-foundation")
(include-book "bp-adu")
(include-book "bp-native-app")
(include-book "bp-session-admission")
(verify-guards fn-bpaj-eid-text)

(defun fn-bpah-local-pendingp (held node)
  (declare (xargs :guard t))
  (and (fn-bpnf-heldp held)
       (fn-bpp-eidp node)
       (let ((bundle (fn-bpnf-held-bundle held)))
         (and (fn-bpb-bundlep bundle)
              (let ((primary (fn-bpb-bundle-primary bundle)))
                (and (fn-bpp-blockp primary)
                     (natp (fn-bpp-flags primary))
                     (not (fn-bpp-fragmentp (fn-bpp-flags primary)))
                     (equal (fn-bpp-destination primary) node)
                     (null (fn-bpn-nth 10 held))
                     (equal (fn-bpn-nth 12 held) '(:dispatch-pending))
                     (null (fn-bpn-nth 14 held))
                     (member-equal (fn-bpah-held-class held)
                                   '(:request :receipt))))))))

(defun fn-bpah-select-oldest (held-list node selected)
  (declare (xargs :guard t))
  (if (atom held-list)
      selected
    (let* ((candidate (car held-list))
           (selected
             (if (and (fn-bpah-local-pendingp candidate node)
                      (or (null selected)
                          (< (nfix (fn-bpn-nth 3 candidate))
                             (nfix (fn-bpn-nth 3 selected)))))
                 candidate selected)))
      (fn-bpah-select-oldest (cdr held-list) node selected))))

(defun fn-bpah-pending-view (st node)
  (declare (xargs :guard t))
  (let ((held (fn-bpah-select-oldest (fn-bpnf-held-list st) node nil)))
    (if (not (fn-bpnf-heldp held))
        nil
      (let* ((bundle (fn-bpnf-held-bundle held))
             (primary (fn-bpb-bundle-primary bundle)))
        (if (and (fn-bpb-bundlep bundle) (fn-bpp-blockp primary))
            (list :delivery
                  (fn-bpnf-held-key (fn-bpnf-held-principal held)
                                     (fn-bpnf-held-id held))
                  (fn-bpah-held-class held)
                  (fn-bpb-payload bundle)
                  (fn-bpn-nth 4 held)
                  (fn-bpp-primary-identity primary)
                  (fn-bpaj-eid-text (fn-bpp-source primary))
                  (fn-bpaj-eid-text (fn-bpp-destination primary)))
          nil)))))

; The native bp-node caller asks this selector before invoking Store.  A
; fragment can carry bytes that happen to decode as a complete request ADU;
; those bytes are not eligible until a durable family replacement has made a
; new whole-bundle held row.
(defthm fn-bpah-local-pending-excludes-fragment
  (implies (fn-bpah-local-pendingp held node)
           (not (fn-bpp-fragmentp
                 (fn-bpp-flags (fn-bpb-bundle-primary
                                (fn-bpnf-held-bundle held))))))
  :hints (("Goal" :in-theory (enable fn-bpah-local-pendingp))))

(defthm fn-bpah-select-oldest-retains-pending
  (implies (or (null selected) (fn-bpah-local-pendingp selected node))
           (let ((h (fn-bpah-select-oldest held-list node selected)))
             (or (null h) (fn-bpah-local-pendingp h node))))
  :hints (("Goal" :induct (fn-bpah-select-oldest held-list node selected)
           :in-theory (disable fn-bpah-local-pendingp fn-bpah-held-class))))

(defthm fn-bpah-host-pending-view-excludes-fragment
  (implies (equal (car (fn-bpah-pending-view st node)) :delivery)
           (not (fn-bpp-fragmentp
                 (fn-bpp-flags
                  (fn-bpb-bundle-primary
                   (fn-bpnf-held-bundle
                    (fn-bpah-select-oldest (fn-bpnf-held-list st)
                                            node nil)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpah-select-oldest-retains-pending
                            (held-list (fn-bpnf-held-list st))
                            (selected nil))
                 (:instance fn-bpah-local-pending-excludes-fragment
                            (held (fn-bpah-select-oldest
                                   (fn-bpnf-held-list st) node nil))))
           :in-theory (e/d (fn-bpah-pending-view)
                           (fn-bpah-select-oldest-retains-pending
                            fn-bpah-local-pending-excludes-fragment
                            fn-bpah-local-pendingp fn-bpah-select-oldest
                            fn-bpah-held-class fn-bpp-fragmentp))))
  :rule-classes nil)

(defun fn-bpah-view-class (view)
  (declare (xargs :guard t))
  (fn-bpn-nth 2 view))

;; D23: the one source decision for a delivered view.  The ingress is the
;; TCPCL neighbour stamped at reception; element 6 is the bundle's source EID
;; text.  `fn-bpaj-carried-source-decision' (bp-session-admission) decides
;; direct, carried (judged under the author's own enrollment) or refused.
(defun fn-bpah-view-source-decision (view cfg)
  (declare (xargs :guard t))
  (let ((ingress (fn-bpn-nth 4 view)))
    (if (and (fn-bpnf-cl-ingressp ingress)
             (stringp (fn-bpn-nth 6 view)))
        (fn-bpaj-carried-source-decision
         cfg (fn-bpnf-ingress-principal ingress)
         (fn-bpn-nth 5 ingress) (fn-bpn-nth 6 view))
      (list :refused :ingress))))

(defun fn-bpah-request-trustedp (view cfg)
  (declare (xargs :guard t))
  (and (consp view)
       (equal (car view) :delivery)
       (equal (fn-bpah-view-class view) :request)
       (fn-bpaj-source-decision-trustedp
        (fn-bpah-view-source-decision view cfg))))

(defun fn-bpah-receipt-trustedp (view cfg)
  (declare (xargs :guard t))
  (and (consp view)
       (equal (car view) :delivery)
       (equal (fn-bpah-view-class view) :receipt)
       (fn-bpaj-source-decision-trustedp
        (fn-bpah-view-source-decision view cfg))
       (let ((decoded (fn-bpa-decode-exact (fn-bpn-nth 3 view))))
         (and (fn-bpa-result-okp decoded)
              (fn-bpa-receiptp (fn-bpa-result-message decoded))
              (equal (fn-bpa-receipt-issuer
                      (fn-bpa-result-message decoded))
                     (fn-bpn-nth 6 view))
              (equal (fn-bpa-receipt-peer-eid
                      (fn-bpa-result-message decoded))
                     (fn-bpn-nth 6 view))))))

; The line the host prints for every dispatched request or receipt: ACL2's
; decision, its principal(s) as configured names, or its refusal reason.
(defun fn-bpah-source-decision-line (view cfg)
  (declare (xargs :guard t))
  (let ((d (fn-bpah-view-source-decision view cfg)))
    (cond ((equal (car d) :direct)
           (string-append "direct principal="
                          (fn-record-octets-string (fn-bpaj-nth 1 d))))
          ((equal (car d) :carried)
           (string-append
            "carried carrier="
            (string-append
             (fn-record-octets-string (fn-bpaj-nth 1 d))
             (string-append " author="
                            (fn-record-octets-string (fn-bpaj-nth 2 d))))))
          (t (string-append
              "refused reason="
              (let ((r (fn-bpaj-nth 1 d)))
                (cond ((equal r :generation) "generation")
                      ((equal r :source-not-carried) "source-not-carried")
                      ((equal r :carried-source-unenrolled)
                       "carried-source-unenrolled")
                      (t "ingress"))))))))

; The owed handoff is an application obligation, not TCPCL custody evidence.
; Bind it back to the exact delivered held request before the host asks FNRJ
; for the durable receipt ADU and enqueues a return bundle.
(defun fn-bpah-outbox-work-id (rid arrival)
  (declare (xargs :guard t))
  (fn-bpn-append
   (fn-record-string-octets "bp-receipt:")
   (fn-bpn-append
    rid (cons 58
              (fn-record-string-octets
               (fn-prov-nat-string arrival))))))

(defun fn-bpah-outbox-view-for (st handoff)
  (declare (xargs :guard t))
  (let* ((key (fn-bpn-nth 2 handoff))
         (held (fn-bpnf-find-held key (fn-bpnf-held-list st)))
         (bundle (fn-bpnf-held-bundle held))
         (primary (fn-bpb-bundle-primary bundle)))
    (if (and (fn-bpnf-handoffp handoff)
             (equal (fn-bpn-nth 3 handoff) :owed)
             (fn-bpnf-heldp held)
             (fn-bpb-bundlep bundle)
             (fn-bpp-blockp primary)
             (equal (fn-bpah-held-class held) :request)
             (equal (fn-bpn-nth 12 held) '(:dispatch-done))
             (member-equal (fn-bpn-nth 1 (fn-bpn-nth 10 held))
                           '(:request-accepted :request-duplicate
                             :request-returned))
             (equal (fn-bpn-nth 10 held)
                    (list :delivered
                          (fn-bpn-nth 1 (fn-bpn-nth 10 held))
                          (fn-bpn-nth 1 handoff)))
             (fn-frame-textp (fn-bpn-nth 1 handoff)))
        (list :outbox (fn-bpn-nth 1 handoff) key
              (fn-bpb-payload bundle)
              (fn-bpaj-eid-text (fn-bpp-source primary))
              (fn-bpah-outbox-work-id (fn-bpn-nth 1 handoff)
                                      (fn-bpn-nth 3 held))
              (fn-record-string-octets "return")
              0)
      nil)))

(defun fn-bpah-select-owed (st handoffs)
  (declare (xargs :guard t))
  (if (atom handoffs)
      nil
    (or (fn-bpah-outbox-view-for st (car handoffs))
        (fn-bpah-select-owed st (cdr handoffs)))))

(defun fn-bpah-select-owed-after (st handoffs after)
  (declare (xargs :guard t))
  (if (atom handoffs)
      nil
    (if (equal (fn-bpn-nth 2 (car handoffs)) after)
        (fn-bpah-select-owed st (cdr handoffs))
      (fn-bpah-select-owed-after st (cdr handoffs) after))))

(defun fn-bpah-outbox-view-after (st after)
  (declare (xargs :guard t))
  (if after
      (fn-bpah-select-owed-after st (fn-bpnf-handoffs st) after)
    (fn-bpah-select-owed st (fn-bpnf-handoffs st))))

(defun fn-bpah-outbox-view (st)
  (declare (xargs :guard t))
  (fn-bpah-outbox-view-after st nil))

(defun fn-bpah-outbox-peer-matchp (view configured-peer)
  (declare (xargs :guard t))
  (and (equal (fn-bpn-nth 0 view) :outbox)
       (stringp configured-peer)
       (equal (fn-bpn-nth 4 view) configured-peer)))

(defun fn-bpah-outbox-job-matchp (st view receipt-adu peer)
  (declare (xargs :guard t))
  (let ((job (fn-bpn-find-job
              (list (fn-bpn-nth 5 view) (fn-bpn-nth 6 view)
                    (fn-bpn-nth 7 view))
              (fn-bpn-machine-state-jobs (fn-bpnf-base st)))))
    (and (equal (fn-bpn-nth 0 view) :outbox)
         (fn-bpn-jobp job)
         (equal (fn-bpn-job-peer job) peer)
         (equal (fn-bpb-payload (fn-bpn-job-bundle job)) receipt-adu))))

(defthm fn-bpah-no-held-no-delivery
  (equal (fn-bpah-pending-view
          (fn-bpnf-state base nil outcomes handoffs correlation issued waits
                         epoch next-op)
          node)
         nil))

(defthm fn-bpah-untrusted-source-never-authorizes-receipt
  (implies (not (fn-bpaj-source-decision-trustedp
                 (fn-bpah-view-source-decision view cfg)))
           (not (fn-bpah-receipt-trustedp view cfg)))
  :hints (("Goal" :in-theory (e/d (fn-bpah-receipt-trustedp)
                                  (fn-bpah-view-source-decision
                                   fn-bpaj-source-decision-trustedp)))))

(defthm fn-bpah-untrusted-source-never-authorizes-request
  (implies (not (fn-bpaj-source-decision-trustedp
                 (fn-bpah-view-source-decision view cfg)))
           (not (fn-bpah-request-trustedp view cfg)))
  :hints (("Goal" :in-theory (e/d (fn-bpah-request-trustedp)
                                  (fn-bpah-view-source-decision
                                   fn-bpaj-source-decision-trustedp)))))
