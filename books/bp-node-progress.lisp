; One host-called progress extension over the FNBS state.  Ordinary events
; delegate to the report/fragment/foundation owner.  Route waits are volatile:
; recovery clears them and a later progress event re-evaluates the held rows.
(in-package "ACL2")
(include-book "bp-report-author")
(include-book "bp-app-handoff-time")
(include-book "bp-node-receive-boundary")
(include-book "bp-node-debt")
(include-book "bp-fnbs-conflict-codec")
(set-verify-guards-eagerness 0)

(defconst *fn-bpnp-max-routes* 64)
; This deployed profile keeps one received-FNBS control record above exact
; cleanup debt.  The policy slot in spec §2.1 is not yet a host input.
(defconst *fn-bpnp-control-margin* 1)

(defun fn-bpnp-single-peer-routes (peer)
  (declare (xargs :guard t))
  (if (fn-bpp-eidp peer) (list (list peer peer)) nil))

(defun fn-bpnp-routep (route)
  (declare (xargs :guard t))
  (and (true-listp route) (equal (len route) 2)
       (fn-bpp-eidp (fn-bpn-nth 0 route))
       (fn-bpp-eidp (fn-bpn-nth 1 route))))

(defun fn-bpnp-routesp (routes)
  (declare (xargs :guard t :measure (acl2-count routes)))
  (if (atom routes) (null routes)
    (and (fn-bpnp-routep (car routes))
         (fn-bpnp-routesp (cdr routes)))))

(defun fn-bpnp-route-peer (destination routes)
  (declare (xargs :guard t :measure (acl2-count routes)))
  (if (atom routes) nil
    (if (equal destination (fn-bpn-nth 0 (car routes)))
        (fn-bpn-nth 1 (car routes))
      (fn-bpnp-route-peer destination (cdr routes)))))

; Slot 11 extends the same :bpnf-state with per-key volatile waits.  Existing
; ten-argument state constructors remain compatible and make this slot nil.
(defun fn-bpnp-waits (st)
  (declare (xargs :guard t))
  (fn-bpn-nth 11 st))

; These counters are maintained by the actual outer reducer.  USED counts
; immutable received FNBS finals, including consumed historical rows.  DEBT
; is the cold fn-bpnd-debt projection cached for served admission.
(defun fn-bpnp-used (st)
  (declare (xargs :guard t))
  (fn-bpn-nth 12 st))

(defun fn-bpnp-debt (st)
  (declare (xargs :guard t))
  (fn-bpn-nth 13 st))

(defun fn-bpnp-with-credit (st used debt)
  (declare (xargs :guard t))
  (if (not (true-listp st)) st
    (update-nth 13 debt (update-nth 12 used st))))

(defun fn-bpnp-with-waits (st waits)
  (declare (xargs :guard t))
  (if (not (true-listp st)) st
    (if (and (null waits) (< (len st) 12)) st
      (update-nth 11 waits st))))

; Outbound sessions and the exact wire awaiting a kind-8 publication are
; volatile fields of the same FNBS state.  Recovery clears both.  The wire is
; never reconstructed by Lisp after ACL2 has made its forwarding decision.
(defun fn-bpnp-sessions (st)
  (declare (xargs :guard t))
  (fn-bpn-nth 14 st))

(defun fn-bpnp-pending-image (st)
  (declare (xargs :guard t))
  (fn-bpn-nth 15 st))

(defun fn-bpnp-with-runtime (st sessions pending-image)
  (declare (xargs :guard t))
  (if (not (true-listp st)) st
    (update-nth 15 pending-image (update-nth 14 sessions st))))

(defun fn-bpnp-with-issued (st issued)
  (declare (xargs :guard t))
  (fn-bpnp-with-runtime
   (fn-bpnp-with-credit (fn-bpnf-with-issued st issued)
                        (fn-bpnp-used st) (fn-bpnp-debt st))
   (fn-bpnp-sessions st) (fn-bpnp-pending-image st)))

(defun fn-bpnp-session (peer session mru)
  (declare (xargs :guard t))
  (list :bpnp-session peer session mru))

(defun fn-bpnp-sessionp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (equal (car x) :bpnp-session)
       (fn-bpp-eidp (fn-bpn-nth 1 x))
       (fn-bpnp-session-idp (fn-bpn-nth 2 x))
       (fn-frame-natp (fn-bpn-nth 3 x))
       (< 0 (fn-bpn-nth 3 x))))

; The carried session table: every row a well-formed session.  It is a
; guard premise of the served step, never a runtime check on it.
(defun fn-bpnp-session-listp (x)
  (declare (xargs :guard t))
  (if (atom x) (null x)
    (and (fn-bpnp-sessionp (car x))
         (fn-bpnp-session-listp (cdr x)))))

(defun fn-bpnp-remove-peer-session (peer sessions)
  (declare (xargs :guard t :measure (acl2-count sessions)))
  (if (atom sessions) nil
    (if (equal (fn-bpn-nth 1 (car sessions)) peer)
        (fn-bpnp-remove-peer-session peer (cdr sessions))
      (cons (car sessions)
            (fn-bpnp-remove-peer-session peer (cdr sessions))))))

(defun fn-bpnp-open-session (sessions peer session mru)
  (declare (xargs :guard t))
  (cons (fn-bpnp-session peer session mru)
        (fn-bpnp-remove-peer-session peer sessions)))

(defun fn-bpnp-session-currentp (sessions peer session mru)
  (declare (xargs :guard t :measure (acl2-count sessions)))
  (if (atom sessions) nil
    (or (equal (car sessions) (fn-bpnp-session peer session mru))
        (fn-bpnp-session-currentp (cdr sessions) peer session mru))))

(defun fn-bpnp-find-session (sessions peer session)
  (declare (xargs :guard t :measure (acl2-count sessions)))
  (if (atom sessions) nil
    (if (and (equal (fn-bpn-nth 1 (car sessions)) peer)
             (equal (fn-bpn-nth 2 (car sessions)) session))
        (car sessions)
      (fn-bpnp-find-session (cdr sessions) peer session))))

; A cheap host scheduling projection.  The session event remains the sole
; authority to select a row and build its exact forwarding image.
(defun fn-bpnp-has-forward-pendingp (held peer)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) nil
    (or (and (equal (fn-bpn-nth 12 (car held)) '(:forward-pending))
             (equal (fn-bpn-nth 11 (car held)) peer)
             (null (fn-bpn-nth 14 (car held))))
        (fn-bpnp-has-forward-pendingp (cdr held) peer))))

; The sender's reading of one TCPCL transfer (RFC 9174 5.2.4).  OBSERVED is
; the connection's outcome word; REASON is the Reason Code of the peer's
; XFER_REFUSE for this transfer, or nil when no XFER_REFUSE arrived.  A peer
; refusal keeps its reason in the kind-9 result: Completed (1) says the peer
; already holds the complete bundle, and fn-bpnp-forward-terminalp settles it
; exactly as :sent; every other reason is a distinct non-terminal result.  A
; refusal with no peer reason (the session machine declined to start the
; transfer) is :failed.  Neither is the application's retention receipt.
; Any other reading (the connection failed or closed after the durable
; kind 8, before an XFER_ACK or XFER_REFUSE) is :uncertain: the peer may or
; may not hold the bundle.  It is a connection-local fault: its kind 9 keeps
; the attempt slot (fn-bpnp-forward-result-slot) and the row is retried by
; the same identity on a later session under the retry bound, without
; stopping the node.  Only an uncertain publication fences the machine.
(defun fn-bpnp-tcpcl-outcome (observed reason)
  (declare (xargs :guard t))
  (cond ((equal observed :accepted) :sent)
        ((and (equal observed :refused) (fn-frame-natp reason))
         (list :refused reason))
        ((and (equal observed :refused) (null reason)) :failed)
        (t :uncertain)))

(defun fn-bpnp-wait-for (key waits)
  (declare (xargs :guard t :measure (acl2-count waits)))
  (if (atom waits) nil
    (if (equal key (fn-bpn-nth 1 (car waits)))
        (car waits)
      (fn-bpnp-wait-for key (cdr waits)))))

(defun fn-bpnp-remove-wait (key waits)
  (declare (xargs :guard t :measure (acl2-count waits)))
  (if (atom waits) nil
    (if (equal key (fn-bpn-nth 1 (car waits)))
        (fn-bpnp-remove-wait key (cdr waits))
      (cons (car waits) (fn-bpnp-remove-wait key (cdr waits))))))

(defun fn-bpnp-prune-waits (waits held)
  (declare (xargs :guard t :measure (acl2-count waits)))
  (if (atom waits) nil
    (let* ((row (car waits))
           (key (fn-bpn-nth 1 row)))
      (if (fn-bpnf-find-held key held)
          (cons row (fn-bpnp-prune-waits (cdr waits) held))
        (fn-bpnp-prune-waits (cdr waits) held)))))

(defun fn-bpnp-wait-key (h)
  (declare (xargs :guard t))
  (fn-bpnf-held-key (fn-bpnf-held-principal h) (fn-bpnf-held-id h)))

; These projections read only fixed record slots admitted at reception or
; reconstructed by bounded cold replay.  In particular they never re-encode
; a retained wire image during a served progress scan.
(defun fn-bpnp-primary (h)
  (declare (xargs :guard t))
  (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))

(defun fn-bpnp-payload (h)
  (declare (xargs :guard t))
  (fn-bpb-block-data
   (fn-bpb-bundle-payload (fn-bpnf-held-bundle h))))

(defun fn-bpnp-held-expiry (h observation)
  (declare (xargs :guard t))
  (if (not (fn-clock-observationp observation)) :uncertain
    (let* ((primary (fn-bpnp-primary h))
           (anchor (fn-bpn-nth 9 h)))
      (if (not (true-listp primary)) :uncertain
        (let ((creation (fn-bpp-creation-time primary))
              (lifetime (fn-bpp-lifetime primary)))
      (if (not (and (fn-clock-timep creation)
                    (fn-clock-timep lifetime)))
          :uncertain
        (cond
         ((equal anchor '(:wall))
          (fn-clock-expiry-decision creation lifetime nil observation))
         ((and (true-listp anchor) (equal (len anchor) 3)
               (equal (car anchor) :observed-age)
               (fn-clock-timep (cadr anchor))
               (fn-clock-timep (caddr anchor))
               (fn-clock-age-anchorp
                (cons (cadr anchor) (caddr anchor))))
          (fn-clock-expiry-decision
           creation lifetime (cons (cadr anchor) (caddr anchor))
           observation))
         (t :uncertain))))))))

(defun fn-bpnp-local-class (h)
  (declare (xargs :guard t))
  (let ((result (fn-bpa-decode-exact (fn-bpnp-payload h))))
    (if (fn-bpa-result-okp result)
        (let ((message (fn-bpa-result-message result)))
          (cond ((fn-bpa-requestp message) :request)
                ((fn-bpa-receiptp message) :receipt)
                (t :unsupported)))
      :unsupported)))

(defun fn-bpnp-live-pendingp (h node observation)
  (declare (xargs :guard t) (ignore node))
  (and (equal (fn-bpn-nth 0 h) :bpnf-held)
       (natp (fn-bpn-nth 3 h))
       (equal (fn-bpn-nth 12 h) '(:dispatch-pending))
       (null (fn-bpn-nth 10 h))
       (null (fn-bpn-nth 14 h))
       (equal (fn-bpnp-held-expiry h observation) :live)
       (let* ((primary (fn-bpnp-primary h))
              (flags (fn-bpn-nth 1 primary)))
         (and (natp flags)
              (not (fn-bpp-fragmentp flags))))))

(defun fn-bpnp-blockedp (h node routes generation waits)
  (declare (xargs :guard t))
  (let* ((key (fn-bpnp-wait-key h))
         (wait (fn-bpnp-wait-for key waits))
         (primary (fn-bpnp-primary h))
         (destination (fn-bpn-nth 3 primary))
         (route (fn-bpnp-route-peer destination routes)))
    (and (equal (fn-bpn-nth 0 wait) :bpnp-wait)
         (equal (fn-bpn-nth 3 wait) generation)
         (if (equal destination node)
             (equal (fn-bpn-nth 2 wait) :class)
           (if route (equal (fn-bpn-nth 2 wait) :session)
             (equal (fn-bpn-nth 2 wait) :route))))))

(defun fn-bpnp-credit-blockedp (h waits free)
  (declare (xargs :guard t))
  (let ((wait (fn-bpnp-wait-for (fn-bpnp-wait-key h) waits)))
    (and (equal (fn-bpn-nth 0 wait) :bpnp-wait)
         (equal (fn-bpn-nth 2 wait) :credit)
         (rationalp free)
         (integerp (fn-bpn-nth 3 wait))
         (<= free (fn-bpn-nth 3 wait)))))

; BP-R17 (spec 4.2, the (:after m) wait).  A delivery the application
; answered :busy leaves the row held and :dispatch-pending with the volatile
; wait (:bpnp-wait key :busy n m): n busy answers so far, m the monotonic
; reading before which class 3 does not offer it again.  At n equal to the
; kind-8 retry bound the row is stranded: still held, never refused, and
; not offered again until recovery clears the volatile wait.
(defconst *fn-bpnp-owner-backoff* 5000)

(defun fn-bpnp-busy-count (key waits)
  (declare (xargs :guard t))
  (let ((wait (fn-bpnp-wait-for key waits)))
    (if (and (equal (fn-bpn-nth 0 wait) :bpnp-wait)
             (equal (fn-bpn-nth 2 wait) :busy))
        (nfix (fn-bpn-nth 3 wait))
      0)))

(defun fn-bpnp-busy-blockedp (h waits observation)
  (declare (xargs :guard t))
  (let ((wait (fn-bpnp-wait-for (fn-bpnp-wait-key h) waits)))
    (and (equal (fn-bpn-nth 0 wait) :bpnp-wait)
         (equal (fn-bpn-nth 2 wait) :busy)
         (or (<= *fn-bpnp-max-forward-retries* (nfix (fn-bpn-nth 3 wait)))
             (not (fn-clock-observationp observation))
             (< (nfix (fn-clock-monotonic observation))
                (nfix (fn-bpn-nth 4 wait)))))))

(defun fn-bpnp-oldest-eligible-with-credit
  (held node observation routes generation waits free selected)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) selected
    (let* ((h (car held))
           (selected
            (if (and (fn-bpnp-live-pendingp h node observation)
                     (not (fn-bpnp-blockedp
                           h node routes generation waits))
                     (not (fn-bpnp-credit-blockedp h waits free))
                     (not (fn-bpnp-busy-blockedp h waits observation))
                     (or (null selected)
                         (< (nfix (fn-bpn-nth 3 h))
                            (nfix (fn-bpn-nth 3 selected)))))
                h selected)))
      (fn-bpnp-oldest-eligible-with-credit
       (cdr held) node observation routes generation waits free selected))))

(defun fn-bpnp-oldest-eligible
  (held node observation routes generation waits selected)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) selected
    (let* ((h (car held))
           (selected
            (if (and (fn-bpnp-live-pendingp h node observation)
                     (not (fn-bpnp-blockedp
                           h node routes generation waits))
                     (or (null selected)
                         (< (nfix (fn-bpn-nth 3 h))
                            (nfix (fn-bpn-nth 3 selected)))))
                h selected)))
      (fn-bpnp-oldest-eligible
       (cdr held) node observation routes generation waits selected))))

(defun fn-bpnp-oldest-uncertain-local
  (held node observation generation waits selected)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) selected
    (let* ((h (car held))
           (primary (fn-bpnp-primary h))
           (flags (fn-bpn-nth 1 primary))
           (selected
            (if (and (equal (fn-bpn-nth 0 h) :bpnf-held)
                     (natp (fn-bpn-nth 3 h))
                     (equal (fn-bpn-nth 12 h) '(:dispatch-pending))
                     (null (fn-bpn-nth 10 h))
                     (null (fn-bpn-nth 14 h))
                     (natp flags)
                     (not (fn-bpp-fragmentp flags))
                     (equal (fn-bpn-nth 3 primary) node)
                     (not (fn-bpnp-blockedp h node nil generation waits))
                     (not (fn-bpnp-busy-blockedp h waits observation))
                     (equal (fn-bpnp-held-expiry h observation) :uncertain)
                     (or (null selected)
                         (< (nfix (fn-bpn-nth 3 h))
                            (nfix (fn-bpn-nth 3 selected)))))
                h selected)))
      (fn-bpnp-oldest-uncertain-local
       (cdr held) node observation generation waits selected))))

(defun fn-bpnp-delivery-view (held)
  (declare (xargs :guard t))
  (let ((primary (fn-bpnp-primary held)))
    (if (not (fn-bpp-blockp primary)) nil
      (list :delivery (fn-bpnp-wait-key held)
            (fn-bpnp-local-class held) (fn-bpnp-payload held)
            (fn-bpn-nth 4 held)
            (fn-bpp-primary-identity primary)
            (fn-bpaj-eid-text (fn-bpp-source primary))
            (fn-bpaj-eid-text (fn-bpp-destination primary))))))

; Each result is computed from the single issued row, not from a served
; fold over the held list.  NIL means that no justified local delta exists.
(defun fn-bpnp-issued-debt-delta (st node)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st))
                  :verify-guards nil))
  (let* ((issued (fn-bpnf-issued st))
         (kind (fn-bpn-nth 3 issued))
         (record (fn-bpn-nth 4 issued)))
    (cond
     ((equal kind :store)
      (fn-bpnd-held-debt record node))
     ((equal kind :deliver)
      (let* ((before (fn-bpnf-find-arrival
                      (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))
             (status (fn-bpn-nth 5 record))
             (handoff
              (if (member-equal status
                                '(:request-accepted :request-duplicate
                                  :request-returned))
                  (fn-bpnf-handoff
                   (fn-bpn-nth 6 record) (fn-bpnp-wait-key before) :owed)
                nil)))
        (if (and before (fn-bpah-delivery-matches-heldp record before))
            (fn-bpnd-held-handoff-delta
             before (fn-bpah-delivered-held before record) handoff node)
          nil)))
     ((equal kind :family)
      (let* ((applied (fn-bpnf-family-apply-at
                       st record (fn-bpn-nth 4 record))))
        (if (equal (car applied) :ready)
            (fn-bpnd-family-delta
             (fn-bpn-nth 3 applied) (fn-bpn-nth 2 applied) node)
          nil)))
     ((equal kind :dispatch)
      (let* ((before (fn-bpnf-find-arrival
                      (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))
             (applied (fn-bpnp-dispatch-apply
                       record (fn-bpnf-held-list st))))
        (if (and before (equal (car applied) :ready))
            (fn-bpnd-held-delta before (fn-bpn-nth 2 applied) node)
          nil)))
     ((equal kind :delete)
      (let* ((row (fn-bpn-nth 0 record))
             (before (fn-bpnf-find-arrival
                      (fn-bpn-nth 3 row) (fn-bpnf-held-list st))))
        (if before
            (fn-bpnd-held-delta
             before (fn-bpn-report-tombstone-held before row) node)
          nil)))
     (t nil))))

(defun fn-bpnp-received-publicationp (issued effects)
  (declare (xargs :guard t))
  (let ((kind (fn-bpn-nth 3 issued))
        (effect (fn-bpn-nth 0 effects)))
    (or (and (equal kind :store)
             (equal (fn-bpn-nth 0 effect) :receive-answer)
             (equal (fn-bpn-nth 2 effect) :stored))
        (and (equal kind :deliver)
             (equal effect '(:delivery-answer :durable)))
        (and (equal kind :family)
             (equal (fn-bpn-nth 0 effect) :family-ready))
        (and (equal kind :delete)
             (equal (fn-bpn-nth 0 effect) :delete-ready)))))

(defun fn-bpnp-credit-refusal (st event kind)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (or (not (equal (fn-cbor-ag-car event) :base))
                                  (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                              (or (not (equal (fn-cbor-ag-car event)
                                              :recover-fnbs))
                                  (and (true-listp (fn-bpn-nth 2 event))
                                       (<= (len (fn-bpn-nth 2 event))
                                           *fn-bpn-machine-max-records*))))
                  :verify-guards nil))
  (cond
   ((equal kind :store)
    (fn-bpnf-answer
     st (list (list :receive-answer (fn-bpn-nth 3 event)
                    '(:refused :capacity)))))
   ((equal kind :family)
    (fn-bpnf-answer st (list (list :family-answer :refused))))
   ((equal kind :deliver)
    ; The app decision may already be durable in FNRJ.  Preserve its
    ; recovery-only fence rather than reporting a definitive refusal.
    (fn-bpn-report-author-step
     st (list :deliver-result (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
              (fn-bpn-nth 3 event) :uncertain '(0))))
   ((equal kind :delete)
    (fn-bpnf-answer st (list (list :delete-answer :refused))))
   (t (fn-bpnf-answer st nil))))

(defun fn-bpnp-credit-proposal-kind (effect issued)
  (declare (xargs :guard t))
  (let ((tag (fn-bpn-nth 0 effect))
        (kind (fn-bpn-nth 3 issued)))
    (if (or (and (equal tag :persist) (equal kind :store))
            (and (equal tag :persist-delivery) (equal kind :deliver))
            (and (equal tag :persist-family) (equal kind :family))
            (and (equal tag :persist-delete) (equal kind :delete)))
        kind nil)))

(defun fn-bpnp-publication-fault-effect (issued)
  (declare (xargs :guard t))
  (let ((kind (fn-bpn-nth 3 issued)))
    (cond
     ((equal kind :store)
      (list :receive-answer (fn-bpn-nth 4 (fn-bpn-nth 4 issued))
            '(:uncertain :debt-correlation)))
     ((equal kind :deliver) (list :delivery-answer :uncertain))
     ((equal kind :family) (list :family-answer :uncertain))
     ((equal kind :delete) (list :delete-answer :uncertain))
     (t (list :dispatch-answer :uncertain)))))

(defun fn-bpnp-transit-dispatch-step (st h peer node)
  (declare (xargs :guard t))
  (let* ((record (fn-bpnp-dispatch-record
                  (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                  (fn-bpn-nth 3 h) (fn-bpah-held-primary-identity h) peer))
         (applied (fn-bpnp-dispatch-apply record (fn-bpnf-held-list st)))
         (delta (if (equal (car applied) :ready)
                    (fn-bpnd-held-delta h (fn-bpn-nth 2 applied) node)
                  0)))
    (if (not (and (fn-frame-natp (fn-bpnf-epoch st))
                  (fn-frame-natp (fn-bpnf-next-op st))
                  (< (fn-bpnf-next-op st) *fn-frame-max-nat*)
                  (equal (car applied) :ready)
                  (fn-bpnp-dispatch-recordp record)
                  (not (equal (fn-bpnp-dispatch-frame record) :bad))))
        (fn-bpnf-answer st nil)
      (if (not (fn-bpnd-admitp
                (fn-bpnp-used st) (fn-bpnp-debt st)
                *fn-bpnp-control-margin* delta
                (if (< delta 0) :pay :spend)))
          (let* ((key (fn-bpnp-wait-key h))
                 (free (fn-bpnd-free
                        (fn-bpnp-used st) (fn-bpnp-debt st)
                        *fn-bpnp-control-margin*))
                 (waits (cons (list :bpnp-wait key :credit free)
                              (fn-bpnp-remove-wait key (fn-bpnp-waits st)))))
            (fn-bpnf-answer
             (fn-bpnp-with-waits st waits)
             (list (list :progress-wait key :credit free))))
        (fn-bpnf-answer
         (fn-bpnf-state-with-arrival
          (fn-bpnf-base st) (fn-bpnf-held-list st)
          (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
          (fn-bpnf-correlation st)
          (fn-bpnf-operation (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                             :dispatch record :pending)
          (fn-bpnf-waits st) (fn-bpnf-epoch st)
          (1+ (fn-bpnf-next-op st)) (fn-bpnf-next-arrival st))
         (list (list :persist-dispatch (fn-bpnf-epoch st)
                     (fn-bpnf-next-op st) record)))))))

(defun fn-bpnp-progress-step (st node observation routes generation)
  (declare (xargs :guard t))
  (if (or (fn-bpnf-issued st) (fn-bpnf-waits st)
          (fn-bpn-machine-state-fenced (fn-bpnf-base st))
          (not (and (fn-bpp-eidp node)
                    (fn-clock-observationp observation)
                    (fn-bpnp-routesp routes)
                    (<= (len routes) *fn-bpnp-max-routes*)
                    (fn-frame-natp generation))))
      (fn-bpnf-answer st nil)
    (let* ((waits (fn-bpnp-prune-waits
                   (fn-bpnp-waits st) (fn-bpnf-held-list st)))
           (st (fn-bpnp-with-waits st waits))
           (h (fn-bpnp-oldest-eligible-with-credit
               (fn-bpnf-held-list st) node observation routes generation
               waits
               (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st)
                             *fn-bpnp-control-margin*)
               nil)))
      (if (not h)
          (let ((uncertain
                 (fn-bpnp-oldest-uncertain-local
                  (fn-bpnf-held-list st) node observation
                  generation waits nil)))
            (if uncertain
                (if (member-equal (fn-bpnp-local-class uncertain)
                                  '(:request :receipt))
                    (fn-bpnf-answer
                     st (list (list :progress-uncertain
                                    (fn-bpnp-wait-key uncertain))))
                  (let* ((key (fn-bpnp-wait-key uncertain))
                         (new-waits
                          (cons (list :bpnp-wait key :class generation)
                                (fn-bpnp-remove-wait key waits))))
                    (fn-bpnf-answer
                     (fn-bpnp-with-waits st new-waits)
                     (list (list :progress-unsupported key)))))
              (fn-bpnf-answer st nil)))
        (let* ((key (fn-bpnp-wait-key h))
               (primary (fn-bpnp-primary h))
               (destination (fn-bpn-nth 3 primary)))
          (if (equal destination node)
              (if (member-equal (fn-bpnp-local-class h)
                                '(:request :receipt))
                  (let ((answer (fn-bpah-deliver-step st key node)))
                    (fn-bpnf-answer
                     (fn-bpnp-with-waits (fn-bpnf-answer-state answer) waits)
                     (fn-bpnf-answer-effects answer)))
                (let ((new-waits
                       (cons (list :bpnp-wait key :class generation)
                             (fn-bpnp-remove-wait key waits))))
                  (fn-bpnf-answer
                   (fn-bpnp-with-waits st new-waits)
                   (list (list :progress-unsupported key)))))
            (let ((peer (fn-bpnp-route-peer destination routes)))
              (if peer
                  (fn-bpnp-transit-dispatch-step st h peer node)
                (let ((new-waits
                       (cons (list :bpnp-wait key :route generation)
                             (fn-bpnp-remove-wait key waits))))
                  (fn-bpnf-answer
                   (fn-bpnp-with-waits st new-waits)
                   (list (list :progress-wait key :route generation))))))))))))

(defun fn-bpnp-dispatch-persist-step (st epoch op result)
  (declare (xargs :guard t))
  (let* ((issued (fn-bpnf-issued st))
         (record (fn-bpn-nth 4 issued))
         (arrival (fn-bpn-nth 3 record))
         (before (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st))))
    (if (not (and (fn-bpnf-operation-matchp issued epoch op)
                  (equal (fn-bpn-nth 3 issued) :dispatch)
                  (equal (fn-bpn-nth 5 issued) :pending)))
        (fn-bpnf-answer st nil)
      (if (equal result :durable)
          (let ((applied (fn-bpnp-dispatch-apply
                          record (fn-bpnf-held-list st))))
            (if (not (equal (car applied) :ready))
                (fn-bpnf-answer
                 (fn-bpnp-with-credit
                  (fn-bpnf-with-issued
                   st (fn-bpnf-operation epoch op :dispatch record :uncertain))
                  (fn-bpnp-used st) (fn-bpnp-debt st))
                 (list (list :dispatch-answer :uncertain)))
              (let* ((node
                      (fn-bpn-config-node-id
                       (fn-bpn-machine-state-config (fn-bpnf-base st))))
                     (delta (fn-bpnd-held-delta
                             before (fn-bpn-nth 2 applied) node))
                     (settled
                      (fn-bpnf-state-with-arrival
                       (fn-bpnf-base st) (fn-bpn-nth 1 applied)
                       (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
                       (fn-bpnf-correlation st) nil (fn-bpnf-waits st)
                       (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                       (fn-bpnf-next-arrival st))))
                (fn-bpnf-answer
                 (fn-bpnp-with-credit
                  settled (1+ (nfix (fn-bpnp-used st)))
                  (+ (nfix (fn-bpnp-debt st)) delta))
                 (list (list :dispatch-ready
                             (fn-bpnp-wait-key (fn-bpn-nth 2 applied))
                             (fn-bpn-nth 5 record)))))))
        (if (equal result :refused)
            (fn-bpnf-answer
             (fn-bpnp-with-credit
              (fn-bpnf-with-issued st nil)
              (fn-bpnp-used st) (fn-bpnp-debt st))
             (list (list :dispatch-answer :refused)))
          (fn-bpnf-answer
           (fn-bpnp-with-credit
            (fn-bpnf-with-issued
             st (fn-bpnf-operation epoch op :dispatch record :uncertain))
            (fn-bpnp-used st) (fn-bpnp-debt st))
           (list (list :dispatch-answer :uncertain))))))))

; Scan in arrival order.  A failed MRU comparison records a per-key volatile
; wait and continues to younger rows in this same bounded event (N04).
(defun fn-bpnp-forward-mru-waitp (h peer mru waits)
  (declare (xargs :guard t))
  (let ((wait (fn-bpnp-wait-for (fn-bpnp-wait-key h) waits)))
    (and (equal (fn-bpn-nth 0 wait) :bpnp-wait)
         (equal (fn-bpn-nth 2 wait) :mru)
         (equal (fn-bpn-nth 3 wait) peer)
         (equal (fn-bpn-nth 4 wait) mru))))

; A row with no attempt, or with an attempt left by an earlier process epoch
; under the retry bound (bp-forward-attempt.lisp), is offered by the same
; arrival-order scan: a retry takes no precedence and no separate path.
(defun fn-bpnp-forward-candidatep (h peer observation epoch)
  (declare (xargs :guard t))
  (and (equal (fn-bpn-nth 0 h) :bpnf-held)
       (natp (fn-bpn-nth 3 h))
       (equal (fn-bpn-nth 11 h) peer)
       (equal (fn-bpn-nth 12 h) '(:forward-pending))
       (or (null (fn-bpn-nth 13 h))
           (fn-bpnp-retry-eligible-slotp (fn-bpn-nth 13 h) epoch peer))
       (null (fn-bpn-nth 14 h))
       (equal (fn-bpnp-held-expiry h observation) :live)))

; The oldest held row to this peer whose uncertain attempt reached the retry
; bound: reported on a session that offers nothing, never dropped.
(defun fn-bpnp-first-stranded (ordered peer epoch)
  (declare (xargs :guard t :measure (acl2-count ordered)))
  (if (atom ordered) nil
    (let ((h (car ordered)))
      (if (and (equal (fn-bpn-nth 0 h) :bpnf-held)
               (equal (fn-bpn-nth 12 h) '(:forward-pending))
               (null (fn-bpn-nth 14 h))
               (fn-bpnp-stranded-slotp (fn-bpn-nth 13 h) epoch peer))
          h
        (fn-bpnp-first-stranded (cdr ordered) peer epoch)))))

(defun fn-bpnp-stranded-effects (held peer epoch)
  (declare (xargs :guard (true-listp held)))
  (let ((stranded (fn-bpnp-first-stranded (reverse held) peer epoch)))
    (and stranded
         (list (list :forward-stranded (fn-bpn-nth 3 stranded) peer
                     (fn-bpnp-attempt-retries (fn-bpn-nth 13 stranded)))))))

(defun fn-bpnp-forward-scan
  (ordered peer mru node observation waits free epoch)
  (declare (xargs :guard (natp mru) :measure (acl2-count ordered)))
  (if (atom ordered) (list :none waits)
    (let* ((h (car ordered))
           (key (fn-bpnp-wait-key h)))
      (if (or (not (fn-bpnp-forward-candidatep h peer observation epoch))
              (fn-bpnp-forward-mru-waitp h peer mru waits)
              (fn-bpnp-credit-blockedp h waits free))
          (fn-bpnp-forward-scan
           (cdr ordered) peer mru node observation waits free epoch)
        (let ((image (fn-bpnp-forward-image h node observation)))
          (if (not (equal (car image) :ready))
              (fn-bpnp-forward-scan
               (cdr ordered) peer mru node observation waits free epoch)
            (if (< mru (len (fn-bpn-nth 1 image)))
                (fn-bpnp-forward-scan
                 (cdr ordered) peer mru node observation
                 (cons (list :bpnp-wait key :mru peer mru)
                       (fn-bpnp-remove-wait key waits)) free epoch)
              (list :ready h (fn-bpn-nth 1 image)
                    (fn-bpb-bundle-age (fn-bpn-nth 2 image))
                    waits))))))))

(defun fn-bpnp-start-one (st peer session mru observation)
  (declare (xargs :guard (and (natp mru)
                              (true-listp (fn-bpnf-held-list st)))
                  :verify-guards nil))
  (if (not (and (fn-bpnp-session-currentp
                (fn-bpnp-sessions st) peer session mru)
                (null (fn-bpnf-issued st))
                (null (fn-bpnf-waits st))
                (not (fn-bpn-machine-state-fenced (fn-bpnf-base st)))))
      (fn-bpnf-answer st nil)
    (let* ((node (fn-bpn-config-node-id
                  (fn-bpn-machine-state-config (fn-bpnf-base st))))
           (free (fn-bpnd-free (fn-bpnp-used st) (fn-bpnp-debt st)
                               *fn-bpnp-control-margin*))
           (scan (fn-bpnp-forward-scan
                  (reverse (fn-bpnf-held-list st)) peer mru node observation
                  (fn-bpnp-waits st) free (fn-bpnf-epoch st)))
           (waits (if (equal (car scan) :ready)
                      (fn-bpn-nth 4 scan) (fn-bpn-nth 1 scan)))
           (held (fn-bpnf-held-list st))
           (epoch (fn-bpnf-epoch st))
           (st (fn-bpnp-with-waits st waits)))
      (if (not (equal (car scan) :ready))
          (fn-bpnf-answer
           st (fn-bpnp-stranded-effects held peer epoch))
        (let* ((h (fn-bpn-nth 1 scan))
               (wire (fn-bpn-nth 2 scan))
               (age (fn-bpn-nth 3 scan))
               (record (fn-bpnp-forward-attempt-record
                        (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                        (fn-bpn-nth 3 h)
                        (fn-bpah-held-primary-identity h)
                        peer session age))
               (applied (fn-bpnp-attempt-apply
                         record (fn-bpnf-held-list st)))
               (delta (if (equal (car applied) :ready)
                          (fn-bpnd-held-delta
                           h (fn-bpn-nth 2 applied) node) 0)))
          (if (not (and (fn-frame-natp (fn-bpnf-epoch st))
                        (fn-frame-natp (fn-bpnf-next-op st))
                        (< (fn-bpnf-next-op st) *fn-frame-max-nat*)
                        (equal (car applied) :ready)
                        (fn-bpnp-forward-attempt-recordp record)
                        (not (equal (fn-bpnp-attempt-frame record) :bad))))
              (fn-bpnf-answer st nil)
            (if (not (fn-bpnd-admitp
                      (fn-bpnp-used st) (fn-bpnp-debt st)
                      *fn-bpnp-control-margin* delta :spend))
                (let* ((key (fn-bpnp-wait-key h))
                       (new-waits
                        (cons (list :bpnp-wait key :credit free)
                              (fn-bpnp-remove-wait key waits))))
                  (fn-bpnf-answer
                   (fn-bpnp-with-waits st new-waits)
                   (list (list :progress-wait key :credit free))))
              (let ((issued
                     (fn-bpnf-state-with-arrival
                      (fn-bpnf-base st) (fn-bpnf-held-list st)
                      (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
                      (fn-bpnf-correlation st)
                      (fn-bpnf-operation
                       (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                       :attempt record :pending)
                      (fn-bpnf-waits st) (fn-bpnf-epoch st)
                      (1+ (fn-bpnf-next-op st))
                      (fn-bpnf-next-arrival st))))
                (fn-bpnf-answer
                 (fn-bpnp-with-runtime
                  (fn-bpnp-with-credit
                   (fn-bpnp-with-waits issued waits)
                   (fn-bpnp-used st) (fn-bpnp-debt st))
                  (fn-bpnp-sessions st)
                  (list (fn-bpnf-epoch st) (fn-bpnf-next-op st) wire))
                 (list (list :persist-attempt
                             (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                             record)))))))))))

(defun fn-bpnp-attempt-persist-step (st epoch op result)
  (declare (xargs :guard t))
  (let* ((issued (fn-bpnf-issued st))
         (record (fn-bpn-nth 4 issued))
         (pending (fn-bpnp-pending-image st)))
    (if (not (and (fn-bpnf-operation-matchp issued epoch op)
                  (equal (fn-bpn-nth 3 issued) :attempt)
                  (equal (fn-bpn-nth 5 issued) :pending)))
        (fn-bpnf-answer st nil)
      (if (equal result :durable)
          (let* ((before (fn-bpnf-find-arrival
                          (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))
                 (applied (fn-bpnp-attempt-apply
                           record (fn-bpnf-held-list st)))
                 (node (fn-bpn-config-node-id
                        (fn-bpn-machine-state-config (fn-bpnf-base st)))))
            (if (not (and (equal (car applied) :ready)
                          (equal (fn-bpn-nth 0 pending) epoch)
                          (equal (fn-bpn-nth 1 pending) op)
                          (fn-cbor-octet-listp (fn-bpn-nth 2 pending))
                          (consp (fn-bpn-nth 2 pending))))
                (fn-bpnf-answer
                 (fn-bpnp-with-issued
                  st (fn-bpnf-operation epoch op :attempt record :uncertain))
                 (list (list :forward-answer :uncertain)))
              (let* ((delta (fn-bpnd-held-delta
                             before (fn-bpn-nth 2 applied) node))
                     (settled
                      (fn-bpnf-state-with-arrival
                       (fn-bpnf-base st) (fn-bpn-nth 1 applied)
                       (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
                       (fn-bpnf-correlation st) nil (fn-bpnf-waits st)
                       (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                       (fn-bpnf-next-arrival st))))
                (fn-bpnf-answer
                 (fn-bpnp-with-runtime
                  (fn-bpnp-with-credit
                   (fn-bpnp-with-waits settled (fn-bpnp-waits st))
                   (1+ (nfix (fn-bpnp-used st)))
                   (+ (nfix (fn-bpnp-debt st)) delta))
                  (fn-bpnp-sessions st) nil)
                 (list (list :cl-send
                             (fn-bpn-nth 5 record) (fn-bpn-nth 6 record)
                             epoch op (fn-bpnp-wait-key (fn-bpn-nth 2 applied))
                             (fn-bpn-nth 2 pending)))))))
        (if (equal result :refused)
            (fn-bpnf-answer
             (fn-bpnp-with-runtime
              (fn-bpnp-with-issued st nil) (fn-bpnp-sessions st) nil)
             (list (list :forward-answer :refused)))
          (fn-bpnf-answer
           (fn-bpnp-with-runtime
            (fn-bpnp-with-issued
             st (fn-bpnf-operation epoch op :attempt record :uncertain))
            (fn-bpnp-sessions st) nil)
           (list (list :forward-answer :uncertain))))))))

(defun fn-bpnp-find-attempt (held attempt-epoch attempt-op session)
  (declare (xargs :guard t :measure (acl2-count held)))
  (if (atom held) nil
    (let ((attempt (fn-bpn-nth 13 (car held))))
      (if (and (equal (fn-bpn-nth 0 attempt) :forwarding)
               (equal (fn-bpn-nth 1 attempt) attempt-epoch)
               (equal (fn-bpn-nth 2 attempt) attempt-op)
               (equal (fn-bpn-nth 4 attempt) session))
          (car held)
        (fn-bpnp-find-attempt
         (cdr held) attempt-epoch attempt-op session)))))

(defun fn-bpnp-forward-result-propose-step
  (st attempt-epoch attempt-op session outcome observation)
  (declare (xargs :guard t) (ignore observation))
  (let* ((h (fn-bpnp-find-attempt
             (fn-bpnf-held-list st) attempt-epoch attempt-op session))
         (record (and h
                      (fn-bpnp-forward-result-record
                       (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                       (fn-bpn-nth 3 h)
                       (fn-bpah-held-primary-identity h)
                       attempt-epoch attempt-op session outcome)))
         (applied (and record
                       (fn-bpnp-forward-result-apply
                        record (fn-bpnf-held-list st)))))
    (if (not h)
        (fn-bpnf-answer st
                         (list (list :forward-stale attempt-epoch
                                     attempt-op session)))
      (let* ((node (fn-bpn-config-node-id
                    (fn-bpn-machine-state-config (fn-bpnf-base st))))
             (delta (and (equal (car applied) :ready)
                         (fn-bpnd-held-delta
                          h (fn-bpn-nth 2 applied) node))))
        (if (not (and (null (fn-bpnf-issued st))
                      (null (fn-bpnf-waits st))
                      (fn-bpnp-transfer-outcomep outcome)
                      (fn-frame-natp (fn-bpnf-epoch st))
                      (fn-frame-natp (fn-bpnf-next-op st))
                      (< (fn-bpnf-next-op st) *fn-frame-max-nat*)
                      (equal (car applied) :ready)
                      (integerp delta)
                      (not (equal (fn-bpnp-result-frame record) :bad))
                      (fn-bpnd-admitp
                       (fn-bpnp-used st) (fn-bpnp-debt st)
                       *fn-bpnp-control-margin* delta :pay)))
            (fn-bpnf-answer st (list (list :forward-answer :uncertain)))
          (fn-bpnf-answer
           (fn-bpnp-with-runtime
            (fn-bpnp-with-credit
             (fn-bpnf-state-with-arrival
              (fn-bpnf-base st) (fn-bpnf-held-list st)
              (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
              (fn-bpnf-correlation st)
              (fn-bpnf-operation
               (fn-bpnf-epoch st) (fn-bpnf-next-op st)
               :forward-result record :pending)
              (fn-bpnf-waits st) (fn-bpnf-epoch st)
              (1+ (fn-bpnf-next-op st)) (fn-bpnf-next-arrival st))
             (fn-bpnp-used st) (fn-bpnp-debt st))
            (fn-bpnp-sessions st) nil)
           (list (list :persist-forward-result
                       (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                       record))))))))

(defun fn-bpnp-forward-result-persist-step (st epoch op result)
  (declare (xargs :guard t))
  (let* ((issued (fn-bpnf-issued st))
         (record (fn-bpn-nth 4 issued)))
    (if (not (and (fn-bpnf-operation-matchp issued epoch op)
                  (equal (fn-bpn-nth 3 issued) :forward-result)
                  (equal (fn-bpn-nth 5 issued) :pending)))
        (fn-bpnf-answer st nil)
      (if (equal result :durable)
          (let* ((before (fn-bpnf-find-arrival
                          (fn-bpn-nth 3 record) (fn-bpnf-held-list st)))
                 (applied (fn-bpnp-forward-result-apply
                           record (fn-bpnf-held-list st)))
                 (node (fn-bpn-config-node-id
                        (fn-bpn-machine-state-config (fn-bpnf-base st)))))
            (if (not (equal (car applied) :ready))
                (fn-bpnf-answer
                 (fn-bpnp-with-issued
                  st (fn-bpnf-operation
                      epoch op :forward-result record :uncertain))
                 (list (list :forward-answer :uncertain)))
              (let* ((delta (fn-bpnd-held-delta
                             before (fn-bpn-nth 2 applied) node))
                     (settled
                      (fn-bpnf-state-with-arrival
                       (fn-bpnf-base st) (fn-bpn-nth 1 applied)
                       (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
                       (fn-bpnf-correlation st) nil (fn-bpnf-waits st)
                       (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                       (fn-bpnf-next-arrival st))))
                (fn-bpnf-answer
                 (fn-bpnp-with-runtime
                  (fn-bpnp-with-credit
                   (fn-bpnp-with-waits settled (fn-bpnp-waits st))
                   (1+ (nfix (fn-bpnp-used st)))
                   (+ (nfix (fn-bpnp-debt st)) delta))
                  (fn-bpnp-sessions st) nil)
                 (list (list :forward-ready
                             (fn-bpn-nth 3 record)
                             (fn-bpn-nth 8 record)))))))
        (if (equal result :refused)
            (fn-bpnf-answer
             (fn-bpnp-with-issued st nil)
             (list (list :forward-answer :refused)))
          (fn-bpnf-answer
           (fn-bpnp-with-issued
            st (fn-bpnf-operation
                epoch op :forward-result record :uncertain))
           (list (list :forward-answer :uncertain))))))))

;; ---------------------------------------------------------------------
;; The operator's resume of a stranded row (spec bp-node-machine 4.3.1).
;;
;; `bp-node resume JOURNAL NODE-ID ARRIVAL' steps (:operator-resume ARRIVAL).
;; A row whose uncertain attempt reached the retry bound is re-armed by a
;; durable kind 9 with outcome :resumed naming that attempt: applying it
;; (fn-bpnp-forward-result-apply, which the :persist-result arm and ordered
;; replay both call) clears the slot, so the next session to the row's next
;; hop offers the unchanged held bundle again and the next kind 8 counts from
;; 0.  The kind-8 rows that exhausted the budget and the :resumed row stay in
;; FNBS: the history keeps the exhaustion and says an operator re-armed it.
;; Anything else is refused with its reason and nothing is written.
(defun fn-bpnp-resume-refusal (st arrival)
  (declare (xargs :guard t))
  (let* ((held (fn-bpnf-held-list st))
         (h (fn-bpnf-find-arrival arrival held))
         (slot (fn-bpn-nth 13 h)))
    (cond ((fn-bpn-machine-state-fenced (fn-bpnf-base st)) :fenced)
          ((not (and (null (fn-bpnf-issued st))
                     (null (fn-bpnf-waits st))))
           :busy)
          ((not (and (natp arrival)
                     (equal (fn-bpnf-arrival-count arrival held) 1)
                     (equal (fn-bpn-nth 0 h) :bpnf-held)))
           :no-row)
          ((not (and (equal (fn-bpn-nth 12 h) '(:forward-pending))
                     (null (fn-bpn-nth 14 h))))
           :not-forward-pending)
          ((null slot) :not-attempted)
          ((not (fn-bpnp-stranded-slotp slot (fn-bpnf-epoch st)
                                        (fn-bpn-nth 11 h)))
           :not-stranded)
          (t nil))))

(defun fn-bpnp-resume-record (st arrival)
  (declare (xargs :guard t))
  (let* ((h (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st)))
         (slot (fn-bpn-nth 13 h)))
    (fn-bpnp-forward-result-record
     (fn-bpnf-epoch st) (fn-bpnf-next-op st) arrival
     (fn-bpah-held-primary-identity h)
     (fn-bpn-nth 1 slot) (fn-bpn-nth 2 slot) (fn-bpn-nth 4 slot)
     :resumed)))

(defun fn-bpnp-operator-resume-step (st arrival)
  (declare (xargs :guard t))
  (let ((reason (fn-bpnp-resume-refusal st arrival)))
    (if reason
        (fn-bpnf-answer st (list (list :resume-refused arrival reason)))
      (let* ((h (fn-bpnf-find-arrival arrival (fn-bpnf-held-list st)))
             (record (fn-bpnp-resume-record st arrival))
             (applied (fn-bpnp-forward-result-apply
                       record (fn-bpnf-held-list st)))
             (node (fn-bpn-config-node-id
                    (fn-bpn-machine-state-config (fn-bpnf-base st))))
             (delta (and (equal (car applied) :ready)
                         (fn-bpnd-held-delta h (fn-bpn-nth 2 applied) node))))
        (if (not (and (fn-frame-natp (fn-bpnf-epoch st))
                      (fn-frame-natp (fn-bpnf-next-op st))
                      (< (fn-bpnf-next-op st) *fn-frame-max-nat*)
                      (equal (car applied) :ready)
                      (integerp delta)
                      (not (equal (fn-bpnp-result-frame record) :bad))
                      (fn-bpnd-admitp
                       (fn-bpnp-used st) (fn-bpnp-debt st)
                       *fn-bpnp-control-margin* delta
                       (if (< delta 0) :pay :control))))
            (fn-bpnf-answer
             st (list (list :resume-refused arrival :no-capacity)))
          (fn-bpnf-answer
           (fn-bpnp-with-runtime
            (fn-bpnp-with-credit
             (fn-bpnf-state-with-arrival
              (fn-bpnf-base st) (fn-bpnf-held-list st)
              (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
              (fn-bpnf-correlation st)
              (fn-bpnf-operation
               (fn-bpnf-epoch st) (fn-bpnf-next-op st)
               :forward-result record :pending)
              (fn-bpnf-waits st) (fn-bpnf-epoch st)
              (1+ (fn-bpnf-next-op st)) (fn-bpnf-next-arrival st))
             (fn-bpnp-used st) (fn-bpnp-debt st))
            (fn-bpnp-sessions st) nil)
           (list (list :persist-forward-result
                       (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                       record))))))))

;; ---------------------------------------------------------------------
;; The boot-domain gate on recovery (spec bp-node-machine 8, N07).
;;
;; A Bundle Age anchor (:observed-age age monotonic) is a reading of the
;; CLOCK_BOOTTIME origin of one boot.  A process lives inside one boot, so
;; the only event at which the boot can change under the machine is
;; recovery.  A seven-field recovery event carries, as its last field, the
;; boot-domain decision fn-bpnf-clock-domain-plan made from the durable
;; clock-domain record and this boot's observed boot ID.  Unless that
;; decision is :same (the durable domain is this boot) or :initialize with
;; nothing retained, the machine fences: it installs no replay, compares no
;; retained anchor, and every later event except another recovery is inert.
;; The six-field recovery event (no domain) keeps its old meaning.
(defun fn-bpnp-clock-domain-evidencep (plan)
  (declare (xargs :guard t))
  (and (consp plan) (true-listp plan)
       (if (member-equal (car plan) '(:same :initialize :fence)) t nil)))

(defun fn-bpnp-domain-recover-eventp (event)
  (declare (xargs :guard t))
  (and (equal (fn-cbor-ag-car event) :recover-fnbs)
       (true-listp event)
       (equal (len event) 7)))

(defun fn-bpnp-clock-domain-admitsp (event)
  (declare (xargs :guard t))
  (let ((plan (fn-bpn-nth 6 event)))
    (or (and (equal (fn-cbor-ag-car plan) :same)
             (consp (fn-bpn-nth 1 plan)))
        (and (equal (fn-cbor-ag-car plan) :initialize)
             (null (fn-bpn-nth 2 event))
             (equal (fn-bpn-nth 5 event) 0)))))

(defun fn-bpnp-clock-domain-reason (plan)
  (declare (xargs :guard t))
  (if (equal (fn-cbor-ag-car plan) :fence)
      (fn-bpn-nth 1 plan)
    :domain-evidence))

(defun fn-bpnp-clock-domain-fence (st plan)
  (declare (xargs :guard t))
  (fn-bpnf-answer
   (fn-bpnp-with-issued
    st (fn-bpnf-operation (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                          :clock-domain nil :uncertain))
   (list (list :restart-fault :clock-domain
               (fn-bpnp-clock-domain-reason plan)))))

;; ---------------------------------------------------------------------
;; The kind-14 conflict record (spec bp-node-machine 4.1 step 4, N11).
;;
;; The held row a valid :receive-bundle event conflicts with: the same
;; conditions under which fn-bpnf-step answers :identity-conflict.
(defun fn-bpnp-conflict-held (st event)
  (declare (xargs :guard t))
  (let ((bundle (fn-bpn-nth 1 event))
        (wire (fn-bpn-nth 2 event))
        (ingress (fn-bpn-nth 3 event)))
    (and (equal (fn-cbor-ag-car event) :receive-bundle)
         (true-listp event) (equal (len event) 5)
         (not (fn-bpnf-issued st))
         (not (fn-bpah-delivery-uncertainp st))
         (fn-frame-natp (fn-bpnf-epoch st))
         (fn-frame-natp (fn-bpnf-next-op st))
         (fn-frame-natp (fn-bpnf-next-arrival st))
         (not (equal (fn-bpnf-next-op st) *fn-frame-max-nat*))
         (fn-bpnf-cl-ingressp ingress)
         (fn-bpb-bundlep bundle)
         (fn-cbor-octet-listp wire)
         (fn-clock-observationp (fn-bpn-nth 4 event))
         (equal wire (fn-bpb-encode bundle))
         (equal (fn-bpnf-receive-decision (fn-bpnf-held-list st)
                                          ingress bundle)
                :identity-conflict)
         (fn-bpnf-find-held
          (fn-bpnf-held-key (fn-bpnf-ingress-principal ingress)
                            (fn-bpb-bundle-id bundle))
          (fn-bpnf-held-list st)))))

(defun fn-bpnp-with-next-issued (st issued)
  (declare (xargs :guard t))
  (fn-bpnp-with-runtime
   (fn-bpnp-with-credit
    (fn-bpnp-with-waits
     (fn-bpnf-state-with-arrival
      (fn-bpnf-base st) (fn-bpnf-held-list st)
      (fn-bpnf-outcomes st) (fn-bpnf-handoffs st)
      (fn-bpnf-correlation st) issued (fn-bpnf-waits st)
      (fn-bpnf-epoch st) (1+ (nfix (fn-bpnf-next-op st)))
      (fn-bpnf-next-arrival st))
     (fn-bpnp-waits st))
    (fn-bpnp-used st) (fn-bpnp-debt st))
   (fn-bpnp-sessions st) (fn-bpnp-pending-image st)))

(defun fn-bpnp-conflict-refusal (ingress)
  (declare (xargs :guard t))
  (list (list :receive-answer ingress :identity-conflict)))

; Within the journal's credit (a kind-14 final is one received final with
; zero debt) the machine proposes the record; otherwise it answers the
; refusal alone.  Either way the ingress gets a refusal and H is kept.
(defun fn-bpnp-conflict-propose-step (st event h)
  (declare (xargs :guard t))
  (let* ((ingress (fn-bpn-nth 3 event))
         (record (fn-bpnf-conflict-of (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                                      h ingress (fn-bpn-nth 2 event))))
    (if (and (fn-bpnf-conflict-recordp record)
             (not (equal (fn-bpnf-conflict-frame record) :bad))
             (fn-bpnd-admitp (fn-bpnp-used st) (fn-bpnp-debt st)
                             *fn-bpnp-control-margin* 0 :spend))
        (fn-bpnf-answer
         (fn-bpnp-with-next-issued
          st (fn-bpnf-operation (fn-bpnf-epoch st) (fn-bpnf-next-op st)
                                :conflict (list record ingress) :pending))
         (list (list :persist-conflict (fn-bpnf-epoch st)
                     (fn-bpnf-next-op st) record)))
      (fn-bpnf-answer st (fn-bpnp-conflict-refusal ingress)))))

; The publication's outcome never changes the answer to the offering
; ingress: its bundle is refused.  A durable record consumes one final of
; credit; an uncertain one fences the machine until recovery.
(defun fn-bpnp-conflict-persist-step (st epoch op result)
  (declare (xargs :guard t))
  (let* ((issued (fn-bpnf-issued st))
         (ingress (fn-bpn-nth 1 (fn-bpn-nth 4 issued))))
    (cond
     ((or (equal (fn-bpn-nth 5 issued) :uncertain)
          (not (fn-bpnf-operation-matchp issued epoch op)))
      (fn-bpnf-answer st nil))
     ((equal result :durable)
      (fn-bpnf-answer
       (fn-bpnp-with-waits
        (fn-bpnp-with-credit (fn-bpnp-with-issued st nil)
                             (1+ (nfix (fn-bpnp-used st))) (fn-bpnp-debt st))
        (fn-bpnp-waits st))
       (fn-bpnp-conflict-refusal ingress)))
     ((equal result :refused)
      (fn-bpnf-answer
       (fn-bpnp-with-waits (fn-bpnp-with-issued st nil) (fn-bpnp-waits st))
       (fn-bpnp-conflict-refusal ingress)))
     (t
      (fn-bpnf-answer
       (fn-bpnp-with-issued
        st (fn-bpnf-operation (fn-bpn-nth 1 issued) (fn-bpn-nth 2 issued)
                              :conflict (fn-bpn-nth 4 issued) :uncertain))
       (fn-bpnp-conflict-refusal ingress))))))

;; BP-R17.  (:deliver-result epoch op key :busy detail obs): the owner
;; answered the delivery named by the volatile marker (:delivery epoch op
;; key) busy.  Nothing is proposed and nothing is published: the marker is
;; cleared and the key's deferral wait is set; every other slot is kept.
(defun fn-bpnp-busy-eventp (event)
  (declare (xargs :guard t))
  (and (true-listp event) (equal (len event) 7)
       (equal (car event) :deliver-result)
       (fn-frame-natp (fn-bpn-nth 1 event))
       (fn-frame-natp (fn-bpn-nth 2 event))
       (true-listp (fn-bpn-nth 3 event))
       (equal (len (fn-bpn-nth 3 event)) 2)
       (equal (fn-bpn-nth 4 event) :busy)
       (fn-cbor-octet-listp (fn-bpn-nth 5 event))
       (<= (len (fn-bpn-nth 5 event)) 256)
       (fn-clock-observationp (fn-bpn-nth 6 event))))

(defun fn-bpnp-busy-wait (key waits observation)
  (declare (xargs :guard t))
  (list :bpnp-wait key :busy (1+ (fn-bpnp-busy-count key waits))
        (+ (nfix (fn-clock-monotonic observation)) *fn-bpnp-owner-backoff*)))

(defun fn-bpnp-busy-delivery-step (st epoch op key observation)
  (declare (xargs :guard t))
  (if (not (and (true-listp st)
                (equal (fn-bpnf-waits st) (list :delivery epoch op key))
                (equal (fn-bpnf-epoch st) epoch)
                (null (fn-bpnf-issued st))))
      (fn-bpnf-answer st (list (list :delivery-answer :refused)))
    (let* ((waits (fn-bpnp-waits st))
           (wait (fn-bpnp-busy-wait key waits observation))
           (n (fn-bpn-nth 3 wait)))
      (fn-bpnf-answer
       (update-nth 11 (cons wait (fn-bpnp-remove-wait key waits))
                   (update-nth 7 nil st))
       (list (if (<= *fn-bpnp-max-forward-retries* n)
                 (list :delivery-stranded key n)
               (list :delivery-deferred key n (fn-bpn-nth 4 wait))))))))

(defun fn-bpnp-host-eventp (event)
  (declare (xargs :guard t))
  (case (fn-cbor-ag-car event)
    (:progress
     (and (true-listp event) (equal (len event) 5)
          (fn-bpp-eidp (fn-bpn-nth 1 event))
          (fn-clock-observationp (fn-bpn-nth 2 event))
          (fn-bpnp-routesp (fn-bpn-nth 3 event))
          (<= (len (fn-bpn-nth 3 event)) *fn-bpnp-max-routes*)
          (fn-frame-natp (fn-bpn-nth 4 event))))
    (:session
     (and (true-listp event) (equal (len event) 6)
          (fn-bpp-eidp (fn-bpn-nth 1 event))
          (fn-bpnp-session-idp (fn-bpn-nth 2 event))
          (or (equal (fn-bpn-nth 3 event) t)
              (null (fn-bpn-nth 3 event)))
          (fn-frame-natp (fn-bpn-nth 4 event))
          (< 0 (fn-bpn-nth 4 event))
          (fn-clock-observationp (fn-bpn-nth 5 event))))
    (:resume
     (and (true-listp event) (equal (len event) 4)
          (fn-bpp-eidp (fn-bpn-nth 1 event))
          (fn-bpnp-session-idp (fn-bpn-nth 2 event))
          (fn-clock-observationp (fn-bpn-nth 3 event))))
    (:forward-result
     (and (true-listp event) (equal (len event) 6)
          (fn-frame-natp (fn-bpn-nth 1 event))
          (fn-frame-natp (fn-bpn-nth 2 event))
          (fn-bpnp-session-idp (fn-bpn-nth 3 event))
          (fn-bpnp-transfer-outcomep (fn-bpn-nth 4 event))
          (fn-clock-observationp (fn-bpn-nth 5 event))))
    (:deliver-result
     (or (fn-bpnf-host-eventp event)
         (fn-bpnp-busy-eventp event)))
    (:operator-resume
     (and (true-listp event) (equal (len event) 2)
          (fn-frame-natp (fn-bpn-nth 1 event))))
    (:recover-fnbs
     (or (fn-bpnf-host-eventp event)
         (and (true-listp event) (equal (len event) 7)
              (true-listp (fn-bpn-nth 2 event))
              (<= (len (fn-bpn-nth 2 event)) *fn-bpn-machine-max-records*)
              (natp (fn-bpn-nth 5 event))
              (<= (fn-bpn-nth 5 event) *fn-bpnf-received-max-records*)
              (fn-bpnp-clock-domain-evidencep (fn-bpn-nth 6 event)))))
    (otherwise (fn-bpnf-host-eventp event))))

(defun fn-bpnp-preserve-runtime-answer (answer st recovery)
  (declare (xargs :guard t))
  (fn-bpnf-answer
   (fn-bpnp-with-runtime
    (fn-bpnf-answer-state answer)
    (if recovery nil (fn-bpnp-sessions st))
    (if recovery nil (fn-bpnp-pending-image st)))
   (fn-bpnf-answer-effects answer)))

(defun fn-bpnp-delegate-with-credit (st event)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (or (not (equal (fn-cbor-ag-car event) :base))
                                  (fn-bpn-machine-eventp (fn-bpn-nth 1 event)))
                              (or (not (equal (fn-cbor-ag-car event)
                                              :recover-fnbs))
                                  (and (true-listp (fn-bpn-nth 2 event))
                                       (<= (len (fn-bpn-nth 2 event))
                                           *fn-bpn-machine-max-records*))))
                  :verify-guards nil))
  (let* ((answer (fn-bpn-report-author-step st event))
         (effects (fn-bpnf-answer-effects answer))
         (effect (fn-bpn-nth 0 effects))
         (inner (fn-bpnf-answer-state answer))
         (node (fn-bpn-config-node-id
                (fn-bpn-machine-state-config (fn-bpnf-base st))))
         (kind (fn-bpnp-credit-proposal-kind effect (fn-bpnf-issued inner)))
         (proposal-delta (and kind (fn-bpnp-issued-debt-delta inner node)))
         (ready (and (equal (fn-cbor-ag-car event) :recover-fnbs)
                     (equal (fn-bpn-nth 0 effect) :restart-ready)))
         (published
          (and (equal (fn-cbor-ag-car event) :persist-result)
               (equal (fn-bpn-nth 3 event) :durable)
               (fn-bpnf-operation-matchp
                (fn-bpnf-issued st)
                (fn-bpn-nth 1 event) (fn-bpn-nth 2 event))
               (fn-bpnp-received-publicationp (fn-bpnf-issued st) effects)))
         (published-delta
          (and published (fn-bpnp-issued-debt-delta st node))))
    (cond
     (ready
      (fn-bpnf-answer
       (fn-bpnp-with-credit
        (fn-bpnp-with-waits inner nil)
        (fn-bpn-nth 5 event)
        (fn-bpnd-debt inner
                      (fn-bpn-config-node-id
                       (fn-bpn-machine-state-config (fn-bpnf-base inner)))))
       effects))
     ((and kind
           (not (and (integerp proposal-delta)
                     (fn-bpnd-admitp
                      (fn-bpnp-used st) (fn-bpnp-debt st)
                      *fn-bpnp-control-margin*
                      proposal-delta
                      (if (< proposal-delta 0) :pay :spend)))))
      (let ((refusal (fn-bpnp-credit-refusal st event kind)))
        (fn-bpnf-answer
         (fn-bpnp-with-credit
          (fn-bpnf-answer-state refusal)
          (fn-bpnp-used st) (fn-bpnp-debt st))
         (fn-bpnf-answer-effects refusal))))
     ((and published (not (integerp published-delta)))
      ; A visible final that cannot be applied from its exact issued row
      ; remains a recovery-only uncertainty, never an accepted callback.
      (fn-bpnf-answer
       (fn-bpnp-with-credit
        (fn-bpnf-with-issued
         st (fn-bpnf-operation
             (fn-bpn-nth 1 (fn-bpnf-issued st))
             (fn-bpn-nth 2 (fn-bpnf-issued st))
             (fn-bpn-nth 3 (fn-bpnf-issued st))
             (fn-bpn-nth 4 (fn-bpnf-issued st)) :uncertain))
        (fn-bpnp-used st) (fn-bpnp-debt st))
       (list (fn-bpnp-publication-fault-effect (fn-bpnf-issued st)))))
     (t
      (fn-bpnf-answer
       (fn-bpnp-with-credit
        (fn-bpnp-with-waits inner (fn-bpnp-waits st))
        (if published (1+ (nfix (fn-bpnp-used st)))
          (fn-bpnp-used st))
        (if published (+ (nfix (fn-bpnp-debt st)) published-delta)
          (fn-bpnp-debt st)))
       effects)))))

(defun fn-bpnp-step (st event)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (fn-bpnp-session-listp (fn-bpnp-sessions st))
                              (true-listp (fn-bpnf-held-list st))
                              (fn-bpnp-host-eventp event))
                  :verify-guards nil))
  (if (and (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
           (not (equal (fn-cbor-ag-car event) :recover-fnbs)))
      (fn-bpnf-answer st nil)
  (cond
   ((and (fn-bpnp-domain-recover-eventp event)
         (not (fn-bpnp-clock-domain-admitsp event)))
    (fn-bpnp-clock-domain-fence st (fn-bpn-nth 6 event)))
   ((and (equal (fn-cbor-ag-car event) :persist-result)
         (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :conflict))
    (fn-bpnp-conflict-persist-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event) (fn-bpn-nth 3 event)))
   ((and (equal (fn-cbor-ag-car event) :deliver-result)
         (equal (fn-bpn-nth 4 event) :busy))
    (fn-bpnp-busy-delivery-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event) (fn-bpn-nth 3 event)
     (fn-bpn-nth 6 event)))
   ((fn-bpnp-conflict-held st event)
    (fn-bpnp-conflict-propose-step st event (fn-bpnp-conflict-held st event)))
   ((equal (fn-cbor-ag-car event) :session)
    (let* ((peer (fn-bpn-nth 1 event))
           (session (fn-bpn-nth 2 event))
           (open (fn-bpn-nth 3 event))
           (mru (fn-bpn-nth 4 event))
           (observation (fn-bpn-nth 5 event))
           (sessions (if open
                         (fn-bpnp-open-session
                          (fn-bpnp-sessions st) peer session mru)
                       (fn-bpnp-remove-peer-session
                        peer (fn-bpnp-sessions st))))
           (updated (fn-bpnp-with-runtime
                     st sessions (fn-bpnp-pending-image st))))
      (if open
          (fn-bpnp-start-one updated peer session mru observation)
        (fn-bpnf-answer updated nil))))
   ((equal (fn-cbor-ag-car event) :resume)
    (let ((peer (fn-bpn-nth 1 event))
          (session (fn-bpn-nth 2 event))
          (observation (fn-bpn-nth 3 event)))
      (let ((current (fn-bpnp-find-session
                      (fn-bpnp-sessions st) peer session)))
        (if current
            (fn-bpnp-start-one
             st peer session (fn-bpn-nth 3 current) observation)
          (fn-bpnf-answer st nil)))))
   ((equal (fn-cbor-ag-car event) :operator-resume)
    (fn-bpnp-operator-resume-step st (fn-bpn-nth 1 event)))
   ((equal (fn-cbor-ag-car event) :forward-result)
    (fn-bpnp-forward-result-propose-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
     (fn-bpn-nth 3 event) (fn-bpn-nth 4 event)
     (fn-bpn-nth 5 event)))
   ((equal (fn-cbor-ag-car event) :progress)
      (let ((answer
             (fn-bpnp-progress-step
              st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
              (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))))
        (fn-bpnf-answer
         (fn-bpnp-with-runtime
          (fn-bpnp-with-credit
           (fn-bpnf-answer-state answer)
           (fn-bpnp-used st) (fn-bpnp-debt st))
          (fn-bpnp-sessions st) (fn-bpnp-pending-image st))
         (fn-bpnf-answer-effects answer))))
   ((and (equal (fn-cbor-ag-car event) :persist-result)
         (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :dispatch))
    (fn-bpnp-preserve-runtime-answer
     (fn-bpnp-dispatch-persist-step
      st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
      (fn-bpn-nth 3 event)) st nil))
   ((and (equal (fn-cbor-ag-car event) :persist-result)
         (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :attempt))
    (fn-bpnp-attempt-persist-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
     (fn-bpn-nth 3 event)))
   ((and (equal (fn-cbor-ag-car event) :persist-result)
         (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :forward-result))
    (fn-bpnp-forward-result-persist-step
     st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
     (fn-bpn-nth 3 event)))
   (t
    (let ((answer (fn-bpnp-delegate-with-credit st event)))
      (fn-bpnp-preserve-runtime-answer
       answer st
       (and (equal (fn-cbor-ag-car event) :recover-fnbs)
            (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects answer)))
                   :restart-ready))))))))
