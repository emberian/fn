; One host-called progress extension over the FNBS state.  Ordinary events
; delegate to the report/fragment/foundation owner.  Route waits are volatile:
; recovery clears them and a later progress event re-evaluates the held rows.
(in-package "ACL2")
(include-book "bp-report-author")
(include-book "bp-app-handoff-time")
(include-book "bp-node-receive-boundary")
(include-book "bp-node-debt")
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
         (integerp (fn-bpn-nth 3 wait))
         (<= free (fn-bpn-nth 3 wait)))))

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
  (declare (xargs :guard t))
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

(defun fn-bpnp-host-eventp (event)
  (declare (xargs :guard t))
  (if (equal (fn-cbor-ag-car event) :progress)
      (and (true-listp event) (equal (len event) 5)
           (fn-bpp-eidp (fn-bpn-nth 1 event))
           (fn-clock-observationp (fn-bpn-nth 2 event))
           (fn-bpnp-routesp (fn-bpn-nth 3 event))
           (<= (len (fn-bpn-nth 3 event)) *fn-bpnp-max-routes*)
           (fn-frame-natp (fn-bpn-nth 4 event)))
    (fn-bpnf-host-eventp event)))

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
                              (fn-bpnp-host-eventp event))
                  :verify-guards nil))
  (if (and (equal (fn-bpn-nth 5 (fn-bpnf-issued st)) :uncertain)
           (not (equal (fn-cbor-ag-car event) :recover-fnbs)))
      (fn-bpnf-answer st nil)
  (if (equal (fn-cbor-ag-car event) :progress)
      (let ((answer
             (fn-bpnp-progress-step
              st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
              (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))))
        (fn-bpnf-answer
         (fn-bpnp-with-credit
          (fn-bpnf-answer-state answer)
          (fn-bpnp-used st) (fn-bpnp-debt st))
         (fn-bpnf-answer-effects answer)))
    (if (and (equal (fn-cbor-ag-car event) :persist-result)
             (equal (fn-bpn-nth 3 (fn-bpnf-issued st)) :dispatch))
        (fn-bpnp-dispatch-persist-step
         st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
         (fn-bpn-nth 3 event))
      (fn-bpnp-delegate-with-credit st event)))))
