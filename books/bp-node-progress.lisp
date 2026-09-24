; One host-called progress extension over the FNBS state.  Ordinary events
; delegate to the report/fragment/foundation owner.  Route waits are volatile:
; recovery clears them and a later progress event re-evaluates the held rows.
(in-package "ACL2")
(include-book "bp-report-author")
(include-book "bp-app-handoff-time")
(include-book "bp-node-receive-boundary")
(set-verify-guards-eagerness 0)

(defconst *fn-bpnp-max-routes* 64)

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

(defun fn-bpnp-with-waits (st waits)
  (declare (xargs :guard t))
  (if (and (null waits) (< (len st) 12)) st
    (update-nth 11 waits st)))

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

(defun fn-bpnp-live-pendingp (h node observation)
  (declare (xargs :guard t))
  (and (fn-bpnf-heldp h)
       (fn-bpp-eidp node)
       (equal (fn-bpn-nth 12 h) '(:dispatch-pending))
       (null (fn-bpn-nth 10 h))
       (null (fn-bpn-nth 14 h))
       (equal (fn-bpah-held-expiry h observation) :live)
       (let* ((bundle (fn-bpnf-held-bundle h))
              (primary (fn-bpb-bundle-primary bundle)))
         (and (fn-bpb-bundlep bundle)
              (fn-bpp-blockp primary)
              (not (fn-bpp-fragmentp (fn-bpp-flags primary)))
              (if (equal (fn-bpp-destination primary) node)
                  (fn-bpah-local-pendingp h node)
                t)))))

(defun fn-bpnp-blockedp (h node routes generation waits)
  (declare (xargs :guard t))
  (let* ((key (fn-bpnp-wait-key h))
         (wait (fn-bpnp-wait-for key waits))
         (primary (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
         (destination (fn-bpp-destination primary))
         (route (fn-bpnp-route-peer destination routes)))
    (and (not (equal destination node))
         (equal (fn-bpn-nth 0 wait) :bpnp-wait)
         (equal (fn-bpn-nth 3 wait) generation)
         (if route (equal (fn-bpn-nth 2 wait) :session)
           (equal (fn-bpn-nth 2 wait) :route)))))

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

(defun fn-bpnp-delivery-view (held)
  (declare (xargs :guard t))
  (if (not (fn-bpnf-heldp held)) nil
    (let* ((bundle (fn-bpnf-held-bundle held))
           (primary (fn-bpb-bundle-primary bundle)))
      (if (not (and (fn-bpb-bundlep bundle) (fn-bpp-blockp primary))) nil
        (list :delivery (fn-bpnp-wait-key held)
              (fn-bpah-held-class held) (fn-bpb-payload bundle)
              (fn-bpn-nth 4 held)
              (fn-bpp-primary-identity primary)
              (fn-bpaj-eid-text (fn-bpp-source primary))
              (fn-bpaj-eid-text (fn-bpp-destination primary)))))))

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
           (h (fn-bpnp-oldest-eligible
               (fn-bpnf-held-list st) node observation routes generation
               waits nil)))
      (if (not h)
          (let ((uncertain
                 (fn-bpah-pending-decision-at st node observation)))
            (if (equal (car uncertain) :uncertain)
                (fn-bpnf-answer
                 st (list (list :progress-uncertain (fn-bpn-nth 1 uncertain))))
              (fn-bpnf-answer st nil)))
        (let* ((key (fn-bpnp-wait-key h))
               (primary (fn-bpb-bundle-primary (fn-bpnf-held-bundle h)))
               (destination (fn-bpp-destination primary)))
          (if (equal destination node)
              (let ((answer (fn-bpah-deliver-step st key node)))
                (fn-bpnf-answer
                 (fn-bpnp-with-waits (fn-bpnf-answer-state answer) waits)
                 (fn-bpnf-answer-effects answer)))
            (let* ((reason (if (fn-bpnp-route-peer destination routes)
                               :session :route))
                   (new-waits
                    (cons (list :bpnp-wait key reason generation)
                          (fn-bpnp-remove-wait key waits))))
              (fn-bpnf-answer
               (fn-bpnp-with-waits st new-waits)
               (list (list :progress-wait key reason generation))))))))))

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

(defun fn-bpnp-step (st event)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (fn-bpnp-host-eventp event))
                  :verify-guards nil))
  (if (equal (fn-cbor-ag-car event) :progress)
      (fn-bpnp-progress-step
       st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
       (fn-bpn-nth 3 event) (fn-bpn-nth 4 event))
    (let ((answer (fn-bpn-report-author-step st event)))
      (fn-bpnf-answer
       (fn-bpnp-with-waits
        (fn-bpnf-answer-state answer)
        (if (equal (fn-cbor-ag-car event) :recover-fnbs)
            nil (fn-bpnp-waits st)))
       (fn-bpnf-answer-effects answer)))))
