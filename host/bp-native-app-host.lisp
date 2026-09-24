; ACL2 boundary for the native BP application receiver.
;
; The raw adapter transports these projections.  It never parses an article,
; chooses a Store record, constructs provenance, or reads a second Store
; image.  Every call below reads the canonical configured owner installed by
; host/owner-host.lisp.
(in-package "ACL2")
(include-book "../books/bp-channel-ingress")

(defun fn-owner-bp-tcpcl-ingress
    (fnbs-state session-counter xfer-id channel announced-uri state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bpaj-tcpcl-ingress-result
          (fn-owner-config state) fnbs-state channel announced-uri
          session-counter xfer-id)))

(defun fn-owner-bp-receipt-trustedp (view state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bpah-receipt-trustedp view (fn-owner-config state))))

(defun fn-owner-bp-request-trustedp (view state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bpah-request-trustedp view (fn-owner-config state))))

; D23: ACL2's source decision for a delivered view, as the line the host
; prints (direct, carried with carrier and author, or the refusal reason).
(defun fn-owner-bp-source-decision-line (view state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bpah-source-decision-line view (fn-owner-config state))))
(include-book "../books/bp-native-app-fast")
(include-book "../books/bp-transit-join")

(defun fn-owner-app-bind-receipt-store (state)
  (declare (xargs :stobjs state :mode :program))
  ; An explicit snapshot for this serialized callback.  The caller rebinds
  ; immediately after every owner mutation and before FNRJ preflight/apply;
  ; the standalone fn-store-sn global is never consulted in owner mode.
  (let* ((state (f-put-global 'fn-bprj-bound-store
                              (fn-owner-store state) state))
         (state (f-put-global 'fn-bprj-store-source :owner-bound state)))
    (value :ready)))

(defun fn-owner-app-unbind-receipt-store (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-bprj-store-source :standalone state))
         (state (f-put-global 'fn-bprj-bound-store nil state)))
    (value :ready)))

; Flat result: (outcome reason adu primary-identity source destination).
; Fragments are refused by fn-bpn-receive, so the canonical primary identity
; is the complete RFC 9171 bundle identity on every accepted branch.
(defun fn-bpapp-receive (config octets obs)
  (declare (xargs :guard t :mode :program))
  (if (not (and (fn-bpn-configp config) (fn-cbor-octet-listp octets)
                (fn-clock-observationp obs)))
      (list :refused :host-arguments nil nil "" "")
    (let ((r (fn-bpn-receive config octets obs)))
      (cond
       ((fn-bpn-acceptedp r)
        (let* ((bundle (fn-bpn-outcome-bundle r))
               (primary (fn-bpb-bundle-primary bundle)))
          (list :accepted nil (fn-bpn-received-adu r)
                (fn-bpp-primary-identity primary)
                (fn-bpaj-eid-text (fn-bpp-source primary))
                (fn-bpaj-eid-text (fn-bpp-destination primary)))))
       ((fn-bpn-uncertainp r)
        (list :uncertain (fn-bpn-outcome-reason r) nil nil "" ""))
       (t (list :refused (fn-bpn-outcome-reason r) nil nil "" ""))))))

(defun fn-bpapp-receive-outcome (r) (declare (xargs :guard t :mode :program)) (nth 0 r))
(defun fn-bpapp-receive-reason (r) (declare (xargs :guard t :mode :program)) (nth 1 r))
(defun fn-bpapp-receive-adu (r) (declare (xargs :guard t :mode :program)) (nth 2 r))
(defun fn-bpapp-receive-identity (r) (declare (xargs :guard t :mode :program)) (nth 3 r))
(defun fn-bpapp-receive-source (r) (declare (xargs :guard t :mode :program)) (nth 4 r))
(defun fn-bpapp-receive-destination (r) (declare (xargs :guard t :mode :program)) (nth 5 r))

; REASON is nil for a ready plan and the refusal's keyword otherwise.  It is
; left in `fn-owner-app-refusal-reason' for fn-owner-app-refusal-log, which
; renders the receiver's line (books/owner-log.lisp
; fn-olog-bp-app-refusal-line).
(defun fn-owner-app-plan-answer (reason state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global 'fn-owner-app-refusal-reason reason state)))
    (value (if reason :refused :ready))))

(defun fn-owner-app-plan-install-legacy
  (inbound-id request-octets node-id bundle-identity state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((request (fn-bpaj-request request-octets))
         (fields (and request (fn-bpaj-article-fields request)))
         (evidence (and request
                        (fn-bpaj-bp-provenance-octets
                         node-id bundle-identity request)))
         (lookup (and request
                      (fn-bpaj-record-lookup-fast
                       (fn-owner-store state) request)))
         (planned-result (case (car lookup)
                           (:absent :accepted)
                           (:found :duplicate)
                           (otherwise nil)))
         (generation (fn-cfg-generation (fn-owner-config state)))
         (txid (fn-state-next-txid
                (fn-node-acceptance (fn-owner-node state))))
         (state (f-put-global 'fn-owner-app-request request-octets state))
         (state (f-put-global 'fn-owner-app-inbound-id inbound-id state))
         (state (f-put-global 'fn-owner-app-generation generation state))
         (state (f-put-global 'fn-owner-app-txid txid state))
         (state (f-put-global 'fn-owner-app-evidence evidence state))
         (state (f-put-global 'fn-owner-app-planned-result
                              planned-result state))
         (state (f-put-global 'fn-owner-app-msgid
                              (and (equal (car fields) :ok) (cadr fields)) state))
         (state (f-put-global 'fn-owner-app-groups
                              (and (equal (car fields) :ok) (caddr fields)) state))
         (state (f-put-global 'fn-owner-app-article
                              (and request (fn-bpa-request-article request)) state)))
    (fn-owner-app-plan-answer
     (cond ((not request) :request)
           ((not (equal (car fields) :ok)) :article-fields)
           ((not (fn-bpaj-request-subjectp request)) :request-subject)
           ((not (equal (fn-bpa-request-source-eid request)
                        (f-get-global 'fn-owner-app-bundle-source state)))
            :bundle-source)
           ((not (equal (fn-bpa-request-destination-eid request)
                        (f-get-global 'fn-owner-app-bundle-destination state)))
            :bundle-destination)
           ((not evidence) :provenance)
           ((not planned-result) :store-lookup)
           (t nil))
     state)))

(defun fn-owner-app-plan-install
  (inbound-id request-octets node-id bundle-identity ingress source-eid state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((joined (f-get-global 'fn-bpaj-state state))
         (status (fn-bpaj-request-status-fast joined request-octets))
         (existing (fn-bpaj-request-intent joined request-octets))
         (oldp (equal (fn-bpaj-nth 0 existing) :request-intent)))
    (cond
     ((member-equal status '(:committed :context :pending-receipt))
      ; A bound request never plans again: fn-bpaj-dispatch-fast answers
      ; these statuses with :return-receipt, :prepare-receipt or
      ; :resolve-absent.  Its planning fields are still the durable ones from
      ; the intent recovered at open, never a value left in this process by
      ; an earlier request or absent after a restart.  A historical context
      ; admitted before any intent has none, and the adapter never asks.
      (let* ((state (f-put-global 'fn-owner-app-transitp nil state))
            (state (f-put-global 'fn-owner-app-request request-octets state))
            (state (f-put-global 'fn-owner-app-generation
                                 (fn-cfg-generation (fn-owner-config state))
                                 state))
            (state (f-put-global 'fn-owner-app-txid
                                 (fn-bpaj-request-planned-txid
                                  joined request-octets)
                                 state))
            (state (f-put-global 'fn-owner-app-planned-result
                                 (fn-bpaj-request-planned-result
                                  joined request-octets)
                                 state)))
        (value :ready)))
     (oldp
      (fn-owner-app-plan-install-legacy
       inbound-id request-octets node-id bundle-identity state))
     ((not (member-equal status '(:new :intent)))
      (fn-owner-app-plan-answer :request-status state))
     (t
      (let* ((request (fn-bpaj-request request-octets))
             (cfg (fn-owner-config state))
             (generation (fn-cfg-generation cfg))
             (txid (fn-state-next-txid
                    (fn-node-acceptance (fn-owner-node state))))
             (plan (and request
                        (fn-bpaj-transit-plan
                         (fn-owner-node state) cfg ingress source-eid
                         request-octets (fn-own-clock (fn-owner-core state)))))
             (planned (if (equal (car plan) :have) :duplicate :accepted))
             (new-intent
               (and (member-equal (car plan) '(:submit :have))
                    (fn-bpaj-transit-intent-from-plan
                     cfg inbound-id request-octets generation txid
                     planned plan)))
             (intent (or existing new-intent))
             (lookup (and request intent
                          (fn-bpaj-transit-record-lookup-fast
                           (fn-owner-store state) request intent)))
             (bindingp (equal (car lookup) :found))
             (freshp (and (equal status :new) new-intent
                          (or (and (equal (car plan) :submit)
                                   (equal (car lookup) :absent))
                              (and (equal (car plan) :have) bindingp))))
             (retryp (and (equal status :intent)
                          (fn-bpaj-transit-intentp existing)
                          (or bindingp
                              (and (equal generation (fn-bpaj-nth 3 existing))
                                   (equal (car plan) :submit)
                                   (equal (fn-bpaj-nth 1 plan)
                                          (fn-bpaj-nth 6 existing))
                                   (equal (fn-bpaj-nth 4 plan)
                                          (fn-bpaj-nth 9 existing))
                                   (equal (car lookup) :absent)))))
             (evidence (and plan (fn-record-string-octets
                                  (fn-bpaj-nth 6 plan))))
             (state (f-put-global 'fn-owner-app-request request-octets state))
             (state (f-put-global 'fn-owner-app-inbound-id inbound-id state))
             (state (f-put-global 'fn-owner-app-generation
                                  (if existing (fn-bpaj-nth 3 existing)
                                    generation) state))
             (state (f-put-global 'fn-owner-app-txid
                                  (if existing (fn-bpaj-nth 4 existing)
                                    txid) state))
             (state (f-put-global 'fn-owner-app-planned-result
                                  (if existing (fn-bpaj-nth 5 existing)
                                    planned) state))
             (state (f-put-global 'fn-owner-app-intent-v3 intent state))
             (state (f-put-global 'fn-owner-app-transitp t state))
             (state (f-put-global 'fn-owner-app-peer
                                  (and intent (fn-bpaj-nth 6 intent)) state))
             (state (f-put-global 'fn-owner-app-msgid
                                  (and plan (fn-bpaj-nth 2 plan)) state))
             (state (f-put-global 'fn-owner-app-article
                                  (and request (fn-bpa-request-article request))
                                  state))
             (state (f-put-global 'fn-owner-app-stored
                                  (and intent (fn-bpaj-nth 9 intent)) state))
             (state (f-put-global 'fn-owner-app-groups
                                  (and plan (fn-oag-group-octets
                                             (fn-bpaj-nth 5 plan))) state))
             (state (f-put-global 'fn-owner-app-evidence evidence state))
             (state (f-put-global 'fn-owner-app-obligation-id
                                  (and plan (fn-bpaj-nth 8 plan)) state))
             (state (f-put-global 'fn-owner-app-stored-subject
                                  (and plan (fn-bpaj-nth 9 plan)) state)))
        ; The planner's own refusal comes first: fn-bpaj-transit-plan's
        ; (:refused :no-principal) or (:refused :request), or the deferral
        ; reason of a (:busy reason) plan, which this install still answers
        ; :refused.
        (fn-owner-app-plan-answer
         (cond ((not request) :request)
               ((member-equal (car plan) '(:refused :busy))
                (or (fn-bpaj-nth 1 plan) (car plan)))
               ((not (or freshp retryp)) :intent)
               ((not (equal (fn-bpa-request-source-eid request)
                            (f-get-global 'fn-owner-app-bundle-source state)))
                :bundle-source)
               ((not (equal (fn-bpa-request-destination-eid request)
                            (f-get-global 'fn-owner-app-bundle-destination
                                          state)))
                :bundle-destination)
               (t nil))
         state))))))

(defun fn-owner-app-plan
  (inbound-id request-octets node-id bundle-identity ingress
              bundle-source bundle-destination state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-app-bundle-source bundle-source state))
         (state (f-put-global 'fn-owner-app-bundle-destination
                              bundle-destination state))
         (state (f-put-global 'fn-owner-app-refusal-reason nil state)))
    (fn-owner-app-plan-install inbound-id request-octets node-id
                               bundle-identity ingress bundle-source state)))

; The receiver's line for transfer XFER-ID that fnn-bpapp-accept-locked
; answered RESULT, with the reason the last plan left (nil when the plan was
; ready and a later step answered).  Leaves the line in `fn-owner-log-line'
; for host/native/owner.lisp fnn-owner-log and answers the line's class
; (:refused, :deferred or :uncertain; :accepted or :duplicate never reach
; here), which the host returns to the convergence layer.
(defun fn-owner-app-refusal-log (result xfer-id state)
  (declare (xargs :stobjs state :mode :program))
  (let ((state (f-put-global
                'fn-owner-log-line
                (fn-olog-bp-app-refusal-line
                 result
                 (f-get-global 'fn-owner-app-refusal-reason state)
                 xfer-id)
                state)))
    (value (fn-olog-bp-app-class result))))

(defun fn-owner-app-current-generation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-cfg-generation (fn-owner-config state))))

; Sole ACL2 application admission event.  The request intent must already be
; durable: fn-bpaj-dispatch-fast is called over the same bound owner Store, and
; only its :submit action reaches the ordinary control submission transition.
(defun fn-owner-app-submit (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((request (f-get-global 'fn-owner-app-request state))
         (generation (f-get-global 'fn-owner-app-generation state))
         (action (fn-bpaj-dispatch-fast
                  (f-get-global 'fn-bpaj-state state)
                  (fn-owner-store state) request generation)))
    (if (not (equal action (list :submit)))
        (value (if (equal (car action) :busy) :busy :refused))
      (if (f-get-global 'fn-owner-app-transitp state)
          (fn-owner-bp-transit-submit
           (f-get-global 'fn-owner-app-peer state)
           (f-get-global 'fn-owner-app-msgid state)
           (f-get-global 'fn-owner-app-article state)
           (f-get-global 'fn-owner-app-obligation-id state)
           (f-get-global 'fn-owner-app-stored-subject state) state)
        (fn-owner-control-submit
         (f-get-global 'fn-owner-app-msgid state)
         (f-get-global 'fn-owner-app-groups state)
         (f-get-global 'fn-owner-app-article state) state)))))

(defun fn-owner-app-record (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((request-octets (f-get-global 'fn-owner-app-request state))
         (request (fn-bpaj-request request-octets))
         (intent (fn-bpaj-request-intent
                  (f-get-global 'fn-bpaj-state state) request-octets))
         (answer (if (equal (fn-bpaj-nth 0 intent)
                            :request-transit-intent)
                     (fn-bpaj-transit-record-lookup-fast
                      (fn-owner-store state) request intent)
                   (fn-bpaj-record-lookup-fast
                    (fn-owner-store state) request)))
         (record (and (equal (car answer) :found) (cadr answer)))
         (state (f-put-global 'fn-owner-app-record
                              (and record (fn-record-encode record)) state))
         (state (f-put-global 'fn-owner-app-record-txid
                              (and record (fn-record-txid record)) state))
         (state (f-put-global 'fn-owner-app-record-generation
                              (and record (fn-record-generation record)) state)))
    (value (if record :found (car answer)))))

(defun fn-owner-app-evidence (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-evidence state)))
(defun fn-owner-app-msgid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-msgid state)))
(defun fn-owner-app-groups (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-groups state)))
(defun fn-owner-app-article (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-article state)))
(defun fn-owner-app-generation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-generation state)))
(defun fn-owner-app-txid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-txid state)))
(defun fn-owner-app-planned-result (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-planned-result state)))
(defun fn-owner-app-record-octets (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-record state)))
(defun fn-owner-app-record-txid (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-record-txid state)))
(defun fn-owner-app-record-generation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (f-get-global 'fn-owner-app-record-generation state)))
