; ACL2 boundary for the native BP application receiver.
;
; The raw adapter transports these projections.  It never parses an article,
; chooses a Store record, constructs provenance, or reads a second Store
; image.  Every call below reads the canonical configured owner installed by
; host/owner-host.lisp.
(in-package "ACL2")
(include-book "../books/bp-native-app-fast")

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

(defun fn-owner-app-plan-install
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
    (value
     (cond ((not request) :refused)
           ((not (equal (car fields) :ok)) :refused)
           ((not (fn-bpaj-request-subjectp request)) :refused)
           ((not (equal (fn-bpa-request-source-eid request)
                        (f-get-global 'fn-owner-app-bundle-source state))) :refused)
           ((not (equal (fn-bpa-request-destination-eid request)
                        (f-get-global 'fn-owner-app-bundle-destination state))) :refused)
           ((not evidence) :refused)
           ((not planned-result) :refused)
           (t :ready)))))

(defun fn-owner-app-plan
  (inbound-id request-octets node-id bundle-identity
              bundle-source bundle-destination state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((state (f-put-global 'fn-owner-app-bundle-source bundle-source state))
         (state (f-put-global 'fn-owner-app-bundle-destination
                              bundle-destination state)))
    (fn-owner-app-plan-install inbound-id request-octets node-id
                               bundle-identity state)))

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
      (fn-owner-control-submit
       (f-get-global 'fn-owner-app-msgid state)
       (f-get-global 'fn-owner-app-groups state)
       (f-get-global 'fn-owner-app-article state) state))))

(defun fn-owner-app-record (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((request-octets (f-get-global 'fn-owner-app-request state))
         (request (fn-bpaj-request request-octets))
         (answer (fn-bpaj-record-lookup-fast
                  (fn-owner-store state) request))
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
