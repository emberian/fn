(in-package "ACL2")
(include-book "../books/bp-native-app-fast")

(defun fn-bprj-store (state)
 (declare (xargs :stobjs state :mode :program))
 ; The native BP application node owns one Store inside fn-owner.  This
 ; selector is only a callback choice; it never copies that Store into the
 ; standalone bridge global.  Operator-only app-journal commands retain the
 ; legacy standalone source.
 (if (equal (f-get-global 'fn-bprj-store-source state) :owner-bound)
     (f-get-global 'fn-bprj-bound-store state)
   (f-get-global 'fn-store-sn state)))

(defun fn-bprj-bind-store (store state)
 (declare (xargs :stobjs state :mode :program))
 ; This low-level setter is called only by fn-owner-app-bind-receipt-store,
 ; whose STORE argument is read from the canonical fn-owner in the same ACL2
 ; state transition.  The native host has no store argument to invent.
 (let* ((state (f-put-global 'fn-bprj-bound-store store state))
        (state (f-put-global 'fn-bprj-store-source :owner-bound state)))
  (value :ready)))

(defun fn-bprj-use-standalone-store (state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((state (f-put-global 'fn-bprj-store-source :standalone state))
        (state (f-put-global 'fn-bprj-bound-store nil state)))
  (value :ready)))

(defun fn-bprj-valid-config (record state)
 (declare (xargs :stobjs state :mode :program))
 (value (if (and (fn-bprr-configp record)
                 (fn-bpr-configp (fn-bprr-config record))) t nil)))

(defun fn-bprj-reset (state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((state (f-put-global 'fn-bprj-state nil state))
        (state (f-put-global 'fn-bpaj-state nil state)))
  (value :ready)))

;; The records flip (flip-L4): replay, preflight, apply and dispatch read the
;; bound Store's rows through the live arena (read-only).
(defun fn-bprj-install (records fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let ((answer (fn-bpaj-replay (fn-bprj-store state) records fn-arena)))
  (if (not (car answer)) (value :fault)
   (let* ((joined (fn-bprr-nth 1 answer))
          (state (f-put-global 'fn-bpaj-state joined state))
          (state (f-put-global 'fn-bprj-state
                               (fn-bpaj-receiver joined) state)))
    (value :ready)))))

(defun fn-bprj-preflight (record fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (value (if (car (fn-bpaj-apply-record-fast
                  (f-get-global 'fn-bpaj-state state)
                  (fn-bprj-store state) record fn-arena)) :ready :fault)))

(defun fn-bprj-apply (record fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let ((answer (fn-bpaj-apply-record-fast
                (f-get-global 'fn-bpaj-state state)
                (fn-bprj-store state) record fn-arena)))
  (if (not (car answer)) (value :fault)
   (let* ((joined (fn-bprr-nth 1 answer))
          (state (f-put-global 'fn-bpaj-state joined state))
          (state (f-put-global 'fn-bprj-state
                               (fn-bpaj-receiver joined) state)))
    (value :ready)))))

(defun fn-bprj-preview-receipt (work-id receipt-id state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((st (f-get-global 'fn-bprj-state state))
        (next (fn-bpaj-bpr-prepare-receipt-fast
               st work-id receipt-id t))
        (pending (fn-bpr-state-pending next)))
  (value (if (and (not (equal next st)) (consp pending))
    (fn-bpa-encode (fn-bpr-receipt-entry-receipt pending)) nil))))

(defun fn-bprj-receipt-adu (request-octets state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (let ((parsed (fn-bpa-decode-exact request-octets)))
  (value (if (fn-record-parse-okp parsed)
    (fn-bpaj-bpr-receipt-adu-fast
     (f-get-global 'fn-bprj-state state)
     (fn-record-parse-value parsed)) nil))))

; Native application projections.  These read the same joined replay state the
; publication preflight and apply functions above update.
(defun fn-bprj-request-status (request-octets state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bpaj-request-status-fast
         (f-get-global 'fn-bpaj-state state) request-octets)))

(defun fn-bprj-request-action (request-octets generation fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (value (fn-bpaj-dispatch-fast
         (f-get-global 'fn-bpaj-state state)
         (fn-bprj-store state) request-octets generation fn-arena)))

(defun fn-bprj-config-status (destination policy issuer state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bpaj-config-status-fast
         (f-get-global 'fn-bpaj-state state) destination policy issuer)))

; PKT-646: the transit intent and context carry the request's reference
; (its metadata, the article's length and digest), the projection's length
; and digest and the Store record's identity, never their bytes; ACL2 builds
; both (books/bp-transit-join.lisp `fn-bpaj-transit-intent-from-plan',
; books/bp-native-app.lisp `fn-bpaj-transit-context-record').
(defun fn-bprj-request-transit-intent-record (record state)
 (declare (xargs :stobjs state :mode :program))
 (value (if (fn-bpaj-transit-intentp record) record nil)))

(defun fn-bprj-request-transit-context-record
 (inbound-id request-octets store-record generation txid record-generation
             application-result state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (value (fn-bpaj-transit-context-record inbound-id request-octets store-record
                                        generation txid record-generation
                                        application-result)))

(defun fn-bprj-pending-receipt-resolution (state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bpaj-pending-receipt-resolution-fast
         (f-get-global 'fn-bpaj-state state))))

(defun fn-bprj-request-work-id (request-octets state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (let ((request (fn-bpaj-request request-octets)))
  (value (and request (fn-bpa-request-work-id request)))))

(defun fn-bprj-request-receipt-id (request-octets state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (let ((request (fn-bpaj-request request-octets)))
  (value (and request (fn-bpaj-receipt-id request)))))

(defun fn-bprj-request-source-eid (request-octets state)
 (declare (xargs :stobjs state :mode :program))
 (let ((request (fn-bpaj-request request-octets)))
  (value (and request (fn-bpa-request-source-eid request)))))

(defun fn-bprj-request-bound-inbound-id (request-octets state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (value (fn-bpaj-request-inbound-id
         (f-get-global 'fn-bpaj-state state) request-octets)))

(defun fn-bprj-request-bound-generation (request-octets state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (value (fn-bpaj-request-generation
         (f-get-global 'fn-bpaj-state state) request-octets)))

(defun fn-bprj-request-result (request-octets state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (value (fn-bpaj-request-result
         (f-get-global 'fn-bpaj-state state) request-octets)))

(defun fn-bprj-request-planned-txid (request-octets state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bpaj-request-planned-txid
         (f-get-global 'fn-bpaj-state state) request-octets)))

(defun fn-bprj-request-planned-result (request-octets state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (value (fn-bpaj-request-planned-result
         (f-get-global 'fn-bpaj-state state) request-octets)))
