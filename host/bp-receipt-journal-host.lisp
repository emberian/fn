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

(defun fn-bprj-preflight (record fn-arena fn-hist state)
 (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
 ; The history stobj synced to the Store read (R, books/history-columns-relation.lisp).
 (mv-let (fn-hist state) (fn-host-hist-sync (fn-bprj-store state) fn-hist state)
  (mv nil (if (car (fn-bpaj-apply-record-fast
                    (f-get-global 'fn-bpaj-state state)
                    (fn-bprj-store state) record fn-arena fn-hist)) :ready :fault)
      fn-hist state)))

(defun fn-bprj-apply (record fn-arena fn-hist state)
 (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program))
 (mv-let (fn-hist state) (fn-host-hist-sync (fn-bprj-store state) fn-hist state)
  (let ((answer (fn-bpaj-apply-record-fast
                 (f-get-global 'fn-bpaj-state state)
                 (fn-bprj-store state) record fn-arena fn-hist)))
   (if (not (car answer)) (mv nil :fault fn-hist state)
    (let* ((joined (fn-bprr-nth 1 answer))
           (state (f-put-global 'fn-bpaj-state joined state))
           (state (f-put-global 'fn-bprj-state
                                (fn-bpaj-receiver joined) state)))
     (mv nil :ready fn-hist state))))))

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

(defun fn-bprj-request-action (request-octets generation fn-arena fn-hist state)
 (declare (xargs :stobjs (fn-arena fn-hist state) :mode :program
                  :guard (fn-cbor-octet-listp request-octets)))
 (mv-let (fn-hist state) (fn-host-hist-sync (fn-bprj-store state) fn-hist state)
  (mv nil (fn-bpaj-dispatch-fast
           (f-get-global 'fn-bpaj-state state)
           (fn-bprj-store state) request-octets generation fn-arena fn-hist)
      fn-hist state)))

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
