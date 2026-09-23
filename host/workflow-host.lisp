; Program-mode bridge: decoded bounded local records enter the executable model.
(in-package "ACL2")
(include-book "../books/bp-workflow-constructors")
; `fn-sn-node' is books/store-node's; include it rather than depend on a
; store session having been opened in this ACL2 first.
(include-book "../books/store-node")

(defun fn-workflow-install-replay (records state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((sn (f-get-global 'fn-store-sn state))
        (node (and sn (fn-sn-node sn)))
        (answer (fn-bprl-replay-journal node records)))
  (if (car answer)
      (let ((state (f-put-global 'fn-workflow-state (fn-bp-journal-nth 1 answer) state)))
       ; Effects reconstructed from old durable records are audit history, not
       ; permission to repeat external actions after open.
       (let ((state (f-put-global 'fn-workflow-effects nil state)))
        ; The work ids this image came back holding.  ACL2 computes the list
        ; and the host carries it back unread: it is what separates a work
        ; recovered from a cut from one this session enqueues next.
        (let ((state (f-put-global 'fn-workflow-recovered
                      (fn-bp-work-ids
                       (fn-bp-state-works (fn-bp-journal-nth 1 answer)))
                      state)))
         (value :ready))))
    (value :fault))))

(defun fn-workflow-state (state)
 (declare (xargs :stobjs state :mode :program))
 (value (f-get-global 'fn-workflow-state state)))

(defun fn-workflow-reset (state)
 (declare (xargs :stobjs state :mode :program))
 (let ((state (f-put-global 'fn-workflow-state nil state)))
  (let ((state (f-put-global 'fn-workflow-effects nil state)))
   (let ((state (f-put-global 'fn-workflow-recovered nil state)))
    (value :ready)))))
(defun fn-workflow-effects (state)
 (declare (xargs :stobjs state :mode :program))
 (value (f-get-global 'fn-workflow-effects state)))

(defun fn-workflow-valid-config (record)
  ; Read-only validation for the first record.  Installation happens only
  ; after the native publication machine reports :durable.
  (if (fn-bp-config-recordp record) t nil))

(defun fn-workflow-enqueue-record
  (txid generation work-id msgid forward-obligation-id peer-eid policy-id
        terms-id state)
  ; Derive the immutable subject and archive obligation from the one recovered
  ; Store image.  Raw Lisp supplies identities and routing policy but never
  ; copies the Store binding decision.
  (declare (xargs :stobjs state :mode :program))
  (let* ((sn (f-get-global 'fn-store-sn state))
         (node (and sn (fn-sn-node sn)))
         (binding (and node
                       (fn-node-find-binding msgid (fn-node-bindings node))))
         (record
          (and binding
               (list :enqueue txid generation work-id msgid
                     (fn-node-binding-subject binding)
                     (fn-node-binding-id binding)
                     forward-obligation-id peer-eid policy-id terms-id))))
    (value (if (and record (fn-bp-journal-recordp record)) record nil))))

; Constructors return nil on refusal; raw Lisp only publishes returned exact
; records.  The receipt authorization boolean names the selected local
; trusted-peer observation profile, not a cryptographic verification claim.
(defun fn-workflow-undertake-record (work-id charge state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bprl-undertake-record
         (f-get-global 'fn-workflow-state state) work-id charge)))

(defun fn-workflow-receipt-record
  (octets txid generation authorizedp state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bprl-receipt-intent-record
         (f-get-global 'fn-workflow-state state)
         octets txid generation authorizedp)))

(defun fn-workflow-release-record (receipt-id state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bprl-release-record-for-journal
         (f-get-global 'fn-workflow-state state) receipt-id)))

(defun fn-workflow-preflight-record (record state)
 (declare (xargs :stobjs state :mode :program))
 (let ((answer (fn-bprl-apply-journal-record
                (f-get-global 'fn-workflow-state state) record)))
  (value (if (car answer) :ready :fault))))

(defun fn-workflow-preflight-history (records state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((sn (f-get-global 'fn-store-sn state))
        (node (and sn (fn-sn-node sn)))
        (answer (fn-bprl-replay-journal node records)))
  (value (if (car answer) :ready :fault))))

(defun fn-workflow-apply-record (record state)
 (declare (xargs :stobjs state :mode :program))
 (let ((answer (fn-bprl-apply-journal-record
                (f-get-global 'fn-workflow-state state) record)))
  (if (not (car answer)) (value :fault)
   (let ((state (f-put-global 'fn-workflow-state
                              (fn-bp-journal-nth 1 answer) state)))
    ; These effects belong only to this just-durable operation.  Disk replay
    ; effects remain historical and are never returned through this gate.
    (let ((state (f-put-global 'fn-workflow-effects
                               (fn-bp-journal-nth 2 answer) state)))
     (value :ready))))))
(defun fn-workflow-fencedp (state)
 (declare (xargs :stobjs state :mode :program))
 (value (if (fn-bp-state-fenced (f-get-global 'fn-workflow-state state)) t nil)))
(defun fn-workflow-work-status (work-id state)
 (declare (xargs :stobjs state :mode :program))
 ; ACL2 owns the projection; this reports it.  :absent means no such work in
 ; the installed image, never "enqueued but not yet attempted".
 (value (fn-bp-work-status work-id
         (fn-bp-state-works (f-get-global 'fn-workflow-state state)))))

; Provenance is a second question and a second answer.  Two works can both be
; :outstanding and have reached the image by materially different routes;
; ACL2 decides which, from the id list the install recorded.
(defun fn-workflow-work-origin (work-id state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bp-work-origin work-id
         (f-get-global 'fn-workflow-recovered state)
         (fn-bp-state-works (f-get-global 'fn-workflow-state state)))))

(defun fn-workflow-take-submit (work-id attempt-id generation state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((effects (f-get-global 'fn-workflow-effects state))
        (effect (and (consp effects) (car effects))))
  (if (and (equal (len effects) 1) (equal (fn-bp-journal-nth 0 effect) :submit)
           (equal (fn-bp-journal-nth 1 effect) work-id)
           (equal (fn-bp-journal-nth 2 effect) attempt-id)
           (equal (fn-bp-journal-nth 3 effect) generation))
      (let ((state (f-put-global 'fn-workflow-effects nil state))) (value t))
    (value nil))))
