; Program-mode bridge: decoded bounded local records enter the executable model.
(in-package "ACL2")
(include-book "../books/bp-workflow-constructors")
(include-book "../books/bp-ion-workflow")
(include-book "../books/bp-request-plan")
; PKT-869: the operator's carry control and its journal's frame.
(include-book "../books/bp-carry-control")
(include-book "../books/bp-carry-frame")
; `fn-sn-node' is books/store-node's; include it rather than depend on a
; store session having been opened in this ACL2 first.
(include-book "../books/store-node")

; The workflow entries that form a request read the article's octets through
; the live payload arena (books/bp-outbound.lisp; the records flip): each takes
; fn-arena before state, only reads it, and returns (mv erp val state), so
; host/native/io.lisp fnn-core-state passes the live arena (fnn-trailing-kind).
(defun fn-workflow-install-replay (records fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let* ((sn (f-get-global 'fn-store-sn state))
        (node (and sn (fn-sn-node sn)))
        (answer (fn-bpiw-replay-journal node records fn-arena)))
  (if (car answer)
      (let ((state (f-put-global 'fn-workflow-state (fn-bp-journal-nth 1 answer) state)))
       (let ((state (f-put-global 'fn-workflow-ion-state
                                  (fn-bp-journal-nth 3 answer) state)))
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
         (value :ready)))))
    (value :fault))))

(defun fn-workflow-state (state)
 (declare (xargs :stobjs state :mode :program))
 (value (f-get-global 'fn-workflow-state state)))

(defun fn-workflow-reset (state)
 (declare (xargs :stobjs state :mode :program))
 (let ((state (f-put-global 'fn-workflow-state nil state)))
  (let ((state (f-put-global 'fn-workflow-ion-state (fn-bpiw-initial) state)))
  (let ((state (f-put-global 'fn-workflow-effects nil state)))
   (let ((state (f-put-global 'fn-workflow-recovered nil state)))
    (value :ready))))))
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

; PKT-869: the carry overlay the carry journal replayed (fn-workflow-carry-
; install below), or the empty overlay when no carry journal is installed.
(defun fn-workflow-carry-state-of (state)
  (declare (xargs :stobjs state :mode :program))
  (if (boundp-global 'fn-workflow-carry-state state)
      (f-get-global 'fn-workflow-carry-state state)
    (fn-bpcc-initial)))

;; PRF-950: a receipt for a work the operator waived is refused by name
;; (books/bp-carry-control.lisp fn-bpcc-receipt-gate): the waiver released
;; its obligation.  With no carry journal installed the overlay is empty.
(defun fn-workflow-receipt-record
  (octets txid generation authorizedp state)
 (declare (xargs :stobjs state :mode :program
                  :guard (fn-cbor-octet-listp octets)))
 (value (fn-bpcc-receipt-gate
         (fn-workflow-carry-state-of state)
         (fn-bprl-receipt-intent-record
          (f-get-global 'fn-workflow-state state)
          octets txid generation authorizedp))))

(defun fn-workflow-release-record (receipt-id state)
 (declare (xargs :stobjs state :mode :program))
 (value (fn-bprl-release-record-for-journal
         (f-get-global 'fn-workflow-state state) receipt-id)))

(defun fn-workflow-preflight-record (record fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let ((answer (fn-bpiw-apply
                (f-get-global 'fn-workflow-state state)
                (f-get-global 'fn-workflow-ion-state state) record fn-arena)))
  (value (if (car answer) :ready :fault))))

(defun fn-workflow-preflight-history (records fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let* ((sn (f-get-global 'fn-store-sn state))
        (node (and sn (fn-sn-node sn)))
        (answer (fn-bpiw-replay-journal node records fn-arena)))
  (value (if (car answer) :ready :fault))))

(defun fn-workflow-apply-record (record fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let ((answer (fn-bpiw-apply
                (f-get-global 'fn-workflow-state state)
                (f-get-global 'fn-workflow-ion-state state) record fn-arena)))
  (if (not (car answer)) (value :fault)
   (let ((state (f-put-global 'fn-workflow-state
                              (fn-bp-journal-nth 1 answer) state)))
    ; These effects belong only to this just-durable operation.  Disk replay
    ; effects remain historical and are never returned through this gate.
    (let ((state (f-put-global 'fn-workflow-effects
                               (fn-bp-journal-nth 2 answer) state)))
     (let ((state (f-put-global 'fn-workflow-ion-state
                                (fn-bp-journal-nth 3 answer) state)))
      (value :ready)))))))
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


; PKT-869: the carry control journal (domain :carry, JOURNAL/carry): its
; replay, preflight and apply over the workflow image installed first, and
; its frame (books/bp-carry-frame.lisp) with text fields as ACL2 strings.
(defun fn-workflow-carry-install (records state)
  (declare (xargs :stobjs state :mode :program))
  (let ((answer (fn-bpcc-replay (f-get-global 'fn-workflow-state state) records)))
    (if (car answer)
        (let ((state (f-put-global 'fn-workflow-carry-state (cdr answer) state)))
          (value :ready))
      (let ((state (f-put-global 'fn-workflow-carry-state (fn-bpcc-initial) state)))
        (value :fault)))))

(defun fn-workflow-carry-preflight (record state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (or (fn-bpcc-configp record)
                 (fn-bpcc-admissiblep (f-get-global 'fn-workflow-state state)
                                      (fn-workflow-carry-state-of state) record))
             :ready :fault)))

(defun fn-workflow-carry-apply (record state)
  (declare (xargs :stobjs state :mode :program))
  (cond ((fn-bpcc-configp record) (value :ready))
        ((fn-bpcc-admissiblep (f-get-global 'fn-workflow-state state)
                              (fn-workflow-carry-state-of state) record)
         (let ((state (f-put-global 'fn-workflow-carry-state
                                    (fn-bpcc-apply (fn-workflow-carry-state-of state) record)
                                    state)))
           (value :ready)))
        (t (value :fault))))

(defun fn-workflow-carry-frame-protected (kind values)
  (declare (xargs :mode :program))
  (let ((spec (fn-frame-spec-for kind *fn-bpcc-frame-specs*)))
    (if (equal spec :none) :bad
      (fn-bpcc-frame-protected kind (fn-store-frame-logical-to-wire-values spec values)))))

(defun fn-workflow-carry-frame-decode (octets digest)
  (declare (xargs :mode :program))
  (fn-store-frame-logical-result
   (fn-store-frame-record-result (fn-bpcc-frame-decode octets digest))
   *fn-bpcc-frame-specs*))

; The generic native request (`bp-obligation request'): ACL2's whole plan for
; one work, from the attempt record to the request ADU and its destination
; (books/bp-request-plan.lisp, keystone fn-bprq-plan-is-the-works-request).
(defun fn-workflow-request-plan (work-id attempt-id fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  ;; PKT-869: a paused or dropped work's request is refused by name
  ;; (books/bp-carry-control.lisp fn-bpcc-request-gate).
  (value (fn-bpcc-request-gate
          (fn-workflow-carry-state-of state)
          work-id
          (fn-bprq-plan (f-get-global 'fn-workflow-state state)
                        work-id attempt-id fn-arena))))

; PKT-869: the operator's carry control.  VERB is :pause, :resume, :drop or
; :abandon (`drop WORK --abandon', PRF-950: the waiver, whose principal is
; ACL2's rendering of the effective UID the host read); the answer is the
; exact record to publish, or (:refused REASON), ACL2's
; (books/bp-carry-control.lisp fn-bpcc-refusal, and for a waiver
; fn-bpcc-waiver-refusal, which needs the pin held, over the installed image).
(defun fn-workflow-carry-record (verb work-id reason uid state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((record (cond ((eq verb :pause) (list :carry "pause" work-id "-"))
                       ((eq verb :resume) (list :carry "resume" work-id "-"))
                       ((eq verb :drop) (list :carry "drop" work-id reason))
                       ((eq verb :abandon)
                        (list :waive "abandon" work-id reason
                              (fn-bpcc-operator-principal uid)))
                       (t nil)))
         (refusal (cond ((null record) :malformed)
                        ((eq verb :abandon)
                         (fn-bpcc-waiver-refusal (f-get-global 'fn-workflow-state state)
                                                 (fn-workflow-carry-state-of state)
                                                 record))
                        (t (fn-bpcc-refusal (f-get-global 'fn-workflow-state state)
                                            (fn-workflow-carry-state-of state)
                                            record)))))
    (value (if refusal (list :refused refusal) (list :record record)))))

; PKT-869: `carry list' (WORK-ID nil) or `carry inspect WORK-ID': ACL2's
; report octets, each work's pin read from the Store image the owner holds.
(defun fn-workflow-carry-pinned (workflow works acc)
  (declare (xargs :mode :program))
  (if (consp works)
      (fn-workflow-carry-pinned
       workflow (cdr works)
       (if (fn-bprl-work-pinnedp workflow (car works))
           (cons (fn-bp-work-id (car works)) acc)
         acc))
    acc))

(defun fn-workflow-carry-report (work-id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((workflow (f-get-global 'fn-workflow-state state))
         (carry (fn-workflow-carry-state-of state))
         (pinned (fn-workflow-carry-pinned workflow (fn-bp-state-works workflow) nil)))
    (value (if work-id
               (fn-bpcc-inspect-report workflow carry pinned work-id)
             (fn-bpcc-list-report workflow carry pinned)))))

; `bp-obligation recover': ACL2's decision for a fenced attempt, (:recover
; RECORD) or (:refused REASON) (books/bp-request-plan.lisp; keystone
; fn-bprq-recovery-plan-unfences-and-reopens-as-live, books/bp-request-recovery.lisp).
(defun fn-workflow-recovery-plan (work-id attempt-id outcome state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bprq-recovery-plan (f-get-global 'fn-workflow-state state)
                                work-id attempt-id outcome)))

; The ION sender's (RETRY ATTEMPT): the journaled retry request first when a
; reopen marked the last attempt :restart-observed, so replay agrees.
(defun fn-workflow-ion-attempt-plan
    (txid tx-generation work-id attempt-id state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bprq-ion-attempt-plan
          (f-get-global 'fn-workflow-state state)
          txid tx-generation work-id attempt-id)))

; Native ION sender calls these exact ACL2 constructors. Raw Lisp only
; publishes their returned records and executes their returned ADU bytes.
; ION is an adapter of the generic attempt: its attempt record is
; fn-bprq-attempt-record (books/bp-request-plan.lisp).
(defun fn-workflow-ion-attempt-record
    (txid tx-generation work-id attempt-id state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bprq-attempt-record
          (f-get-global 'fn-workflow-state state)
          txid tx-generation work-id attempt-id)))

(defun fn-workflow-ion-route-record
    (work-id attempt-id generation bp-destination own-bp-eid fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-bpiw-route-record
          (f-get-global 'fn-workflow-state state)
          (f-get-global 'fn-workflow-ion-state state)
          work-id attempt-id generation bp-destination own-bp-eid fn-arena)))

(defun fn-workflow-ion-observation-record
    (work-id attempt-id generation bp-destination own-bp-eid raw fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-bpiw-observation-record
          (f-get-global 'fn-workflow-state state)
          (f-get-global 'fn-workflow-ion-state state)
          work-id attempt-id generation bp-destination own-bp-eid
          (fn-record-octets-string raw) fn-arena)))

(defun fn-workflow-ion-request-adu
    (work-id attempt-id generation fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((result (fn-bpo-request-adu
                 (f-get-global 'fn-workflow-state state)
                 work-id attempt-id generation fn-arena)))
    (value (if (fn-bpo-result-okp result)
               (fn-bpo-result-value result) nil))))

(defun fn-workflow-ion-status (work-id attempt-id generation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bpiw-status (f-get-global 'fn-workflow-ion-state state)
                         work-id attempt-id generation)))
