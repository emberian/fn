; Program-mode bridge: decoded bounded local records enter the executable model.
(in-package "ACL2")
; D61: the image attaches these (attach-stobj) before the generic they implement;
; a certified host file carries the same order in its own world (tools/host_check.py --attach-order).
(include-book "../books/payload-arena")
(include-book "../books/owner-retain-state")
(include-book "../books/history-columns")
(include-book "../books/bp-workflow-constructors")
(include-book "../books/bp-ion-workflow")
(include-book "../books/bp-ion-lifetime")
(include-book "../books/bp-request-plan")
(include-book "../books/bp-payload-gate")
; PKT-869: the operator's carry control and its journal's frame.
(include-book "../books/bp-carry-control")
(include-book "../books/bp-carry-frame")
; `fn-sn-node' is books/store-node's; include it rather than depend on a
; store session having been opened in this ACL2 first.
(include-book "../books/store-node")
(include-book "../books/definterface")
(include-book "store-host")
(local (in-theory (enable adt-nth-0 adt-nth-1+)))

; The workflow entries that form a request read the article's octets through
; the live payload arena (books/bp-outbound.lisp; the records flip): each takes
; fn-arena before state, only reads it, and returns (mv erp val state), so
; host/native/io.lisp fnn-core-state passes the live arena (fnn-trailing-kind).
; The BP snapshot has its own pin trie in both images. Store gates keep
; their own lineage; this is separate from the operator carry overlay.
(defun fn-workflow-pin-carry-of (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-workflow-pin-carry state)
      (f-get-global 'fn-workflow-pin-carry state) nil))

(defun fn-workflow-pin-carry-put (pin-carry state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-workflow-pin-carry pin-carry state))

(defthm fn-workflow-pin-carry-put-preserves-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-workflow-pin-carry-put pin-carry state)))
  :hints (("Goal" :in-theory (e/d (fn-workflow-pin-carry-put) (state-p1)))))

(defthm fn-workflow-pin-carry-put-frames-global-association
  (implies (not (equal key 'fn-workflow-pin-carry))
           (equal (assoc-equal key (nth 2 (fn-workflow-pin-carry-put pin-carry state)))
                  (assoc-equal key (nth 2 state))))
  :hints (("Goal" :in-theory (enable fn-workflow-pin-carry-put put-global))))

; Standalone canonical Store cache: never refreshed against the BP node.
(defun fn-workflow-store-pin-carry-of (state)
  (declare (xargs :stobjs state :guard t))
  (if (boundp-global 'fn-workflow-store-pin-carry state)
      (f-get-global 'fn-workflow-store-pin-carry state) nil))

(defun fn-workflow-store-pin-carry-put (pin-carry state)
  (declare (xargs :stobjs state :guard t))
  (f-put-global 'fn-workflow-store-pin-carry pin-carry state))

(defthm fn-workflow-store-pin-carry-put-preserves-state-p1
  (implies (state-p1 state)
           (state-p1 (fn-workflow-store-pin-carry-put pin-carry state)))
  :hints (("Goal" :in-theory (e/d (fn-workflow-store-pin-carry-put) (state-p1)))))

(defthm fn-workflow-store-pin-carry-put-frames-global-association
  (implies (not (equal key 'fn-workflow-store-pin-carry))
           (equal (assoc-equal key (nth 2 (fn-workflow-store-pin-carry-put pin-carry state)))
                  (assoc-equal key (nth 2 state))))
  :hints (("Goal" :in-theory (enable fn-workflow-store-pin-carry-put put-global))))


(defun fn-workflow-install-replay (records fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  ; Replay is cold: pass the carry unchanged; install anchors it to the
  ; resulting BP ledger, which may differ from the Store seed.
  (let* ((pin-carry (fn-workflow-pin-carry-of state))
         (answer (fn-bpiw-replay-journal (fn-sn-node (f-get-global 'fn-store-sn state)) records pin-carry fn-arena)))
    (if (not (car answer))
        (value :fault)
      (let* ((workflow (fn-bp-journal-nth 1 answer))
             ; Pay the standalone Store trie's initial build during cold
             ; installation, before the first served ION canonical gate.
             (state (fn-workflow-store-pin-carry-put
                     (fn-prc-refresh (fn-workflow-store-pin-carry-of state)
                       (fn-node-retention (fn-sn-node (f-get-global 'fn-store-sn state))))
                     state))
             (state (f-put-global 'fn-workflow-state workflow state))
             (state (fn-workflow-pin-carry-put
                     (fn-prc-refresh pin-carry
                       (fn-node-retention (fn-bp-state-node workflow))) state))
             (state (f-put-global 'fn-workflow-ion-state
                                  (fn-bp-journal-nth 3 answer) state))
             (state (f-put-global 'fn-workflow-effects nil state))
             (state (f-put-global 'fn-workflow-recovered
                                  (fn-bp-work-ids (fn-bp-state-works workflow)) state)))
        (value :ready)))))

(definterface fn-workflow-install-replay :class :program)

(defun fn-workflow-state (state)
 (declare (xargs :stobjs state :mode :program))
 (value (f-get-global 'fn-workflow-state state)))

(defun fn-workflow-reset (state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((pin-carry (fn-workflow-pin-carry-of state))
         ; An empty standalone journal opens through reset, not replay.
         ; The owner's reset delegate leaves the standalone Store cache alone.
         (state (if (and (not (boundp-global 'fn-owner state))
                         (boundp-global 'fn-store-sn state))
                    (fn-workflow-store-pin-carry-put
                     (fn-prc-refresh (fn-workflow-store-pin-carry-of state)
                       (fn-node-retention (fn-sn-node (f-get-global 'fn-store-sn state))))
                     state)
                  state))
         (state (f-put-global 'fn-workflow-state nil state))
         (state (fn-workflow-pin-carry-put
                 (fn-prc-refresh pin-carry (fn-node-retention (fn-bp-state-node nil))) state))
         (state (f-put-global 'fn-workflow-ion-state (fn-bpiw-initial) state))
         (state (f-put-global 'fn-workflow-effects nil state))
         (state (f-put-global 'fn-workflow-recovered nil state)))
    (value :ready)))

(definterface fn-workflow-reset :class :program)
(defun fn-workflow-effects (state)
 (declare (xargs :stobjs state :mode :program))
 (value (f-get-global 'fn-workflow-effects state)))

(defun fn-workflow-valid-config (record)
  ; Read-only validation for the first record.  Installation happens only
  ; after the native publication machine reports :durable.
  (if (fn-bp-config-recordp record) t nil))

(definterface fn-workflow-valid-config
  :class ::ideal)

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

(definterface fn-workflow-enqueue-record
  :class ::program)

; Constructors return nil on refusal; raw Lisp only publishes returned exact
; records.  The receipt authorization boolean names the selected local
; trusted-peer observation profile, not a cryptographic verification claim.
(defun fn-workflow-undertake-record (work-id charge state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((pin-carry (fn-workflow-pin-carry-of state)))
  (value (fn-bprl-undertake-record
         (f-get-global 'fn-workflow-state state) work-id charge pin-carry))))

(definterface fn-workflow-undertake-record
  :class ::program)

; PKT-869: the carry overlay the carry journal replayed (fn-workflow-carry-
; install below), or the empty overlay when no carry journal is installed.
(defun fn-workflow-carry-state-of (state)
  (declare (xargs :stobjs state :guard t))
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

(definterface fn-workflow-receipt-record
  :class ::program
  :kinds ((octets fn-cbor-octet-listp)))

(defun fn-workflow-release-record (receipt-id state)
 (declare (xargs :stobjs state :mode :program))
 (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (value (fn-bprl-release-record-for-journal
         (f-get-global 'fn-workflow-state state) receipt-id pin-carry))))

(definterface fn-workflow-release-record
  :class ::program)

(defun fn-workflow-preflight-record (record fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (let ((answer (fn-bpiw-apply
                (f-get-global 'fn-workflow-state state)
                (f-get-global 'fn-workflow-ion-state state) record pin-carry fn-arena)))
  (value (if (car answer) :ready :fault)))))

(definterface fn-workflow-preflight-record :class :program)

(defun fn-workflow-preflight-history (records fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let* ((pin-carry (fn-workflow-pin-carry-of state)))
  (let* ((sn (f-get-global 'fn-store-sn state))
        (node (and sn (fn-sn-node sn)))
        (answer (fn-bpiw-replay-journal node records pin-carry fn-arena)))
  (value (if (car answer) :ready :fault)))))

(defun fn-workflow-apply-record (record fn-arena state)
 (declare (xargs :stobjs (fn-arena state) :mode :program))
 (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (let ((answer (fn-bpiw-apply
                (f-get-global 'fn-workflow-state state)
                (f-get-global 'fn-workflow-ion-state state) record pin-carry fn-arena)))
  (if (not (car answer)) (value :fault)
   (let ((state (f-put-global 'fn-workflow-state
                              (fn-bp-journal-nth 1 answer) state)))
    ; These effects belong only to this just-durable operation.  Disk replay
    ; effects remain historical and are never returned through this gate.
    (let ((state (f-put-global 'fn-workflow-effects
                               (fn-bp-journal-nth 2 answer) state)))
     (let ((state (f-put-global 'fn-workflow-ion-state
                                (fn-bp-journal-nth 3 answer) state)))
      (value :ready))))))))

(definterface fn-workflow-apply-record :class :program)
(defun fn-workflow-fencedp (state)
 (declare (xargs :stobjs state :mode :program))
 (value (if (fn-bp-state-fenced (f-get-global 'fn-workflow-state state)) t nil)))

(definterface fn-workflow-fencedp
  :class ::program)
(defun fn-workflow-work-status (work-id state)
 (declare (xargs :stobjs state :mode :program))
 ; ACL2 owns the projection; this reports it.  :absent means no such work in
 ; the installed image, never "enqueued but not yet attempted".
 (value (fn-bp-work-status work-id
         (fn-bp-state-works (f-get-global 'fn-workflow-state state)))))

(definterface fn-workflow-work-status
  :class ::program)

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

(definterface fn-workflow-take-submit
  :class ::program)


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

(definterface fn-workflow-carry-install
  :class ::program)

(defun fn-workflow-carry-preflight (record state)
  (declare (xargs :stobjs state :mode :program))
  (value (if (or (fn-bpcc-configp record)
                 (fn-bpcc-admissiblep (f-get-global 'fn-workflow-state state)
                                      (fn-workflow-carry-state-of state) record))
             :ready :fault)))

(definterface fn-workflow-carry-preflight
  :class ::program)

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

(definterface fn-workflow-carry-apply
  :class ::program)

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
(defun fn-workflow-request-plan-with-pin-carry
    (work-id attempt-id pin-carry fn-arena state)
  (declare (xargs :stobjs (fn-arena state)
                  :guard (boundp-global 'fn-workflow-state state)))
  ; Generated retry/attempt/outcome branches do not query pins. The owner
  ; canonical gate can reuse the carry it has already read for its plan.
  (value (fn-bpcc-request-gate
          (fn-workflow-carry-state-of state) work-id
          (fn-bprq-plan (f-get-global 'fn-workflow-state state)
                        work-id attempt-id pin-carry fn-arena))))

(defun fn-workflow-request-plan (work-id attempt-id fn-arena state)
  (declare (xargs :stobjs (fn-arena state)
                  :guard (boundp-global 'fn-workflow-state state)))
  (fn-workflow-request-plan-with-pin-carry
   work-id attempt-id (fn-workflow-pin-carry-of state) fn-arena state))

; PKT-869: the operator's carry control.  VERB is :pause, :resume, :drop or
; :abandon (`drop WORK --abandon', PRF-950: the waiver, whose principal is
; ACL2's rendering of the effective UID the host read); the answer is the
; exact record to publish, or (:refused REASON), ACL2's
; (books/bp-carry-control.lisp fn-bpcc-refusal, and for a waiver
; fn-bpcc-waiver-refusal, which needs the pin held, over the installed image).
(defun fn-workflow-carry-record (verb work-id reason uid state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
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
                                                 record pin-carry))
                        (t (fn-bpcc-refusal (f-get-global 'fn-workflow-state state)
                                            (fn-workflow-carry-state-of state)
                                            record)))))
    (value (if refusal (list :refused refusal) (list :record record))))))

(definterface fn-workflow-carry-record
  :class ::program)

; PKT-869: `carry list' (WORK-ID nil) or `carry inspect WORK-ID': ACL2's
; report octets, each work's pin read from the Store image the owner holds.
(defun fn-workflow-carry-pinned (workflow works acc pin-carry)
  (declare (xargs :mode :program))
  (if (consp works)
      (fn-workflow-carry-pinned
       workflow (cdr works)
       (if (fn-bprl-work-pinnedp workflow (car works) pin-carry)
           (cons (fn-bp-work-id (car works)) acc)
         acc) pin-carry)
    acc))

(defun fn-workflow-carry-report (work-id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((pin-carry (fn-prc-refresh (fn-workflow-pin-carry-of state)
                         (fn-node-retention (fn-bp-state-node (f-get-global 'fn-workflow-state state)))))
        (state (fn-workflow-pin-carry-put pin-carry state)))
  (let* ((workflow (f-get-global 'fn-workflow-state state))
         (carry (fn-workflow-carry-state-of state))
         (pinned (fn-workflow-carry-pinned workflow (fn-bp-state-works workflow) nil pin-carry)))
    (value (if work-id
               (fn-bpcc-inspect-report workflow carry pinned work-id)
             (fn-bpcc-list-report workflow carry pinned))))))

(definterface fn-workflow-carry-report
  :class ::program)

; `bp-obligation recover': ACL2's decision for a fenced attempt, (:recover
; RECORD) or (:refused REASON) (books/bp-request-plan.lisp; keystone
; fn-bprq-recovery-plan-unfences-and-reopens-as-live, books/bp-request-recovery.lisp).
(defun fn-workflow-recovery-plan (work-id attempt-id outcome state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((pin-carry (fn-workflow-pin-carry-of state)))
  (value (fn-bprq-recovery-plan (f-get-global 'fn-workflow-state state)
                                work-id attempt-id outcome pin-carry))))

(definterface fn-workflow-recovery-plan
  :class ::program)

; The ION sender's (RETRY ATTEMPT): the journaled retry request first when a
; reopen marked the last attempt :restart-observed, so replay agrees.
;; Through the payload gate (books/bp-payload-gate.lisp
;; fn-bppg-ion-gates-send-only-pinned-live-payload): the canonical node is the
;; opened Store's, so an FNWF-local undertaking does not admit an attempt.
; The host must call this before publishing retry/attempt/route records.
; An unrepresentable lifetime is a pre-attempt refusal, never uncertainty.
(defun fn-workflow-ion-helper-seconds (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bpit-helper-seconds
          (fn-bp-config-lifetime
           (fn-bp-state-config (f-get-global 'fn-workflow-state state))))))

(definterface fn-workflow-ion-helper-seconds
  :class ::program)

(defun fn-workflow-ion-attempt-plan
    (txid tx-generation work-id attempt-id fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let* ((pin-carry (fn-prc-refresh (fn-workflow-store-pin-carry-of state)
                         (fn-node-retention (fn-sn-node (f-get-global 'fn-store-sn state)))))
        (state (fn-workflow-store-pin-carry-put pin-carry state)))
  (let* ((s (f-get-global 'fn-workflow-state state))
         (sn (f-get-global 'fn-store-sn state)))
    (value (fn-bppg-ion-attempt-gate
            (and sn (fn-sn-node sn)) s work-id
            (fn-bprq-ion-attempt-plan s txid tx-generation work-id attempt-id (fn-workflow-pin-carry-of state))
            pin-carry fn-arena)))))

(definterface fn-workflow-ion-attempt-plan
  :class ::program)

; Native ION sender calls these exact ACL2 constructors. Raw Lisp only
; publishes their returned records and executes their returned ADU bytes.
; ION is an adapter of the generic attempt: its attempt record is
; fn-bprq-attempt-record (books/bp-request-plan.lisp).
(defun fn-workflow-ion-attempt-record
    (txid tx-generation work-id attempt-id state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((pin-carry (fn-workflow-pin-carry-of state)))
  (value (fn-bprq-attempt-record
          (f-get-global 'fn-workflow-state state)
          txid tx-generation work-id attempt-id pin-carry))))

(defun fn-workflow-ion-route-record
    (work-id attempt-id generation bp-destination own-bp-eid fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-bpiw-route-record
          (f-get-global 'fn-workflow-state state)
          (f-get-global 'fn-workflow-ion-state state)
          work-id attempt-id generation bp-destination own-bp-eid fn-arena)))

(definterface fn-workflow-ion-route-record
  :class ::program)

(defun fn-workflow-ion-observation-record
    (work-id attempt-id generation bp-destination own-bp-eid raw fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (value (fn-bpiw-observation-record
          (f-get-global 'fn-workflow-state state)
          (f-get-global 'fn-workflow-ion-state state)
          work-id attempt-id generation bp-destination own-bp-eid
          (fn-record-octets-string raw) fn-arena)))

(definterface fn-workflow-ion-observation-record
  :class ::program)

(defun fn-workflow-ion-request-adu
    (work-id attempt-id generation fn-arena state)
  (declare (xargs :stobjs (fn-arena state) :mode :program))
  (let ((result (fn-bpo-request-adu
                 (f-get-global 'fn-workflow-state state)
                 work-id attempt-id generation fn-arena)))
    ;; An octet list, or the refusal's name: :request-refused (no request
    ;; for this attempt) or :article-reclaimed (it would carry a reclaim
    ;; tombstone, books/bp-payload-gate.lisp fn-bppg-ion-adu).
    (value (cond ((not (fn-bpo-result-okp result)) :request-refused)
                 ((fn-bppg-ion-adu (fn-bpo-result-value result))
                  (fn-bpo-result-value result))
                 (t :article-reclaimed)))))

(definterface fn-workflow-ion-request-adu
  :class ::program)

(defun fn-workflow-ion-status (work-id attempt-id generation state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-bpiw-status (f-get-global 'fn-workflow-ion-state state)
                         work-id attempt-id generation)))

(definterface fn-workflow-ion-status
  :class ::program)
