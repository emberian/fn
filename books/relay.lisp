; fn relay undertaking: a relay node is receiver-then-sender (wave 2, packet B;
; C2-07, D12).
;
; Composed state over the two existing machines' public entry points only:
; the receiver's fn-bpr-accept-request / fn-bpr-prepare-receipt /
; fn-bpr-commit-receipt / fn-bpr-receipt-adu and the sender's fn-bp-step.
; The Store is an input, as it is to the receiver; the relay's node is the
; sender's node image, which fn-relay-statep pins to the Store's node.
;
; The undertaking rule (RET-001, RET-003, C2-07): a receipt whose terms
; promise onward forwarding may be prepared only when
;   (a) the content is durably accepted in the relay's Store: the node holds
;       the committed article/archive binding the request context names, and
;   (b) a durable onward work item exists, bound to that content, and the
;       relay has durably recorded which onward work backs which promise.
; An archival-only receipt needs (a) alone and promises no forwarding.  The
; relay never emits destination-application acceptance: its terms table has
; no such kind (fn-relay-kindp).
;
; Crash argument (books/relay-invariants.lisp): every transition, and
; fn-relay-crash-recover for every receiver outcome and sender recovery
; result, preserves fn-relay-invp, which says every committed or pending
; forwarding receipt has its recorded onward work present in the sender's
; durable works.  Partial cross-journal completion therefore recovers to no
; promise or to a promise with its obligation, never a promise alone.

(in-package "ACL2")
(include-book "bp-receipt")
(include-book "bp-workflow-binding-invariants")
(include-book "assumptions")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

; -----------------------------------------------------------------------------
; Terms table: what a terms identifier promises at this relay.

(defun fn-relay-kindp (k)
  (declare (xargs :guard t))
  (or (equal k :archived) (equal k :forwarding)))

(defun fn-relay-terms-tablep (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (consp (car xs))
           (stringp (car (car xs)))
           (fn-relay-kindp (cdr (car xs)))
           (fn-relay-terms-tablep (cdr xs)))
    (null xs)))

(defun fn-relay-terms-kind (terms-id table)
  (declare (xargs :guard t))
  (if (consp table)
      (if (and (consp (car table)) (equal terms-id (car (car table))))
          (cdr (car table))
        (fn-relay-terms-kind terms-id (cdr table)))
    nil))

; -----------------------------------------------------------------------------
; Undertakings: which onward work backs which upstream promise.

(defun fn-relay-undertaking-upstream (x) (declare (xargs :guard t)) (fn-bp-nth 0 x))
(defun fn-relay-undertaking-onward (x) (declare (xargs :guard t)) (fn-bp-nth 1 x))
(defun fn-relay-make-undertaking (upstream onward)
  (declare (xargs :guard t))
  (list upstream onward))
(defun fn-relay-undertaking-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (true-listp (car xs)) (equal (len (car xs)) 2)
           (stringp (fn-relay-undertaking-upstream (car xs)))
           (stringp (fn-relay-undertaking-onward (car xs)))
           (fn-relay-undertaking-listp (cdr xs)))
    (null xs)))
(defun fn-relay-find-undertaking (upstream xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal upstream (fn-relay-undertaking-upstream (car xs)))
          (car xs)
        (fn-relay-find-undertaking upstream (cdr xs)))
    nil))

; -----------------------------------------------------------------------------
; State: (store receiver sender terms undertakings)

(defun fn-relay-store (rs) (declare (xargs :guard t)) (fn-bp-nth 0 rs))
(defun fn-relay-receiver (rs) (declare (xargs :guard t)) (fn-bp-nth 1 rs))
(defun fn-relay-sender (rs) (declare (xargs :guard t)) (fn-bp-nth 2 rs))
(defun fn-relay-terms (rs) (declare (xargs :guard t)) (fn-bp-nth 3 rs))
(defun fn-relay-undertakings (rs) (declare (xargs :guard t)) (fn-bp-nth 4 rs))
(defun fn-relay-make-state (store receiver sender terms undertakings)
  (declare (xargs :guard t))
  (list store receiver sender terms undertakings))
(defun fn-relay-node (rs)
  (declare (xargs :guard t))
  (fn-bp-state-node (fn-relay-sender rs)))

(defun fn-relay-statep (rs)
  (declare (xargs :guard t :verify-guards nil))
  (and (true-listp rs) (equal (len rs) 5)
       (fn-bp-binding-statep (fn-relay-sender rs))
       (equal (fn-bp-state-node (fn-relay-sender rs))
              (fn-sn-node (fn-relay-store rs)))
       (fn-relay-terms-tablep (fn-relay-terms rs))
       (fn-relay-undertaking-listp (fn-relay-undertakings rs))))

(defun fn-relay-initial-state (store receiver-config sender-config terms)
  (declare (xargs :guard t :verify-guards nil))
  (fn-relay-make-state store
                       (fn-bpr-initial-state receiver-config)
                       (fn-bp-initial-state (fn-sn-node store) sender-config)
                       terms nil))

; -----------------------------------------------------------------------------
; The two durable facts a promise rests on

; (a) The node holds the committed article/archive binding the context names.
(defun fn-relay-content-durablep (node ctx)
  (declare (xargs :guard t :verify-guards nil))
  (let ((binding (fn-node-find-binding (fn-bpr-context-msgid ctx)
                                       (fn-node-bindings node))))
    (and (consp binding)
         (equal (fn-node-binding-subject binding) (fn-bpr-context-subject ctx))
         (equal (fn-node-binding-id binding) (fn-bpr-context-archive-id ctx)))))

; (b) A durable onward work exists (present in the sender's durable works).
(defun fn-relay-onward-presentp (sender onward-id)
  (declare (xargs :guard t))
  (consp (fn-bp-find-work onward-id (fn-bp-state-works sender))))

; (b'), checked when the undertaking is recorded: that work names the very
; content the context names.
(defun fn-relay-onward-durablep (sender onward-id ctx)
  (declare (xargs :guard t :verify-guards nil))
  (let ((work (fn-bp-find-work onward-id (fn-bp-state-works sender))))
    (and (consp work)
         (equal (fn-bp-work-msgid work) (fn-bpr-context-msgid ctx))
         (equal (fn-bp-work-subject work) (fn-bpr-context-subject ctx))
         (equal (fn-bp-work-archive-id work) (fn-bpr-context-archive-id ctx)))))

; -----------------------------------------------------------------------------
; Transitions

; Receiver side: exactly fn-bpr-accept-request.  Result: (tag state).
(defun fn-relay-accept (rs record request policy-authorizedp)
  (declare (xargs :guard t :verify-guards nil))
  (let ((answer (fn-bpr-accept-request (fn-relay-receiver rs) (fn-relay-store rs)
                                       record request policy-authorizedp)))
    (list (car answer)
          (fn-relay-make-state (fn-relay-store rs) (car (cdr answer))
                               (fn-relay-sender rs) (fn-relay-terms rs)
                               (fn-relay-undertakings rs)))))

; Sender side: exactly fn-bp-step.  Result: (state effects).
(defun fn-relay-sender-step (rs event)
  (declare (xargs :guard t :verify-guards nil))
  (let ((answer (fn-bp-step (fn-relay-sender rs) event)))
    (list (fn-relay-make-state (fn-relay-store rs) (fn-relay-receiver rs)
                               (fn-bp-result-state answer)
                               (fn-relay-terms rs) (fn-relay-undertakings rs))
          (fn-bp-result-effects answer))))

; Durably record which onward work backs an upstream context.  Refused
; without (a), without (b'), for an unknown context, or twice.  This is the
; proposed FNWF record (:relay-undertaking upstream-work-id onward-work-id).
(defun fn-relay-record-undertaking (rs upstream onward)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ctx (fn-bpr-find-context upstream
                                  (fn-bpr-state-contexts (fn-relay-receiver rs)))))
    (if (or (not (fn-relay-statep rs))
            (not (consp ctx))
            (not (stringp upstream))
            (not (stringp onward))
            (consp (fn-relay-find-undertaking upstream (fn-relay-undertakings rs)))
            (not (fn-relay-content-durablep (fn-relay-node rs) ctx))
            (not (fn-relay-onward-durablep (fn-relay-sender rs) onward ctx)))
        rs
      (fn-relay-make-state (fn-relay-store rs) (fn-relay-receiver rs)
                           (fn-relay-sender rs) (fn-relay-terms rs)
                           (cons (fn-relay-make-undertaking upstream onward)
                                 (fn-relay-undertakings rs))))))

; Prepare the typed receipt intent.  Result: (kind state); kind is nil on
; refusal, :archived or :forwarding otherwise.  The receiver's own refusals
; (unauthorized, duplicate receipt, pending intent, unknown context) show as
; an unchanged receiver and are refused here too.
(defun fn-relay-undertake (rs upstream receipt-id policy-authorizedp)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((receiver (fn-relay-receiver rs))
         (ctx (fn-bpr-find-context upstream (fn-bpr-state-contexts receiver)))
         (kind (fn-relay-terms-kind (fn-bpr-context-terms-id ctx)
                                    (fn-relay-terms rs)))
         (u (fn-relay-find-undertaking upstream (fn-relay-undertakings rs))))
    (if (or (not (fn-relay-statep rs))
            (not (consp ctx))
            (not (fn-relay-kindp kind))
            (not (fn-relay-content-durablep (fn-relay-node rs) ctx))
            (and (equal kind :forwarding)
                 (or (not (consp u))
                     (not (fn-relay-onward-presentp
                           (fn-relay-sender rs)
                           (fn-relay-undertaking-onward u))))))
        (list nil rs)
      (let ((next (fn-bpr-prepare-receipt receiver upstream receipt-id
                                          policy-authorizedp)))
        (if (equal next receiver)
            (list nil rs)
          (list kind
                (fn-relay-make-state (fn-relay-store rs) next
                                     (fn-relay-sender rs) (fn-relay-terms rs)
                                     (fn-relay-undertakings rs))))))))

; Exactly fn-bpr-commit-receipt.
(defun fn-relay-commit-receipt (rs upstream receipt-id outcome)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-relay-statep rs))
      rs
    (fn-relay-make-state (fn-relay-store rs)
                         (fn-bpr-commit-receipt (fn-relay-receiver rs)
                                                upstream receipt-id outcome)
                         (fn-relay-sender rs) (fn-relay-terms rs)
                         (fn-relay-undertakings rs))))

; The typed receipt: (kind receipt) once committed, nil otherwise.  The
; receipt bytes come from fn-bpr-receipt-adu as before; the kind is what the
; relay's terms table says its terms promise.
(defun fn-relay-receipt (rs upstream)
  (declare (xargs :guard t :verify-guards nil))
  (let ((entry (fn-bpr-find-receipt upstream
                                    (fn-bpr-state-receipts (fn-relay-receiver rs)))))
    (if (consp entry)
        (list (fn-relay-terms-kind
               (fn-bpr-context-terms-id (fn-bpr-receipt-entry-context entry))
               (fn-relay-terms rs))
              (fn-bpr-receipt-entry-receipt entry))
      nil)))

(defun fn-relay-receipt-adu (rs request)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bpr-receipt-adu (fn-relay-receiver rs) request))

; -----------------------------------------------------------------------------
; Crash then replay, over both journals.
;
; The receiver journal replays to its durable contexts and receipts; a receipt
; intent with no outcome is resolved by inspecting the published receipt
; (fn-bpr-commit-receipt with :committed or :absent).  The sender journal
; replays through fn-bp-restart, which fences any pending intent, and the
; fenced intent is resolved by fn-bp-recover with :committed or :absent.  The
; undertakings ledger is durable before any receipt intent that relies on it.
; Every combination of the two outcomes is one crash-and-recovery of the relay.

(defun fn-relay-crash-recover (rs receiver-outcome sender-result)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((receiver (fn-relay-receiver rs))
         (pending (fn-bpr-state-pending receiver))
         (receiver1
          (if (consp pending)
              (fn-bpr-commit-receipt
               receiver
               (fn-bpr-context-work-id (fn-bpr-receipt-entry-context pending))
               (fn-bpa-receipt-id (fn-bpr-receipt-entry-receipt pending))
               receiver-outcome)
            receiver))
         (sender1 (fn-bp-result-state
                   (fn-bp-step (fn-relay-sender rs) (fn-bp-restart-event))))
         (sender2
          (if (consp (fn-bp-state-pending sender1))
              (fn-bp-result-state
               (fn-bp-step sender1
                           (fn-bp-storage-recover-event
                            (fn-bp-pending-txid (fn-bp-state-pending sender1))
                            (fn-bp-pending-generation (fn-bp-state-pending sender1))
                            sender-result)))
            sender1)))
    (fn-relay-make-state (fn-relay-store rs) receiver1 sender2
                         (fn-relay-terms rs) (fn-relay-undertakings rs))))

; -----------------------------------------------------------------------------
; The invariant: every promise is backed.

(defun fn-relay-entry-backedp (entry node terms undertakings works)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((ctx (fn-bpr-receipt-entry-context entry))
         (kind (fn-relay-terms-kind (fn-bpr-context-terms-id ctx) terms)))
    (and (fn-relay-kindp kind)
         (fn-relay-content-durablep node ctx)
         (or (equal kind :archived)
             (let ((u (fn-relay-find-undertaking (fn-bpr-context-work-id ctx)
                                                 undertakings)))
               (and (consp u)
                    (consp (fn-bp-find-work (fn-relay-undertaking-onward u)
                                            works))))))))

(defun fn-relay-entries-backedp (entries node terms undertakings works)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (and (fn-relay-entry-backedp (car entries) node terms undertakings works)
           (fn-relay-entries-backedp (cdr entries) node terms undertakings works))
    t))

(defun fn-relay-undertakings-backedp (undertakings works)
  (declare (xargs :guard t))
  (if (consp undertakings)
      (and (consp (fn-bp-find-work (fn-relay-undertaking-onward (car undertakings))
                                   works))
           (fn-relay-undertakings-backedp (cdr undertakings) works))
    t))

(defun fn-relay-invp (rs)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-relay-statep rs)
       (fn-relay-entries-backedp
        (fn-bpr-state-receipts (fn-relay-receiver rs))
        (fn-relay-node rs) (fn-relay-terms rs) (fn-relay-undertakings rs)
        (fn-bp-state-works (fn-relay-sender rs)))
       (or (null (fn-bpr-state-pending (fn-relay-receiver rs)))
           (and (consp (fn-bpr-state-pending (fn-relay-receiver rs)))
                (fn-relay-entry-backedp
                 (fn-bpr-state-pending (fn-relay-receiver rs))
                 (fn-relay-node rs) (fn-relay-terms rs) (fn-relay-undertakings rs)
                 (fn-bp-state-works (fn-relay-sender rs)))))
       (fn-relay-undertakings-backedp (fn-relay-undertakings rs)
                                      (fn-bp-state-works (fn-relay-sender rs)))))
