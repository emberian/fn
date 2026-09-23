; fn: executable binding of live node transactions to the file kernel.
(in-package "ACL2")
; store-files-invariants is included because the kernel preservation
; keystones are this book's guard proofs: fn-sn-finish calls
; fn-sf-emit-success on the result of fn-sf-core-completion, and
; fn-sf-core-completion-preserves-state discharges that guard.
(include-book "store-files-invariants")
; stx-index is included for the two fields this record gained on
; 2026-09-21 (decision D21): the served statement index and the keyring it
; was computed under.  The index sits ABOVE books/node -- books/stx-index
; includes books/stx-lace includes books/node, and fn-stx-store IS
; (fn-state-articles (fn-node-acceptance node)) -- so a slot on
; fn-node-statep would be a cycle (w11/node-index).  This record is not in
; books/stx-index's closure, so carrying it here is not.
(include-book "stx-index")
(include-book "records-seam")
(include-book "records-stamp")
; The codecs cluster withdraws the record and codec definitions at export
; (2026-09-19); the proofs here open fn-record-p and the record accessors.
(local (in-theory (enable fn-record-record-vocabulary fn-record-shape-vocabulary)))

; Fixed configuration accompanies the file machine and the actual live node.
; No transition accepts a replacement configuration or a host 'matching' reply.
; Total MBE selectors preserve the original ACL2 values on malformed inputs.
; The composed record is opaque below its lemmas (docs/proof-style.md s1).
; Layout: (groups capacity files node keyring index keyring-generation verdicts
;          historical-keyring-snapshots identity-next-sequence)
; keyring and index were appended, not inserted, so the first four accessors
; keep their positions and their bodies (D21).
(defun fn-sn-shapep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 10)))

(defun fn-sn-groups (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car s)
       :exec (fn-ag-car s)))

(verify-guards fn-sn-groups)
(defun fn-sn-capacity (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr s)
       :exec (fn-ag-car (fn-ag-cdr s))))

(verify-guards fn-sn-capacity)
(defun fn-sn-files (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (caddr s)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr s)))))

(verify-guards fn-sn-files)
(defun fn-sn-node (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadddr s)
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))

(verify-guards fn-sn-node)

; The live Store owns the decision for an already held Message-ID.  The host
; supplies the parsed exact ID, source octets and selected group names; it
; does not compare an article or infer acceptance from a transport result.
; Keep the guard independent of fn-sn-statep: that recognizer walks the store
; and must not run on this served path.
(defun fn-sn-existing-action (msgid payload groups s)
  (declare (xargs :guard t))
  (let ((article (fn-find-article
                  msgid (fn-state-articles
                         (fn-node-acceptance (fn-sn-node s))))))
    (if article
        (if (and (equal payload (fn-article-payload article))
                 (equal groups (fn-article-groups article)))
            :duplicate
          :conflict)
      nil)))

; The keyring the index was computed under.  It is configuration, and it is
; the third piece of configuration this record carries beside groups and
; capacity.  No other state or configuration record in the tree holds one
; (w11/node-index measured it); a keyring reaches ACL2 today only as a file
; the operator names (bin/fn --keyring).  A carried index whose keyring is not
; also carried is not determined by the state, because two keyrings give two
; indexes over one store -- which is why this field exists (D21).
(defun fn-sn-keyring (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cddddr s))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))

(verify-guards fn-sn-keyring)

; The served statement index of books/stx-index.  Its agreement with the lace
; projection is NOT a conjunct of fn-sn-statep: that recognizer is the guard
; of every transition below and the host checks a callee's guard on every call
; (D20), so the agreement there would re-derive the index -- and so re-run
; fn-stx-verdict, and so re-verify every signature in the store -- per host
; call.  The agreement is fn-sn-indexedp, carried and proved preserved (D21).
(defun fn-sn-index (s) (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr (cddddr s))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))))

(verify-guards fn-sn-index)
(defun fn-sn-keyring-generation (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (caddr (cddddr s))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
              (fn-ag-cdr (fn-ag-cdr s)))))))))

(verify-guards fn-sn-keyring-generation)

; Acceptance evidence is newest-first `(msgid . verdict)' pairs.  It is a
; historical observation: changing the current keyring must not rewrite it.
(defun fn-sn-verdicts (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadddr (cddddr s))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s))))))))))

(verify-guards fn-sn-verdicts)

(defun fn-sn-keyring-snapshots (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (car (cddddr (cddddr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr s)))))))))))

(verify-guards fn-sn-keyring-snapshots)

(defun fn-sn-identity-next (s)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (cadr (cddddr (cddddr s)))
       :exec (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
              (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
              (fn-ag-cdr s))))))))))))

(verify-guards fn-sn-identity-next)

(defun fn-sn-keyring-snapshot-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-stxk-p (car xs))
           (fn-sn-keyring-snapshot-listp (cdr xs)))
    (null xs)))

(defun fn-sn-verdict-listp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (consp (car xs))
           (stringp (car (car xs)))
           (member-equal (fn-stx-verdict-token (cdr (car xs)))
                         *fn-stx-verdicts*)
           (natp (fn-stx-verdict-generation (cdr (car xs))))
           (fn-sn-verdict-listp (cdr xs)))
    (null xs)))

(defun fn-sn-make-v2 (groups capacity files node keyring index
                      keyring-generation verdicts snapshots identity-next)
  (declare (xargs :guard t))
  (list groups capacity files node keyring index keyring-generation verdicts
        snapshots identity-next))

(defun fn-sn-make (groups capacity files node keyring index)
  (declare (xargs :guard t))
  (fn-sn-make-v2 groups capacity files node keyring index 0 nil nil 0))

(defthm fn-sn-shapep-of-fn-sn-make-v2
  (fn-sn-shapep (fn-sn-make-v2 groups capacity files node keyring index
                                keyring-generation verdicts snapshots identity-next)))
(defthm fn-sn-groups-of-fn-sn-make-v2
  (equal (fn-sn-groups (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         groups))
(defthm fn-sn-capacity-of-fn-sn-make-v2
  (equal (fn-sn-capacity (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         capacity))
(defthm fn-sn-files-of-fn-sn-make-v2
  (equal (fn-sn-files (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         files))
(defthm fn-sn-node-of-fn-sn-make-v2
  (equal (fn-sn-node (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         node))
(defthm fn-sn-keyring-of-fn-sn-make-v2
  (equal (fn-sn-keyring (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         keyring))
(defthm fn-sn-index-of-fn-sn-make-v2
  (equal (fn-sn-index (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         index))
(defthm fn-sn-keyring-generation-of-fn-sn-make-v2
  (equal (fn-sn-keyring-generation
          (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         keyring-generation))
(defthm fn-sn-verdicts-of-fn-sn-make-v2
  (equal (fn-sn-verdicts
          (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         verdicts))
(defthm fn-sn-keyring-snapshots-of-fn-sn-make-v2
  (equal (fn-sn-keyring-snapshots
          (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         snapshots))
(defthm fn-sn-identity-next-of-fn-sn-make-v2
  (equal (fn-sn-identity-next
          (fn-sn-make-v2 groups capacity files node keyring index keyring-generation verdicts snapshots identity-next))
         identity-next))

(defthm fn-sn-shapep-of-fn-sn-make
  (fn-sn-shapep (fn-sn-make groups capacity files node keyring index)))
(defthm fn-sn-groups-of-fn-sn-make
  (equal (fn-sn-groups (fn-sn-make groups capacity files node keyring index)) groups))
(defthm fn-sn-capacity-of-fn-sn-make
  (equal (fn-sn-capacity (fn-sn-make groups capacity files node keyring index)) capacity))
(defthm fn-sn-files-of-fn-sn-make
  (equal (fn-sn-files (fn-sn-make groups capacity files node keyring index)) files))
(defthm fn-sn-node-of-fn-sn-make
  (equal (fn-sn-node (fn-sn-make groups capacity files node keyring index)) node))
(defthm fn-sn-keyring-of-fn-sn-make
  (equal (fn-sn-keyring (fn-sn-make groups capacity files node keyring index)) keyring))
(defthm fn-sn-index-of-fn-sn-make
  (equal (fn-sn-index (fn-sn-make groups capacity files node keyring index)) index))
; The four fields `6e992351' added to `fn-sn-state', over the six-field
; constructor that fills them: it is not silent about them, it writes 0, NIL,
; NIL and 0, and a caller that builds through it owes `fn-sn-statep' those
; four conjuncts.  Without these rules `(fn-sn-keyring-generation
; (fn-sn-make ...))' is a stuck term and `fn-sn-observed-seed-is-state'
; (books/store-observed) cannot be proved -- which is how that book was red,
; found by the w32 triage lane's provisional-certification run over this
; closure on 2026-09-22 and named in its own record.
(defthm fn-sn-keyring-generation-of-fn-sn-make
  (equal (fn-sn-keyring-generation
          (fn-sn-make groups capacity files node keyring index))
         0))
(defthm fn-sn-verdicts-of-fn-sn-make
  (equal (fn-sn-verdicts (fn-sn-make groups capacity files node keyring index))
         nil))
(defthm fn-sn-keyring-snapshots-of-fn-sn-make
  (equal (fn-sn-keyring-snapshots
          (fn-sn-make groups capacity files node keyring index))
         nil))
(defthm fn-sn-identity-next-of-fn-sn-make
  (equal (fn-sn-identity-next
          (fn-sn-make groups capacity files node keyring index))
         0))
(in-theory (disable (:d fn-sn-shapep) (:d fn-sn-groups) (:d fn-sn-capacity)
                    (:d fn-sn-files) (:d fn-sn-node) (:d fn-sn-keyring)
                    (:d fn-sn-index) (:d fn-sn-keyring-generation)
                    (:d fn-sn-verdicts) (:d fn-sn-keyring-snapshots)
                    (:d fn-sn-identity-next)
                    (:d fn-sn-make-v2) (:d fn-sn-make)))

; Shape facts type reasoning used to supply while the record opened
; (docs/proof-style.md s1), exported as forward-chaining rules only.
(defthm fn-sn-shapep-forward-shape
  (implies (fn-sn-shapep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sn-shapep))))
(defthm fn-sn-accessors-forward-consp
  (and (implies (fn-sn-groups x) (consp x))
       (implies (fn-sn-capacity x) (consp x))
       (implies (fn-sn-files x) (consp x))
       (implies (fn-sn-node x) (consp x))
       (implies (fn-sn-keyring x) (consp x))
       (implies (fn-sn-index x) (consp x)))
  :rule-classes ((:forward-chaining :corollary (implies (fn-sn-groups x) (consp x))
                                    :trigger-terms ((fn-sn-groups x)))
                 (:forward-chaining :corollary (implies (fn-sn-capacity x) (consp x))
                                    :trigger-terms ((fn-sn-capacity x)))
                 (:forward-chaining :corollary (implies (fn-sn-files x) (consp x))
                                    :trigger-terms ((fn-sn-files x)))
                 (:forward-chaining :corollary (implies (fn-sn-node x) (consp x))
                                    :trigger-terms ((fn-sn-node x)))
                 (:forward-chaining :corollary (implies (fn-sn-keyring x) (consp x))
                                    :trigger-terms ((fn-sn-keyring x)))
                 (:forward-chaining :corollary (implies (fn-sn-index x) (consp x))
                                    :trigger-terms ((fn-sn-index x))))
  :hints (("Goal" :in-theory (enable fn-sn-groups fn-sn-capacity fn-sn-files
                                     fn-sn-node fn-sn-keyring fn-sn-index))))

(defun fn-sn-statep (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-shapep s)
       (fn-string-listp (fn-sn-groups s))
       (fn-no-duplicatesp (fn-sn-groups s))
       (natp (fn-sn-capacity s))
       (fn-sf-statep (fn-sn-files s))
       (fn-node-statep (fn-sn-node s))
       ; Cheap: this walks the keyring, never the store.  The index's
       ; agreement with the store is fn-sn-indexedp, below, deliberately NOT
       ; here -- see the comment on fn-sn-index and decision D21.
       (fn-prin-keyringp (fn-sn-keyring s))
       (natp (fn-sn-keyring-generation s))
       (fn-sn-verdict-listp (fn-sn-verdicts s))
       (fn-sn-keyring-snapshot-listp (fn-sn-keyring-snapshots s))
       (natp (fn-sn-identity-next s))))

(verify-guards fn-sn-statep)
(defthm fn-sn-statep-forward-shape
  (implies (fn-sn-statep x) (and (consp x) (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sn-statep fn-sn-shapep))))
; The initial keyring is the empty one, so this keeps arity 2 and every one of
; its callers is source-unchanged.  nil satisfies fn-prin-keyringp, and
; (fn-stx-index-of-store nil k) is (fn-stx-index-empty) for EVERY k, so the
; empty store's agreement holds under any keyring.  A node that knows no
; principal's key verifies no statement, so its lace and its index are both
; empty: the correct answer for an unconfigured node, not a degenerate one.
(defun fn-sn-initial (groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-make-v2 groups capacity (fn-sf-initial-state)
              (fn-node-initial-state groups capacity)
              nil (fn-stx-index-empty) 0 nil nil 0))

(verify-guards fn-sn-initial)

; Arity 3, as before.  It now carries the keyring and the index across, which
; is what gives the index complete coverage at every transition that already
; rebuilds the state through it -- fn-sn-refuse-reservation, fn-sn-known-abort
; and fn-sn-sweep-staging among them.  A transition that CHANGES the index
; says so by using fn-sn-update-indexed instead.
(defun fn-sn-update (s files node)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-make-v2 (fn-sn-groups s) (fn-sn-capacity s) files node
              (fn-sn-keyring s) (fn-sn-index s)
              (fn-sn-keyring-generation s) (fn-sn-verdicts s)
              (fn-sn-keyring-snapshots s) (fn-sn-identity-next s)))

(verify-guards fn-sn-update)
(defun fn-sn-update-indexed (s files node index)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-make-v2 (fn-sn-groups s) (fn-sn-capacity s) files node
              (fn-sn-keyring s) index
              (fn-sn-keyring-generation s) (fn-sn-verdicts s)
              (fn-sn-keyring-snapshots s) (fn-sn-identity-next s)))

(verify-guards fn-sn-update-indexed)

(defun fn-sn-update-accepted (s files node index msgid verdict)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-make-v2 (fn-sn-groups s) (fn-sn-capacity s) files node
              (fn-sn-keyring s) index (fn-sn-keyring-generation s)
              (cons (cons msgid verdict) (fn-sn-verdicts s))
              (fn-sn-keyring-snapshots s) (fn-sn-identity-next s)))

(verify-guards fn-sn-update-accepted)

(defun fn-sn-update-replayed (s files node index identity-context)
  (declare (xargs :guard t))
  (fn-sn-make-v2
   (fn-sn-groups s) (fn-sn-capacity s) files node
   (fn-sn-keyring s) index (fn-sn-keyring-generation s)
   (fn-replay-verdict-pairs (fn-stxk-context-verdicts identity-context))
   (fn-stxk-context-snapshots identity-context)
   (fn-stxk-context-next identity-context)))

(defthm fn-sn-verdict-listp-of-recorded-cons
  (implies (and (fn-sn-verdict-listp verdicts)
                (stringp msgid)
                (member-equal (fn-stx-verdict-token verdict)
                              *fn-stx-verdicts*)
                (natp (fn-stx-verdict-generation verdict)))
           (fn-sn-verdict-listp (cons (cons msgid verdict) verdicts))))

(defun fn-sn-article-record (s obs msgid payload groups
                              obligation-id subject evidence charge)
  (declare (xargs :guard t))
  (let ((stamp (fn-record-stamp-of-observation obs))
        (txid (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))
    (if (not (natp stamp))
        :clock-unusable
      (fn-record-make (fn-sn-identity-next s) txid txid msgid payload groups
                      obligation-id subject evidence charge stamp))))

(defthm fn-sn-article-record-stamps-the-observation
  (implies (natp (fn-record-stamp-of-observation obs))
           (equal (fn-record-stamp
                   (fn-sn-article-record s obs msgid payload groups
                                         obligation-id subject evidence charge))
                  (floor (fn-clock-wall obs) 1000)))
  :hints (("Goal" :in-theory (enable fn-sn-article-record
                                     fn-record-stamp-of-observation))))

(defthm fn-sn-article-record-without-a-usable-clock-is-refused
  (implies (not (natp (fn-record-stamp-of-observation obs)))
           (equal (fn-sn-article-record s obs msgid payload groups
                                        obligation-id subject evidence charge)
                  :clock-unusable))
  :hints (("Goal" :in-theory (enable fn-sn-article-record))))

; The record is derived from the real pending proposal, including its retention
; stage, instead of a second host interpretation of the submission.
(defun fn-sn-pending-record (node sequence)
  (declare (xargs :guard t :verify-guards nil))
  (let ((pending (fn-state-pending (fn-node-acceptance node)))
        (stage (fn-node-stage node)))
    (fn-record-make sequence (fn-pending-txid pending)
                    (fn-pending-generation pending)
                    (fn-pending-msgid pending) (fn-pending-payload pending)
                    (fn-pending-groups pending) (fn-node-stage-id stage)
                    (fn-node-stage-subject stage) (fn-node-stage-evidence stage)
                    (fn-node-stage-charge stage) (fn-pending-stamp pending))))

(verify-guards fn-sn-pending-record)
(defun fn-sn-record-bindsp (node record)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil))
  (and (fn-record-p record)
       (fn-node-pending-matchesp node (fn-record-txid record)
                                (fn-record-generation record))
       (equal record (fn-sn-pending-record node (fn-record-sequence record)))))

(verify-guards fn-sn-record-bindsp)

; Proper-list record helpers retain their original logical bodies.  Public
; preparation/completion gates establish the stronger fn-record-p condition.
(defun fn-sn-prepare-node (node record)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-node-prepare (fn-replay-advance-txid node (fn-record-txid record))
                   (fn-record-generation record) (fn-record-msgid record)
                   (fn-record-payload record) (fn-record-groups record)
                   (fn-record-obligation-id record)
                   (fn-record-content-subject record)
                   (fn-record-release-evidence record) (fn-record-charge record)
                   (fn-record-stamp record)))

(verify-guards fn-sn-prepare-node)

; The guard proof of fn-sn-prepare: the speculative node is a node.
(defthm fn-sn-prepare-node-preserves-state
  (implies (fn-node-statep node)
           (fn-node-statep (fn-sn-prepare-node node record))))

; Pure preparation: a failed gate publishes neither the speculative node nor
; record.  The durable reservation stays available until refusal/abort/recovery.
(defun fn-sn-prepare (s record)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (null (fn-node-stage (fn-sn-node s)))
           (fn-record-p record)
           (not (equal (fn-record-stamp record) :legacy)))
      (let* ((node (fn-sn-prepare-node (fn-sn-node s) record))
             (files (fn-sf-prepare-record (fn-sn-files s) record
                                          (fn-sn-groups s) (fn-sn-capacity s))))
        (if (and (fn-sn-record-bindsp node record)
                 (equal (fn-sf-phase files) :record-staged))
            (fn-sn-update s files node)
          s))
    s))

(verify-guards fn-sn-prepare
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep)
                (fn-sf-statep fn-node-statep fn-node-pending-matchesp
                 fn-sn-pending-record fn-sn-prepare-node)))))

(defthm fn-sn-prepare-refuses-a-legacy-record
  (implies (equal (fn-record-stamp record) :legacy)
           (equal (fn-sn-prepare s record) s))
  :hints (("Goal" :in-theory (enable fn-sn-prepare))))

; Retention events use the same reserved transaction and file publication
; machine.  Their node effect is deliberately deferred until fn-sn-finish:
; before the directory barrier the candidate is known absent or uncertain,
; so the live canonical ledger must not advertise a release yet.
(defun fn-sn-prepare-retention (s event)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (fn-store-retention-event-p event)
           (consp (fn-replay-apply-retention-event (fn-sn-node s) event)))
      (let ((files (fn-sf-prepare-record (fn-sn-files s) event
                                         (fn-sn-groups s) (fn-sn-capacity s))))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

(defun fn-sn-identity-context (s)
  (declare (xargs :guard t))
  (let ((snapshots (fn-sn-keyring-snapshots s)))
    (fn-stxk-context :ok (fn-sn-identity-next s) snapshots nil
                     (if (consp snapshots)
                         (fn-stxk-keyring-generation (car snapshots))
                       nil)
                     nil)))

(defun fn-sn-prepare-identity (s event)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :reserved)
           (or (fn-stxe-p event) (fn-stxk-p event) (fn-stxa-p event))
           (or (not (fn-stxa-p event))
               (not (equal (fn-record-stamp (fn-replay-composite-record event))
                           :legacy)))
           (consp (fn-replay-apply-record (fn-sn-node s) event))
           (equal (fn-stxk-context-kind
                   (fn-replay-identity-step (fn-sn-identity-context s) event))
                  :ok))
      (let ((files (fn-sf-prepare-record (fn-sn-files s) event
                                         (fn-sn-groups s) (fn-sn-capacity s))))
        (if (equal (fn-sf-phase files) :record-staged)
            (fn-sn-update s files (fn-sn-node s))
          s))
    s))

(defun fn-sn-find-record (pair records)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp records)
      (if (equal pair (fn-sf-record-pair (car records)))
          (car records)
        (fn-sn-find-record pair (cdr records)))
    nil))

(verify-guards fn-sn-find-record)
(defun fn-sn-completion-record (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sn-find-record (fn-sf-completion (fn-sn-files s))
                     (fn-sf-records (fn-sn-files s))))

(verify-guards fn-sn-completion-record)
(defun fn-sn-completion-enabledp (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (let ((record (fn-sn-completion-record s)))
         (cond ((fn-store-retention-event-p record)
                (consp (fn-replay-apply-retention-event (fn-sn-node s) record)))
               ((or (fn-stxe-p record) (fn-stxk-p record) (fn-stxa-p record))
                (and (consp (fn-replay-apply-record (fn-sn-node s) record))
                     (equal (fn-stxk-context-kind
                             (fn-replay-identity-step
                              (fn-sn-identity-context s) record)) :ok)))
               (t (fn-sn-record-bindsp (fn-sn-node s) record))))
       (equal (fn-sf-completion (fn-sn-files s))
              (fn-sf-record-pair (fn-sn-completion-record s)))))

(verify-guards fn-sn-completion-enabledp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; One logical completion operation.  Success is recorded only after calling
; the actual matching durable node branch; there is no externally supplied
; completion status.  The filesystem durability observation remains the file
; kernel's record-directory result, under its documented platform assumptions.
; The statement delta of the article the durable branch below publishes.  The
; article is NAMED, not existentially claimed: fn-install-pending
; (books/acceptance.lisp line 236) conses exactly
; (fn-article-from-pending (fn-state-pending ...)) onto the store, and
; fn-stx-durable-completion-is-an-acceptance (books/stx-lace.lisp) is the
; theorem that says so.  It is read off the state BEFORE the completion,
; because the completion clears the pending.
(defun fn-sn-accepted-delta (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (fn-stx-delta (fn-article-payload
                 (fn-article-from-pending
                  (fn-state-pending (fn-node-acceptance (fn-sn-node s)))))
                (fn-sn-keyring s)))

(verify-guards fn-sn-accepted-delta
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; The shape fact fn-stx-index-add's guard wants, with fn-sn-accepted-delta
; withdrawn at fn-sn-finish's guard proof.
(defthm fn-sn-accepted-delta-is-lace
  (fn-lace-p (fn-sn-accepted-delta s))
  :hints (("Goal" :in-theory (enable fn-sn-accepted-delta))))

; `fn-stx-delta' (books/stx-lace) is guarded by `fn-prin-keyringp', so under
; `:guard t' this function has to say what it does without one; it contributes
; no statements, which is what `fn-stx-delta' itself returns for a keyring
; that verifies nothing.  Every caller passes `(fn-sn-keyring s)' of a state
; that satisfies `fn-sn-statep', so the branch is not reachable in the
; composed machine.  The decoder stays closed in the guard proof: opening
; `fn-replay-composite-record' unfolds the record codec into the conjecture
; (measured 2026-09-22, hbox certify-20260922T054916Z-2704241).
(defun fn-sn-composite-delta (event keyring)
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :in-theory (disable fn-replay-composite-record)))))
  (if (not (fn-prin-keyringp keyring)) nil
    (let ((record (fn-replay-composite-record event)))
      (if (fn-record-p record)
          (fn-stx-delta (fn-record-payload record) keyring)
        (fn-stx-delta nil keyring)))))

(defun fn-sn-finish-identity (s files record node)
  (declare (xargs :guard t))
  (let* ((ctx (fn-replay-identity-step (fn-sn-identity-context s) record))
         (new-verdicts (fn-replay-verdict-pairs
                        (fn-stxk-context-verdicts ctx)))
         (index (if (fn-stxa-p record)
                    (fn-stx-index-add (fn-sn-index s)
                                      (fn-sn-composite-delta record
                                                             (fn-sn-keyring s)))
                  (fn-sn-index s))))
    (fn-sn-make-v2
     (fn-sn-groups s) (fn-sn-capacity s) files node
     (fn-sn-keyring s) index (fn-sn-keyring-generation s)
     (append new-verdicts (fn-sn-verdicts s))
     (fn-stxk-context-snapshots ctx) (fn-stxk-context-next ctx))))

(defun fn-sn-advance-identity-next (s)
  (declare (xargs :guard t))
  (fn-sn-make-v2
   (fn-sn-groups s) (fn-sn-capacity s) (fn-sn-files s) (fn-sn-node s)
   (fn-sn-keyring s) (fn-sn-index s) (fn-sn-keyring-generation s)
   (fn-sn-verdicts s) (fn-sn-keyring-snapshots s)
   (1+ (nfix (fn-sn-identity-next s)))))

(defun fn-sn-finish (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-sn-completion-enabledp s)
      (let* ((record (fn-sn-completion-record s))
             (retentionp (fn-store-retention-event-p record))
             (identityp (or (fn-stxe-p record) (fn-stxk-p record)
                            (fn-stxa-p record)))
             (node (cond (retentionp
                          (fn-replay-apply-retention-event (fn-sn-node s) record))
                         (identityp
                          (fn-replay-apply-record (fn-sn-node s) record))
                         (t
                          (fn-node-complete (fn-sn-node s) (fn-record-txid record)
                                            (fn-record-generation record) :durable))))
             (files (fn-sf-core-completion
                     (fn-sn-files s) (fn-store-event-sequence record)
                     (fn-store-event-txid record))))
        ; The one site where the index changes, and it changes by at most one
        ; cons (fn-stx-index-grows-by-at-most-one-binding).  No walk of the
        ; store happens here; that is the whole point of carrying it.
        (if retentionp
            (fn-sn-advance-identity-next
             (fn-sn-update-indexed
              s (fn-sf-emit-success files (fn-store-event-sequence record)
                                    (fn-store-event-txid record))
              node (fn-sn-index s)))
          (if identityp
              (fn-sn-finish-identity
               s (fn-sf-emit-success files (fn-store-event-sequence record)
                                     (fn-store-event-txid record))
               record node)
            (fn-sn-advance-identity-next
             (fn-sn-update-accepted
              s (fn-sf-emit-success files (fn-store-event-sequence record)
                                    (fn-store-event-txid record))
              node
              (fn-stx-index-add (fn-sn-index s) (fn-sn-accepted-delta s))
              (fn-record-msgid record)
              (fn-stx-verdict-of-octets
               (fn-record-payload record)
               (fn-sn-keyring s) (fn-sn-keyring-generation s)))))))
    s))

; The guard obligations are type facts about the state's fields, the
; completion record's shape and the kernel step; none needs the completion
; gate or the record opened.  With `fn-sn-completion-enabledp',
; `fn-sn-record-bindsp', the store-transaction recognizers and the record
; codec open (they are enabled at this point of the book), the hypothesis
; unfolded into the codec and the goal split 5744 ways at Goal' (305 s,
; 23.4 million steps, 2026-09-23 seam run;
; planning/evidence/store-cluster-cost-2026-09-23.md).  Closed, the shape
; comes from the recognizers' forward-chaining rules.
(verify-guards fn-sn-finish
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep)
                (fn-sf-statep fn-node-statep fn-sn-completion-record
                 fn-node-pending-matchesp fn-sn-pending-record
                 fn-sn-prepare-node fn-sf-core-completion
                 fn-sn-accepted-delta
                 fn-sn-completion-enabledp fn-sn-record-bindsp
                 fn-sn-identity-context fn-replay-identity-step
                 fn-replay-apply-retention-event fn-replay-apply-record
                 fn-store-retention-event-p fn-stxe-p fn-stxk-p fn-stxa-p
                 fn-record-record-vocabulary fn-record-shape-vocabulary)))))

; The I/O surface cannot inject a core-completion observation or emit success.
; There is deliberately no :core-completion operation here: the kernel's
; fn-sf-core-completion is reachable only inside fn-sn-finish above, so a host
; word claiming completion is a no-op (fn-sn-io-cannot-acknowledge).
(defun fn-sn-file-step (files operation result)
  (declare (xargs :guard (fn-sf-statep files) :verify-guards nil))
  (case operation
    (:start-frontier (fn-sf-start-frontier files))
    (:frontier-file (fn-sf-frontier-file-result files result))
    (:frontier-replace (fn-sf-frontier-replace-result files result))
    (:frontier-directory (fn-sf-frontier-dir-result files result))
    (:record-file (fn-sf-record-file-result files result))
    (:record-link (fn-sf-record-link-result files result))
    (:record-directory (fn-sf-record-dir-result files result))
    (:recovery-barrier (fn-sf-recovery-barrier files result))
    (otherwise files)))

(verify-guards fn-sn-file-step)
(defun fn-sn-io (s operation result)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (mbe :logic (fn-sn-statep s) :exec t)
      (fn-sn-update s (fn-sn-file-step (fn-sn-files s) operation result)
                    (fn-sn-node s))
    s))

(verify-guards fn-sn-io
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; A crash discards the live process view.  Recovery reconstructs a new node
; through the existing replay interpreter, whose individual records call the
; same actual fn-node-prepare/fn-node-complete pair used above.  The kernel
; crash is one constructor of an admissible image; the host never calls it.
; A real process reopens through fn-sn-open-observed (store-observed.lisp),
; whose theorems take fn-sf-crash-imagep as the platform premise.
(defun fn-sn-crash (s frontier-choice record-choice)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-sn-statep s)
           (fn-sf-crash-choicep frontier-choice record-choice))
      ; The node is reset to the empty store, so the index is the empty one.
      ; This is a recomputation whose cost is zero, not a carried value.
      (fn-sn-update-indexed
       s (fn-sf-crash (fn-sn-files s) frontier-choice record-choice)
       (fn-node-initial-state (fn-sn-groups s) (fn-sn-capacity s))
       (fn-stx-index-empty))
    s))

(verify-guards fn-sn-crash)
(defun fn-sn-recover (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (equal (fn-sf-phase (fn-sn-files s)) :replaying))
      (let* ((files (fn-sf-recover (fn-sn-files s)
                                   (fn-sn-groups s) (fn-sn-capacity s)))
             (node (fn-sf-replay-node (fn-sn-groups s) (fn-sn-capacity s)
                                       (fn-sf-records files)
                                       (fn-sf-frontier files)))
             (identity-context
              (fn-replay-identity (fn-sf-records files))))
        ; Recovery is the one transition whose node does not come from a
        ; step of this machine, so it is the one that recomputes.  It is not
        ; a served path: it runs once, at open, on the replayed store.
        (if (and (equal (fn-sf-phase files) :recovering)
                 (equal (fn-stxk-context-kind identity-context) :ok))
            (fn-sn-update-replayed
             s files node
             (fn-stx-index-of-store (fn-stx-store node) (fn-sn-keyring s))
             identity-context)
          ; The article replay and the identity replay are both required.
          ; Never leave :recovering visible when only the former succeeded:
          ; observed open uses that phase to authorize its durability barriers.
          (fn-sn-update
           s (fn-sf-make :fault (fn-sf-frontier files) nil
                         (fn-sf-records files) nil nil
                         (fn-sf-successes files) 0)
           (fn-sn-node s))))
    s))

(verify-guards fn-sn-recover
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; unreachable-in-composition: no host path calls fn-sn-fence-node or
; fn-sn-resolve-node (host/store-node-host.lisp resolves every uncertainty by
; reopening through fn-sn-open-observed).  They remain as proof notation for
; the in-process resolution correspondence and because other books name them
; in theory lists; they are not evidence for any host claim.
(defun fn-sn-fence-node (node record)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-node-complete node (fn-record-txid record)
                    (fn-record-generation record) :indeterminate))

(verify-guards fn-sn-fence-node)
(defun fn-sn-resolve-node (node record committedp)
  (declare (xargs :guard (and (fn-node-statep node) (true-listp record))
                  :verify-guards nil))
  (fn-node-recover node (fn-record-txid record) (fn-record-generation record)
                   (if committedp :committed :absent)))

(verify-guards fn-sn-resolve-node)

; -----------------------------------------------------------------------------
; The keyring, the carried agreement, and the two served queries (D21)

; Live reconfiguration of the verification context.  It recomputes the index
; over the whole store, and that is correct: a new keyring gives a new set of
; verified statements, so nothing of the old index survives.  This is a
; reconfiguration event, not a served path.  A malformed keyring is refused
; -- the state is returned unchanged -- rather than installed, because
; fn-sn-statep carries fn-prin-keyringp of this field.
(defun fn-sn-set-keyring (s keyring)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (and (mbe :logic (fn-sn-statep s) :exec t)
           (fn-prin-keyringp keyring))
      (fn-sn-make-v2 (fn-sn-groups s) (fn-sn-capacity s) (fn-sn-files s)
                  (fn-sn-node s) keyring
                  (fn-stx-index-of-store (fn-stx-store (fn-sn-node s)) keyring)
                  (1+ (fn-sn-keyring-generation s))
                  (fn-sn-verdicts s) (fn-sn-keyring-snapshots s)
                  (fn-sn-identity-next s))
    s))

(verify-guards fn-sn-set-keyring
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; The carried agreement.  This is the guard of NOTHING: it is established at
; fn-sn-initial, proved preserved by every transition in
; books/store-node-invariants.lisp, and used as the hypothesis of the query
; keystone there.  Making it a conjunct of fn-sn-statep instead would put a
; whole-store re-derivation -- with a signature verification per article --
; into the guard the host checks on every call into this machine (D20, D3).
(defun fn-sn-indexedp (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-statep s)
       (fn-stx-index-invariantp (fn-sn-index s) (fn-sn-node s)
                                (fn-sn-keyring s))))

(verify-guards fn-sn-indexedp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

; The two served queries.  Their guard is t and their bodies mention neither
; fn-stx-store nor fn-stx-lace nor fn-node-acceptance, so no host call through
; either of them walks the store or re-parses an article.
(defun fn-sn-statement-lookup (s id)
  (declare (xargs :guard t))
  (fn-stx-index-lookup (fn-sn-index s) id))

(defun fn-sn-equivocatorp (s creator incarnation)
  (declare (xargs :guard t))
  (fn-stx-index-equivocatorp (fn-sn-index s) creator incarnation))

(defun fn-sn-verdict-lookup-list (msgid xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (and (consp (car xs)) (equal msgid (car (car xs))))
          (cdr (car xs))
        (fn-sn-verdict-lookup-list msgid (cdr xs)))
    nil))

; Durable kind-4 acceptance installs a historical verdict here.  A legacy
; fn-r completion also exposes its current-process observation for compatibility,
; but that observation is deliberately absent after recovery: fn-r contains no
; immutable verdict/provenance bytes.  Only kind 4 is durable authority.  This
; query neither opens the article nor consults the current keyring.
(defun fn-sn-verdict-lookup (s msgid)
  (declare (xargs :guard t))
  (fn-sn-verdict-lookup-list msgid (fn-sn-verdicts s)))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md s2).  Enabled on include: the record
; lemmas, fn-sn-update and fn-sn-find-record (glue and induction vocabulary)
; and fn-sn-prepare-node-preserves-state.  Withdrawn: the recognizer, the
; initial state and every transition; store-node-invariants opens them
; locally.  The two deferred preparations and the identity context joined
; the list on 2026-09-23: they postdate it, and left enabled they opened in
; every goal that dispatched on a store event, carrying the replay steps and
; the record codec in with them (store-node-resolution-cost-2026-09-23.md,
; store-cluster-cost-2026-09-23.md).  A proof about one of them opens it in
; its hint.
(in-theory (disable fn-sn-statep fn-sn-initial fn-sn-pending-record
                    fn-sn-record-bindsp fn-sn-prepare-node fn-sn-prepare
                    fn-sn-prepare-retention fn-sn-prepare-identity
                    fn-sn-identity-context
                    fn-sn-completion-record fn-sn-completion-enabledp
                    fn-sn-accepted-delta
                    fn-sn-finish fn-sn-file-step fn-sn-io fn-sn-crash
                    fn-sn-recover fn-sn-fence-node fn-sn-resolve-node
                    fn-sn-set-keyring fn-sn-indexedp
                    fn-sn-statement-lookup fn-sn-equivocatorp
                    fn-sn-verdict-lookup-list fn-sn-verdict-lookup))
