; fn: PreparedCommit, completion by token, and the shared transition over the
; held record (wave 5, lane catalog-slice step 4, 2026-09-26; D33; the
; consolidation design sections 1.3 and 4.3).
;
; Today the finish finds the record that is completing by walking the
; history for its (sequence . txid) pair (`fn-sn-completion-record',
; books/store-node.lisp; `fn-ccar-seek', books/owner-commit-carried.lisp),
; and re-reads its bytes for the statement verdict and the identity delta.
; This book replaces both with values the live execution state holds:
;
;   PreparedCommit  (fn-pc-make token expected held plan reservation)
;     token        (txid . expected): the operation token, unique per attempt
;                  because the txid is consumed per attempt
;     expected     the catalog count at prepare: the row's position when it commits
;     held         the interned held record (the handle sealed at prepare; an
;                  abandoned attempt's handle is garbage reclaimed at the next open)
;     plan         the record file's frame (the host's frame today)
;     reservation  the charge and capacity vector reserved (fn-cvec, fn-smr)
;
;   fn-cat-prepare   interns from the buffer and returns the PreparedCommit, or
;                    (:pending) when one is pending: at most one (the phase gate)
;   fn-cat-complete  TOKEN must be the pending's, else (:stale-token) and nothing
;                    changes; EXPECTED must be the count, else (:expected-mismatch)
;                    and nothing changes (a corrupted state is refused, never
;                    committed elsewhere); otherwise the held row is committed at
;                    EXPECTED, the pending is cleared and the :article delta is
;                    emitted, read off the committed row.  No search.
;   fn-cat-abandon   a known abort: clears the pending; a stale token is refused
;
; The delta is emitted ONCE, by the completion, from the committed row (the
; numbers are the catalog's assignment); the LANEDUMP's prepare-time delta
; field would have been a second computation of the same value and is not
; a field.
;
; THE SHARED TRANSITION, `fn-sn-finish-held' (s h ctx): `fn-sn-finish' with
; the completing record supplied (the token's held record, no walk), the
; verdict and the delta taken from the record's context CTX instead of the
; bytes, and the record's binding to the node's pending transaction checked
; on the ten metadata positions (`fn-snh-bindsp').  Its gate
; `fn-snh-enabledp' compares the context's keyring generation with the
; store's and refuses a stale context by name, so the finish never commits
; a verdict decided under a keyring the store no longer holds.
;
; THE CONTEXT THEOREM, chosen form.  The design offered two: the phase gate
; (no admitted transition changes the keyring while a prepare is pending)
; or the finish re-deciding.  The phase gate is NOT a theorem of this
; machine: `fn-sn-set-keyring' has no phase check.  (No native host line
; calls it: host/store-node-host.lisp `fn-store-sn-set-keyring' is reached
; from tools/run_store.py only, the retired Python host; the native node's
; keyring is fixed at open.)  So the re-decide form is taken, in its exact
; shape: `fn-sn-context-fixed-between-prepare-and-finish' says the keyring
; GENERATION NAMES the keyring along every transition -- each transition
; the host applies leaves both, and `fn-sn-set-keyring', the one writer,
; advances the generation whenever it changes the keyring -- so a context
; whose generation is the store's was decided under the store's keyring,
; which is what `fn-snh-enabledp' checks in O(1) and what
; `fn-sn-finish-held-is-finish' assumes.  A context whose generation is not
; the store's is refused (`fn-sn-finish-held-refuses-a-stale-context'), and
; the host re-decides it from the arena (step 8; PKT-585).
;
; KEYSTONE fn-cat-complete-by-token (PRF-203): with the pending's token and
; EXPECTED the count, the completed row is (fn-cat-at expected C') = the
; pending's held record with its numbers, the count is expected + 1, the
; pending is cleared and the delta names that row.  A stale token is refused
; by name; a token from an abandoned attempt cannot complete the next
; attempt, because the next attempt's txid differs.
;
; KEYSTONE fn-sn-finish-held-is-finish: on the article arm, the held finish
; over the completing record's held view and the context of its bytes under
; the store's keyring and generation IS `fn-sn-finish'.  The article arm is
; the served POST's; the composite (kind-4), retention, consumer and topic
; arms keep `fn-sn-finish' over the event (PKT-585).

(in-package "ACL2")
(include-book "catalog-handles")
(include-book "catalog")
(include-book "store-node")
(include-book "store-node-resolution")
(include-book "store-events-carried")

; -----------------------------------------------------------------------------
; PreparedCommit.

(defun fn-pc-tokenp (x)
  (declare (xargs :guard t))
  (and (consp x) (natp (car x)) (natp (cdr x))))

(defun fn-pc-anyp (x)
  (declare (xargs :guard t) (ignore x))
  t)

(fn-defrecord fn-pc
  :constructor (fn-pc-make token expected held plan reservation)
  :fields ((fn-pc-token fn-pc-tokenp)
           (fn-pc-expected natp)
           (fn-pc-held fn-held-p)
           (fn-pc-plan fn-pc-anyp)
           (fn-pc-reservation fn-pc-anyp))
  :recognizer fn-pc-p
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

; Nothing pending, or one PreparedCommit.
(defun fn-pc-optionp (x)
  (declare (xargs :guard t))
  (or (null x) (fn-pc-p x)))

(defthm fn-pc-p-fields
  (implies (fn-pc-p pc)
           (and (fn-pc-tokenp (fn-pc-token pc))
                (natp (fn-pc-expected pc))
                (fn-held-p (fn-pc-held pc))))
  :hints (("Goal" :in-theory (enable fn-pc-p))))

; -----------------------------------------------------------------------------
; The :article delta, read off a committed row.  The grammar of every delta
; kind is books/catalog-delta.lisp's; this is the one the completion emits.

(fn-defrecord fn-dart
  :constructor (fn-dart-make seq msgid numbers handle facts context)
  :tag :article
  :fields ((fn-dart-seq natp)
           (fn-dart-msgid fn-record-msgidp)
           (fn-dart-numbers fn-held-numbersp)
           (fn-dart-handle natp)
           (fn-dart-facts fn-hf-p)
           (fn-dart-context fn-hc-p))
  :recognizer fn-dart-p
  :recognizer-verify-guards nil
  :car-fn fn-cbor-ag-car
  :cdr-fn fn-cbor-ag-cdr)

(verify-guards fn-dart-p)

(defun fn-delta-of-row (seq row)
  (declare (xargs :guard (natp seq)))
  (fn-dart-make seq (fn-record-msgid row) (fn-held-numbers row)
                (fn-record-payload row) (fn-held-facts row) (fn-held-context row)))

(defthm fn-dart-p-of-delta-of-row
  (implies (and (natp seq) (fn-held-p row))
           (fn-dart-p (fn-delta-of-row seq row)))
  :hints (("Goal" :in-theory (enable fn-dart-p fn-held-p fn-dart-internals
                                     fn-held-internals fn-record-internals))))

; -----------------------------------------------------------------------------
; Prepare, complete, abandon.

; W supplies the metadata (its payload position is not read: the bytes are
; the buffer's), PLAN and RESERVATION are the host's frame and reservation.
; Refused by name when a PreparedCommit is pending.
(defun fn-cat-prepare (w plan reservation fn-octets keyring generation pending
                         fn-arena fn-cat)
  (declare (xargs :stobjs (fn-octets fn-arena fn-cat)
                  :guard (and (fn-prin-keyringp keyring) (natp generation))))
  (if pending
      (mv (list :pending) fn-arena)
    (mv-let (held fn-arena)
      (fn-cat-intern w fn-octets keyring generation fn-arena)
      (let ((expected (fn-cat-count fn-cat)))
        (mv (fn-pc-make (cons (nfix (fn-record-txid w)) expected)
                        expected held plan reservation)
            fn-arena)))))

; => (mv result pending' fn-cat): result is (:stale-token), (:expected-mismatch)
; or the :article delta of the committed row.
(defun fn-cat-complete (token pending fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (fn-pc-optionp pending)
                  :guard-hints (("Goal" :in-theory (enable fn-pc-p)))))
  (if (or (null pending) (not (equal token (fn-pc-token pending))))
      (mv (list :stale-token) pending fn-cat)
    (let ((expected (fn-pc-expected pending)))
      (if (not (equal expected (fn-cat-count fn-cat)))
          (mv (list :expected-mismatch) pending fn-cat)
        (let ((fn-cat (fn-cat-commit (fn-pc-held pending) fn-cat)))
          (mv (fn-delta-of-row expected (fn-cat-at expected fn-cat))
              nil fn-cat))))))

; The completion of a row the owner's view already hides (R1, step 8: a
; cancel that arrived before its target; books/served-catalog-owner.lisp):
; the held record is committed withdrawn at its own index, so no view shows
; it, as the owner's refresh shows it at no version.  The token discipline
; is fn-cat-complete's; BY names the cause the caller knows (informational,
; as fn-cat-withdraw's BY).
(defthm fn-held-p-of-fn-held-with-withdrawn
  (implies (and (fn-held-p h) (fn-held-withdrawnp w))
           (fn-held-p (fn-held-with-withdrawn h w)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-with-withdrawn))))

(defun fn-cat-complete-hidden (token pending by fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (fn-pc-optionp pending) (natp by))
                  :guard-hints (("Goal" :in-theory (enable fn-pc-p fn-held-withdrawnp)))))
  (if (or (null pending) (not (equal token (fn-pc-token pending))))
      (mv (list :stale-token) pending fn-cat)
    (let ((expected (fn-pc-expected pending)))
      (if (not (equal expected (fn-cat-count fn-cat)))
          (mv (list :expected-mismatch) pending fn-cat)
        (let ((fn-cat (fn-cat-commit
                       (fn-held-with-withdrawn (fn-pc-held pending) (cons expected by))
                       fn-cat)))
          (mv (fn-delta-of-row expected (fn-cat-at expected fn-cat))
              nil fn-cat))))))

; => (mv status pending'): :ok and nothing pending, or :stale-token unchanged.
(defun fn-cat-abandon (token pending)
  (declare (xargs :guard (fn-pc-optionp pending)
                  :guard-hints (("Goal" :in-theory (enable fn-pc-p)))))
  (if (or (null pending) (not (equal token (fn-pc-token pending))))
      (mv :stale-token pending)
    (mv :ok nil)))

; -----------------------------------------------------------------------------
; The token protocol's theorems (PRF-203).

; The prepare's result, when not refused: its token, expected and held.
(defthm fn-cat-prepare-fields
  (implies (not pending)
           (let ((pc (mv-nth 0 (fn-cat-prepare w plan reservation fn-octets keyring
                                               generation pending fn-arena fn-cat))))
             (and (equal (fn-pc-token pc) (cons (nfix (fn-record-txid w)) (fn-cat-count fn-cat)))
                  (equal (fn-pc-expected pc) (fn-cat-count fn-cat))
                  (equal (fn-pc-held pc)
                         (mv-nth 0 (fn-cat-intern w fn-octets keyring generation fn-arena)))
                  (equal (fn-pc-plan pc) plan)
                  (equal (fn-pc-reservation pc) reservation))))
  :hints (("Goal" :in-theory (enable fn-pc-internals))))

(defthm fn-cat-prepare-refused-when-pending
  (implies pending
           (equal (fn-cat-prepare w plan reservation fn-octets keyring generation
                                  pending fn-arena fn-cat)
                  (mv (list :pending) fn-arena))))

; The interned record is a held record whenever W's ten metadata positions
; are a wire record's, whatever bytes stand in its payload position (the
; intern of the buffer is the list intern of W with the buffer's bytes:
; fn-cat-intern-is-intern-list).
(defthm fn-held-p-of-intern-list-of-held-wire
  (implies (and (fn-record-p w) (natp generation))
           (fn-held-p (mv-nth 0 (fn-cat-intern-list (fn-held-wire w bytes)
                                                    keyring generation fn-arena))))
  :hints (("Goal" :in-theory (enable fn-cat-intern-list fn-held-wire
                                     fn-record-p fn-held-p
                                     fn-record-internals fn-held-internals
                                     fn-hf-p fn-hc-p))))

(defthm fn-held-p-of-intern-of-record
  (implies (and (fn-record-p w) (natp generation))
           (fn-held-p (mv-nth 0 (fn-cat-intern w fn-octets keyring generation fn-arena))))
  :hints (("Goal" :in-theory (enable fn-cat-intern fn-cat-intern-list fn-held-wire
                                     fn-record-p fn-held-p
                                     fn-record-internals fn-held-internals
                                     fn-hf-p fn-hc-p))))

(defthm fn-pc-p-of-prepare
  (implies (and (not pending) (fn-record-p w) (natp generation))
           (fn-pc-p (mv-nth 0 (fn-cat-prepare w plan reservation fn-octets keyring
                                              generation pending fn-arena fn-cat))))
  :hints (("Goal" :in-theory (e/d (fn-pc-p fn-pc-internals fn-pc-tokenp)
                                  (fn-held-p))
           :use ((:instance fn-held-p-of-intern-list-of-held-wire (bytes fn-octets))))))

; KEYSTONE: completion by token.  No search: the row is at EXPECTED.
(defthm fn-cat-complete-by-token
  (implies (and (fn-pc-p pending)
                (equal token (fn-pc-token pending))
                (equal (fn-pc-expected pending) (fn-cat-count fn-cat)))
           (let ((expected (fn-pc-expected pending)))
             (mv-let (result pending2 fn-cat2)
               (fn-cat-complete token pending fn-cat)
               (and (equal (fn-cat-at expected fn-cat2)
                           (fn-cat-assign (fn-pc-held pending) fn-cat))
                    (equal (fn-cat-count fn-cat2) (+ 1 expected))
                    (equal pending2 nil)
                    (equal result
                           (fn-delta-of-row expected
                                            (fn-cat-assign (fn-pc-held pending) fn-cat)))))))
  :hints (("Goal" :in-theory (e/d (fn-cat-complete)
                                  (fn-pc-p fn-cat-count-is-len fn-cat-at-is-nth
                                   fn-cat-commit-is-append)))))

; The refusals, by name, and nothing changes.
(defthm fn-cat-complete-stale-refused
  (implies (or (null pending) (not (equal token (fn-pc-token pending))))
           (equal (fn-cat-complete token pending fn-cat)
                  (mv (list :stale-token) pending fn-cat))))

(defthm fn-cat-complete-expected-mismatch-refused
  (implies (and pending (equal token (fn-pc-token pending))
                (not (equal (fn-pc-expected pending) (fn-cat-count fn-cat))))
           (equal (fn-cat-complete token pending fn-cat)
                  (mv (list :expected-mismatch) pending fn-cat))))

(defthm fn-cat-abandon-clears
  (implies (and pending (equal token (fn-pc-token pending)))
           (equal (fn-cat-abandon token pending) (mv :ok nil))))

(defthm fn-cat-abandon-stale-refused
  (implies (or (null pending) (not (equal token (fn-pc-token pending))))
           (equal (fn-cat-abandon token pending) (mv :stale-token pending))))

; A token from an abandoned attempt cannot complete the next attempt: the
; next prepare's token carries the next txid, and the txid is consumed per
; attempt (host/native/owner.lisp fnn-owner-attempt advances the frontier
; before every attempt).  The witness with EQUAL txids is in the test book:
; the hypothesis is what keeps the old token out.
(defthm fn-cat-token-of-abandoned-attempt-is-stale
  (implies (and (not pending)
                (not (equal (nfix (fn-record-txid w1)) (nfix (fn-record-txid w2)))))
           (mv-let (status pending1)
             (fn-cat-abandon (cons (nfix (fn-record-txid w1)) (fn-cat-count fn-cat))
                             (mv-nth 0 (fn-cat-prepare w1 plan1 res1 fn-octets keyring
                                                       generation pending fn-arena fn-cat)))
             (declare (ignore status))
             (let ((pending2 (mv-nth 0 (fn-cat-prepare w2 plan2 res2 fn-octets keyring
                                                       generation pending1 fn-arena fn-cat))))
               (equal (mv-nth 0 (fn-cat-complete
                                 (cons (nfix (fn-record-txid w1)) (fn-cat-count fn-cat))
                                 pending2 fn-cat))
                      (list :stale-token)))))
  :hints (("Goal" :in-theory (enable fn-pc-internals))))

(in-theory (disable fn-cat-prepare fn-cat-complete fn-cat-abandon fn-delta-of-row))

; -----------------------------------------------------------------------------
; The shared transition.  The article arm of fn-sn-finish, with the record
; supplied and its bytes' decisions taken from the context.

; The completing record binds the node's pending transaction: the ten
; metadata positions of `fn-sn-pending-record' (books/store-node.lisp),
; without the payload.
(defun fn-snh-bindsp (node h)
  (declare (xargs :guard (fn-node-statep node) :verify-guards nil))
  (and (fn-held-p h)
       (fn-node-pending-matchesp node (fn-record-txid h) (fn-record-generation h))
       (let ((pending (fn-state-pending (fn-node-acceptance node)))
             (stage (fn-node-stage node)))
         (and (equal (fn-record-txid h) (fn-pending-txid pending))
              (equal (fn-record-generation h) (fn-pending-generation pending))
              (equal (fn-record-msgid h) (fn-pending-msgid pending))
              (equal (fn-record-groups h) (fn-pending-groups pending))
              (equal (fn-record-obligation-id h) (fn-node-stage-id stage))
              (equal (fn-record-content-subject h) (fn-node-stage-subject stage))
              (equal (fn-record-release-evidence h) (fn-node-stage-evidence stage))
              (equal (fn-record-charge h) (fn-node-stage-charge stage))
              (equal (fn-record-stamp h) (fn-pending-stamp pending))))))

(verify-guards fn-snh-bindsp)

; The consumer projection's answer for an article record at SEQ
; (`fn-cpe-projection-step', books/consumer-store-projection.lisp: an
; article is not a consumer event, so the step reads only its sequence).
(defun fn-snh-projection-okp (c seq expected)
  (declare (xargs :guard t))
  (and (fn-cp-uintp expected)
       (not (equal expected *fn-cbor-max-uint*))
       (equal seq expected)
       (or (null c) (equal (fn-cp-nth 3 c) expected))))

(defun fn-snh-projection-next (c expected)
  (declare (xargs :guard t))
  (if (null c) nil (fn-cpe-projection-advance c (1+ (nfix expected)))))

; The topic prefix's answer for an article record at SEQ
; (`fn-th-prefix-step', books/topic-history-prefix.lisp: the last arm).
(defun fn-snh-topic-okp (p seq)
  (declare (xargs :guard t))
  (and (equal (fn-th-at 0 p) :ok) (equal (fn-th-at 1 p) seq)))

(defun fn-snh-topic-next (p)
  (declare (xargs :guard t))
  (fn-th-prefix-state :ok (1+ (nfix (fn-th-at 1 p))) (fn-th-at 2 p) (fn-th-at 3 p)
                      (fn-th-at 4 p) (fn-th-at 5 p) nil))

; The gate: fn-sn-completion-enabledp's article arm with the record
; supplied, and the context's generation the store's.
(defun fn-snh-enabledp (s h ctx)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (and (mbe :logic (fn-sn-statep s) :exec t)
       (equal (fn-sf-phase (fn-sn-files s)) :completing)
       (fn-snh-bindsp (fn-sn-node s) h)
       (equal (fn-sf-completion (fn-sn-files s))
              (cons (fn-record-sequence h) (fn-record-txid h)))
       (fn-snh-projection-okp (fn-sn-consumer s) (fn-record-sequence h)
                              (fn-sn-identity-next s))
       (fn-snh-topic-okp (fn-sn-topic s) (fn-record-sequence h))
       (fn-hc-p ctx)
       (fn-lace-p (fn-hc-delta ctx))
       (equal (fn-hc-generation ctx) (fn-sn-keyring-generation s))))

(verify-guards fn-snh-enabledp
  :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep)))))

(defun fn-sn-finish-held (s h ctx)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (if (fn-snh-enabledp s h ctx)
      (let* ((seq (fn-record-sequence h))
             (txid (fn-record-txid h))
             (node (fn-node-complete (fn-sn-node s) txid (fn-record-generation h)
                                     :durable))
             (files (fn-sf-core-completion (fn-sn-files s) seq txid)))
        (fn-sn-with-topic
         (fn-sn-with-consumer
          (fn-sn-advance-identity-next
           (fn-sn-update-accepted
            s (fn-sf-emit-success files seq txid) node
            (fn-stx-index-add (fn-sn-index s) (fn-hc-delta ctx))
            (fn-record-msgid h) (fn-hc-verdict ctx)))
          (fn-snh-projection-next (fn-sn-consumer s) (fn-sn-identity-next s)))
         (fn-snh-topic-next (fn-sn-topic s))))
    s))

(verify-guards fn-sn-finish-held
  :hints (("Goal" :in-theory
           (e/d (fn-sn-statep fn-snh-enabledp)
                (fn-sf-statep fn-node-statep fn-snh-bindsp
                 fn-node-pending-matchesp fn-sf-core-completion
                 fn-record-record-vocabulary fn-record-shape-vocabulary)))))

(defthm fn-sn-finish-held-refuses-a-stale-context
  (implies (not (equal (fn-hc-generation ctx) (fn-sn-keyring-generation s)))
           (equal (fn-sn-finish-held s h ctx) s)))

; -----------------------------------------------------------------------------
; The equation with fn-sn-finish on the article arm.

; After the flip the completing article row IS a held record (the history
; retains rows, books/held-record.lisp): fn-sn-finish's article arm reads its
; verdict and delta off the row's own context, as the held finish does.  So
; the equation is over the completing row itself, with no wire record and no
; bytes: the row's handle is the pending's handle (the payload hypothesis,
; which the maintained relation carries: fn-sn-record-bindsp compares it).

; A held row is no other kind of Store event (the carried readings by
; shape, books/store-events-carried.lisp).
(local
 (defthm fn-snh-record-is-no-other-kind
   (implies (fn-held-p w)
            (and (not (fn-store-retention-event-p w))
                 (not (fn-stxe-p w))
                 (not (fn-stxk-p w))
                 (not (fn-hstxa-p w))
                 (not (fn-cpe-eventp w))
                 (not (fn-th-topic-eventp w))))
   :hints (("Goal" :in-theory (union-theories '(fn-store-event-p) (theory 'minimal-theory))
            :use ((:instance fn-evc-class-by-shape-is-fn-held-p (x w))
                  (:instance fn-evc-class-by-shape-is-fn-store-retention-event-p (x w))
                  (:instance fn-evc-class-by-shape-is-fn-stxe-p (x w))
                  (:instance fn-evc-class-by-shape-is-fn-stxk-p (x w))
                  (:instance fn-evc-class-by-shape-is-fn-hstxa-p (x w))
                  (:instance fn-evc-class-by-shape-is-fn-cpe-eventp (x w))
                  (:instance fn-evc-class-by-shape-is-fn-th-topic-eventp (x w)))))))

(local
 (defthm fn-snh-store-event-fields-of-record
   (implies (fn-held-p w)
            (and (fn-store-event-p w)
                 (equal (fn-store-event-sequence w) (fn-record-sequence w))
                 (equal (fn-store-event-txid w) (fn-record-txid w))))
   :hints (("Goal" :in-theory (e/d (fn-store-event-p fn-store-event-sequence
                                    fn-store-event-txid)
                                   (fn-held-p))))))

; The consumer projection step on an article row.
(local (defthm fn-snh-projection-step-of-article
   (implies (fn-held-p w)
            (and (equal (equal (car (fn-cpe-projection-step c w n)) :ok)
                        (fn-snh-projection-okp c (fn-record-sequence w) n))
                 (implies (fn-snh-projection-okp c (fn-record-sequence w) n)
                          (equal (fn-cp-nth 1 (fn-cpe-projection-step c w n))
                                 (fn-snh-projection-next c n)))))
   :hints (("Goal" :in-theory (e/d (fn-cpe-projection-step fn-cp-nth)
                                   (fn-held-p fn-cpe-eventp))))))

; The topic prefix step on an article row.
(local
 (defthm fn-snh-th-at-of-prefix-state
   (and (equal (fn-th-at 0 (fn-th-prefix-state st nx sn ac an in tl)) st)
        (equal (fn-th-at 1 (fn-th-prefix-state st nx sn ac an in tl)) nx))
   :hints (("Goal" :in-theory (enable fn-th-prefix-state fn-th-at)))))

; A local administrator event satisfies every conjunct of the topic
; recognizer (its own shape supplies the three coordinates), so what is not
; a topic event is not a local administrator event.
(local (defthm fn-snh-not-topic-not-local-admin
   (implies (not (fn-th-topic-eventp w))
            (not (fn-th-local-admin-eventp w)))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-th-topic-eventp fn-th-local-admin-eventp eq)
                                              (theory 'minimal-theory))))))

(local (defthm fn-snh-record-is-not-local-admin
   (implies (fn-held-p w) (not (fn-th-local-admin-eventp w)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance fn-snh-not-topic-not-local-admin)
                  (:instance fn-snh-record-is-no-other-kind))))))

(local (defthm fn-snh-prefix-step-of-article
   (implies (fn-held-p w)
            (and (equal (equal (car (fn-th-prefix-step p w)) :ok)
                        (fn-snh-topic-okp p (fn-record-sequence w)))
                 (implies (fn-snh-topic-okp p (fn-record-sequence w))
                          (and (consp (fn-th-prefix-step p w))
                               (equal (fn-th-prefix-step p w) (fn-snh-topic-next p))))))
   :hints (("Goal" :in-theory (e/d (fn-th-prefix-step fn-th-at)
                                   (fn-th-local-admin-eventp fn-held-p))
            :use ((:instance fn-snh-record-is-no-other-kind))))))

; The row's binding to the pending transaction: the metadata reading is the
; store's whenever the row's handle is the pending's handle.
(local (defthm fn-snh-bindsp-is-record-bindsp
   (implies (and (fn-held-p h)
                 (equal (fn-record-payload h)
                        (fn-pending-payload (fn-state-pending (fn-node-acceptance node)))))
            (equal (fn-snh-bindsp node h) (fn-sn-record-bindsp node h)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-snh-bindsp fn-sn-record-bindsp fn-sn-pending-record
                                    fn-held-wire fn-record-internals)
                                   (fn-node-pending-matchesp fn-held-p))
            :use ((:instance fn-record-make-injective
                             (sequence (fn-record-sequence h)) (txid (fn-record-txid h))
                             (generation (fn-record-generation h)) (msgid (fn-record-msgid h))
                             (payload (fn-record-payload h)) (groups (fn-record-groups h))
                             (obligation-id (fn-record-obligation-id h))
                             (content-subject (fn-record-content-subject h))
                             (release-evidence (fn-record-release-evidence h))
                             (charge (fn-record-charge h)) (stamp (fn-record-stamp h))
                             (sequence-2 (fn-record-sequence h))
                             (txid-2 (fn-pending-txid (fn-state-pending (fn-node-acceptance node))))
                             (generation-2 (fn-pending-generation (fn-state-pending (fn-node-acceptance node))))
                             (msgid-2 (fn-pending-msgid (fn-state-pending (fn-node-acceptance node))))
                             (payload-2 (fn-pending-payload (fn-state-pending (fn-node-acceptance node))))
                             (groups-2 (fn-pending-groups (fn-state-pending (fn-node-acceptance node))))
                             (obligation-id-2 (fn-node-stage-id (fn-node-stage node)))
                             (content-subject-2 (fn-node-stage-subject (fn-node-stage node)))
                             (release-evidence-2 (fn-node-stage-evidence (fn-node-stage node)))
                             (charge-2 (fn-node-stage-charge (fn-node-stage node)))
                             (stamp-2 (fn-pending-stamp (fn-state-pending (fn-node-acceptance node))))))))))

; A store's keyring generation is a natural (fn-sn-statep carries it).
(local (defthm fn-snh-statep-generation
   (implies (fn-sn-statep s) (natp (fn-sn-keyring-generation s)))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (e/d (fn-sn-statep) (fn-sf-statep fn-node-statep))))))

; The article arm's topic result is an :ok prefix state.
(local (defthm fn-snh-topic-next-ok
   (and (consp (fn-snh-topic-next p))
        (equal (car (fn-snh-topic-next p)) :ok))
   :hints (("Goal" :in-theory (enable fn-snh-topic-next fn-th-prefix-state)))))

; KEYSTONE.  H is the completing row (`fn-sn-completion-record'), a held
; record whose handle is the pending's; CTX is the row's own context.  Then
; the held finish is the finish.
(defthm fn-sn-finish-held-is-finish
  (implies (and (fn-sn-statep s)
                (equal (fn-sn-completion-record s) h)
                (fn-held-p h)
                (equal (fn-record-payload h)
                       (fn-pending-payload (fn-state-pending (fn-node-acceptance (fn-sn-node s)))))
                (equal ctx (fn-held-context h)))
           (equal (fn-sn-finish-held s h ctx) (fn-sn-finish s)))
  :hints (("Goal" :in-theory (e/d (fn-sn-finish fn-sn-finish-held fn-snh-enabledp
                                   fn-sn-completion-enabledp fn-sn-completion-core-enabledp
                                   fn-sn-accepted-delta fn-sf-record-pair)
                                  (fn-snh-bindsp fn-sn-record-bindsp fn-sn-completion-record
                                   fn-node-pending-matchesp fn-sn-pending-record fn-held-p
                                   fn-sf-core-completion fn-sf-emit-success fn-node-complete
                                   fn-sn-update-accepted fn-sn-advance-identity-next
                                   fn-sn-with-consumer fn-sn-with-topic fn-stx-index-add
                                   fn-cpe-projection-step fn-th-prefix-step
                                   fn-snh-projection-okp fn-snh-projection-next
                                   fn-snh-topic-okp fn-snh-topic-next
                                   fn-record-record-vocabulary fn-record-shape-vocabulary
                                   fn-replay-apply-retention-event fn-replay-apply-record
                                   fn-replay-identity-step fn-sn-identity-context
                                   fn-sn-finish-identity fn-sn-update-indexed))
           :use ((:instance fn-snh-bindsp-is-record-bindsp (node (fn-sn-node s))))
           :do-not-induct t)))

(in-theory (disable fn-sn-finish-held fn-snh-enabledp fn-snh-bindsp))

; -----------------------------------------------------------------------------
; The context theorem: the keyring generation names the keyring.  Every
; transition the host applies leaves the keyring and its generation;
; `fn-sn-set-keyring', the one writer, advances the generation whenever it
; changes the keyring.  So a context whose generation is the store's was
; decided under the store's keyring.

; The state constructors every transition rebuilds through leave the two
; fields (fn-sn-make-v6 with the store's own keyring and generation).
(local (defthm fn-snh-keyring-of-updates
   (and (equal (fn-sn-keyring (fn-sn-update s f n)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-update s f n)) (fn-sn-keyring-generation s))
        (equal (fn-sn-keyring (fn-sn-update-indexed s f n i)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-update-indexed s f n i)) (fn-sn-keyring-generation s))
        (equal (fn-sn-keyring (fn-sn-update-accepted s f n i m v)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-update-accepted s f n i m v)) (fn-sn-keyring-generation s))
        (equal (fn-sn-keyring (fn-sn-update-replayed s f n i c)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-update-replayed s f n i c)) (fn-sn-keyring-generation s))
        (equal (fn-sn-keyring (fn-sn-with-consumer s c)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-with-consumer s c)) (fn-sn-keyring-generation s))
        (equal (fn-sn-keyring (fn-sn-with-topic s tp)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-with-topic s tp)) (fn-sn-keyring-generation s))
        (equal (fn-sn-keyring (fn-sn-with-event-index s e)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-with-event-index s e)) (fn-sn-keyring-generation s))
        (equal (fn-sn-keyring (fn-sn-advance-identity-next s)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-advance-identity-next s)) (fn-sn-keyring-generation s))
        (equal (fn-sn-keyring (fn-sn-finish-identity s f r n)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-finish-identity s f r n)) (fn-sn-keyring-generation s)))
   :hints (("Goal" :in-theory (e/d (fn-sn-update fn-sn-update-indexed fn-sn-update-accepted
                                    fn-sn-update-replayed fn-sn-with-consumer fn-sn-with-topic
                                    fn-sn-with-event-index fn-sn-advance-identity-next
                                    fn-sn-finish-identity)
                                   (fn-replay-identity-step fn-stx-index-add
                                    fn-sn-composite-delta fn-replay-verdict-pairs))))))

; The two readers as slots (4 and 6), for the configuration update, which
; writes slots 0, 1, 3 and 10 (fn-sn-with-configuration-preserves-unselected-slot).
(local (defthm fn-snh-keyring-is-nth
   (and (equal (fn-sn-keyring s) (nth 4 s))
        (equal (fn-sn-keyring-generation s) (nth 6 s)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-sn-keyring fn-sn-keyring-generation nth)))))

(local (defthm fn-snh-keyring-of-with-configuration
   (and (equal (fn-sn-keyring (fn-sn-with-configuration s g c n h)) (fn-sn-keyring s))
        (equal (fn-sn-keyring-generation (fn-sn-with-configuration s g c n h))
               (fn-sn-keyring-generation s)))
   :hints (("Goal" :in-theory (disable fn-sn-with-configuration nth update-nth
                                       fn-sn-keyring fn-sn-keyring-generation)
            :use ((:instance fn-snh-keyring-is-nth)
                  (:instance fn-snh-keyring-is-nth (s (fn-sn-with-configuration s g c n h)))
                  (:instance fn-sn-with-configuration-preserves-unselected-slot
                             (k 4) (groups g) (capacity c) (node n) (config-history h))
                  (:instance fn-sn-with-configuration-preserves-unselected-slot
                             (k 6) (groups g) (capacity c) (node n) (config-history h)))))))

; One lemma per transition, each opened alone over a minimal theory: its
; branches are the constructors above or the state itself.
(defmacro fn-snh-ctx-lemma (name call &rest defs)
  `(local (defthm ,name
     (and (equal (fn-sn-keyring ,call) (fn-sn-keyring s))
          (equal (fn-sn-keyring-generation ,call) (fn-sn-keyring-generation s)))
     :hints (("Goal" :in-theory (union-theories '(,@defs fn-snh-keyring-of-updates
                                                   fn-snh-keyring-of-with-configuration)
                                                (theory 'minimal-theory)))))))

(fn-snh-ctx-lemma fn-snh-ctx-prepare (fn-sn-prepare s r) fn-sn-prepare)
(fn-snh-ctx-lemma fn-snh-ctx-io (fn-sn-io s op res) fn-sn-io)
(fn-snh-ctx-lemma fn-snh-ctx-finish (fn-sn-finish s) fn-sn-finish)
(fn-snh-ctx-lemma fn-snh-ctx-finish-held (fn-sn-finish-held s h ctx) fn-sn-finish-held)
(fn-snh-ctx-lemma fn-snh-ctx-crash (fn-sn-crash s fc rc) fn-sn-crash)
(fn-snh-ctx-lemma fn-snh-ctx-recover (fn-sn-recover s) fn-sn-recover)
(fn-snh-ctx-lemma fn-snh-ctx-refuse (fn-sn-refuse-reservation s txid) fn-sn-refuse-reservation)
(fn-snh-ctx-lemma fn-snh-ctx-abort (fn-sn-known-abort s) fn-sn-known-abort)
(fn-snh-ctx-lemma fn-snh-ctx-prepare-retention (fn-sn-prepare-retention s e) fn-sn-prepare-retention)
(fn-snh-ctx-lemma fn-snh-ctx-prepare-identity (fn-sn-prepare-identity s e) fn-sn-prepare-identity)
(fn-snh-ctx-lemma fn-snh-ctx-prepare-consumer (fn-sn-prepare-consumer s e) fn-sn-prepare-consumer)
(fn-snh-ctx-lemma fn-snh-ctx-prepare-topic (fn-sn-prepare-topic s e) fn-sn-prepare-topic)
(fn-snh-ctx-lemma fn-snh-ctx-snt-step (fn-snt-step s event) fn-snt-step
                  fn-snh-ctx-prepare fn-snh-ctx-io fn-snh-ctx-finish fn-snh-ctx-crash
                  fn-snh-ctx-recover)
(fn-snh-ctx-lemma fn-snh-ctx-snrt-step (fn-snrt-step s event) fn-snrt-step
                  fn-snh-ctx-refuse fn-snh-ctx-abort fn-snh-ctx-prepare-retention
                  fn-snh-ctx-prepare-identity fn-snh-ctx-prepare-consumer
                  fn-snh-ctx-prepare-topic fn-snh-ctx-snt-step)

; The writer: the generation moves whenever the keyring does.
(local (defthm fn-snh-ctx-set-keyring
   (implies (equal (fn-sn-keyring-generation (fn-sn-set-keyring s keyring contexts))
                   (fn-sn-keyring-generation s))
            (equal (fn-sn-keyring (fn-sn-set-keyring s keyring contexts)) (fn-sn-keyring s)))
   :hints (("Goal" :in-theory (e/d (fn-sn-set-keyring)
                                   (fn-sn-statep fn-prin-keyringp fn-stx-index-of-store))))))

(defthm fn-sn-context-fixed-between-prepare-and-finish
  (and (equal (fn-sn-keyring (fn-snrt-step s event)) (fn-sn-keyring s))
       (equal (fn-sn-keyring-generation (fn-snrt-step s event))
              (fn-sn-keyring-generation s))
       (equal (fn-sn-keyring (fn-sn-io s operation result)) (fn-sn-keyring s))
       (equal (fn-sn-keyring-generation (fn-sn-io s operation result))
              (fn-sn-keyring-generation s))
       (equal (fn-sn-keyring (fn-sn-finish s)) (fn-sn-keyring s))
       (equal (fn-sn-keyring-generation (fn-sn-finish s)) (fn-sn-keyring-generation s))
       (equal (fn-sn-keyring (fn-sn-finish-held s h ctx)) (fn-sn-keyring s))
       (equal (fn-sn-keyring-generation (fn-sn-finish-held s h ctx))
              (fn-sn-keyring-generation s))
       (equal (fn-sn-keyring (fn-sn-with-configuration s groups capacity node history))
              (fn-sn-keyring s))
       (equal (fn-sn-keyring-generation (fn-sn-with-configuration s groups capacity node history))
              (fn-sn-keyring-generation s))
       (implies (equal (fn-sn-keyring-generation (fn-sn-set-keyring s keyring contexts))
                       (fn-sn-keyring-generation s))
                (equal (fn-sn-keyring (fn-sn-set-keyring s keyring contexts)) (fn-sn-keyring s))))
  :hints (("Goal" :in-theory (union-theories '(fn-snh-ctx-snrt-step fn-snh-ctx-io fn-snh-ctx-finish
                                                fn-snh-ctx-finish-held fn-snh-keyring-of-with-configuration
                                                fn-snh-ctx-set-keyring)
                                              (theory 'minimal-theory)))))

; unreachable-in-composition: no native host line calls fn-sn-set-keyring
; (host/store-node-host.lisp fn-store-sn-set-keyring is tools/run_store.py's).
; The negative of the phase gate the design offered: the writer changes the
; generation, so the O(1) generation compare in fn-snh-enabledp is exact.
(defthm fn-sn-set-keyring-advances-the-generation
  (implies (and (fn-sn-statep s) (fn-prin-keyringp keyring)
                (equal (fn-sf-phase (fn-sn-files s)) :ready)
                (not (eq (fn-sn-recontext-rows (fn-sf-records (fn-sn-files s)) contexts
                                               (1+ (fn-sn-keyring-generation s)))
                         :mismatch)))
           (equal (fn-sn-keyring-generation (fn-sn-set-keyring s keyring contexts))
                  (1+ (fn-sn-keyring-generation s))))
  :hints (("Goal" :in-theory (e/d (fn-sn-set-keyring) (fn-sn-statep)))))
