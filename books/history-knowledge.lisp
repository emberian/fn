; fn: the event history as the semantic backbone (row W8 of the 6.6.0 list;
; GPT-6's warranty review, warranty-quality-proof-engineering.md section 6;
; lane reclaim-equivalence, 2026-09-29).  Prefix `fn-hkn-' (docs/prefixes.md).
;
; What a history MEANS, and which transformations of it keep that meaning.
; Four things are decided here, each over the functions the host calls:
;
; 1. KNOWLEDGE.  `fn-hkn-knowledge' reads the event history (the octet
;    events `fn-rclp-events' rewrites, host/checkpoint-host.lisp
;    fn-store-log-reclaim-event) and the node's stage, and answers one of
;    five states: :not-accepted, :accepted-retained, :accepted-reclaimed,
;    :outcome-unresolved (a proposal staged and not in the readable history:
;    a lost acknowledgement, an indeterminate completion) and
;    :history-unavailable.  KEYSTONE `fn-hkn-reclamation-never-forgets-an-
;    acceptance': the rewrite the host applies to the history turns
;    :accepted-retained into :accepted-reclaimed or leaves it, and changes no
;    other answer -- the current absence of a payload never collapses to
;    :not-accepted, and an identity the history does not hold is never
;    invented by it.
;
; 2. ACKNOWLEDGEMENT IDENTIFIES COMMITMENT.  KEYSTONE
;    `fn-hkn-acceptance-records-subject-principal-and-undertaking': the
;    replay of an article record (books/replay.lisp fn-replay-apply-record,
;    the step every open runs) that accepts binds the record's Message-ID
;    to the record's CONTENT SUBJECT (books/subject-id-buffer.lisp: the
;    digest of the accepted octets, not the mutable transport headers nor
;    the stored rendering) and its obligation id, and holds the pin with the
;    record's own release EVIDENCE (the principal and policy context, a
;    `fn-provp' value: :post, :peer-transit, :bp-receive, :local) and CHARGE
;    (the undertaking).  Accepted(op) => Recorded(op, subject, principal,
;    policy context, undertakings).  Nothing in the bound values is a
;    function of the replay's own inputs (the groups and capacity of the
;    open), which is item 3: replay copies yesterday's authorization, it
;    never derives one from today's policy
;    (`fn-hkn-replay-binds-the-recorded-evidence-not-the-policy').
;
; 3. THE LOGICAL RELEASE, then the continuation language.  Reclamation is a
;    semantic transition first: `fn-hkn-release' is the node with the
;    article's payload at the tombstone (books/store-reclaim.lisp
;    fn-rcl-reclaim-state) and its archive pin's charge at the one permanent
;    history unit (what the tombstoned record's replay admits,
;    books/store-reclaim-pack.lisp fn-rclp-tombstoned).  The physical
;    rewrite implements exactly that (the pack's decode theorem).  Over the
;    released node the continuation language answers as over the original:
;      a retry of the original identity, or a CONFLICTING retry (any
;        payload, any groups): refused after as before
;        (`fn-hkn-retry-refused-after-release-as-before');
;      a receipt or a release naming an obligation: discharges the same
;        obligation or none (`fn-hkn-release-discharges-the-same-obligation');
;      a query by Message-ID or number: books/store-reclaim.lisp
;        fn-rcl-reclaim-keeps-every-binding / -keeps-the-numbering;
;      a new obligation id: known after as before
;        (`fn-hkn-release-keeps-every-known-id');
;      a policy change followed by a further reclaim: nothing is rewritten
;        twice (books/store-reclaim-pack.lisp fn-rclp-events-idempotent,
;        fn-rclp-a-reclaimed-event-stays-reclaimed).
;    The ONE observable difference is stated, not hidden: the release frees
;    exactly the content charge (`fn-hkn-release-frees-exactly-the-content-
;    charge'), so a POST the original refused for capacity may be admitted
;    after the release, and only such a POST
;    (`fn-hkn-release-enables-only-what-the-freed-charge-affords').  That is
;    the explicit logical change of reclamation (STO-017, D03); the naive
;    "every continuation observes the same" is FALSE for it, and the teeth
;    (tests/acl2/history-knowledge-tests.lisp) say so with a must-fail.
;
; 4. REFUSAL FOOTPRINTS.  A refused node transition is the identity, per
;    entry, by definition (`fn-hkn-refused-prepare-is-the-identity-by-
;    definition', `-unmatched-complete-', `-unmatched-release-'); the one
;    refusal with a footprint, the full-store POST, consumes exactly one
;    transaction id (books/refusal-effect.lisp
;    fn-rfx-refused-post-consumes-one-txid), and that path never touches
;    the recovery barriers (`fn-hkn-refusal-keeps-the-recovery-barriers').
;    The bound: the frontier is a uint32 and `fn-sf-start-frontier' refuses
;    at *fn-sf-max-uint*, so the refused path consumes at most the ids
;    between the frontier and the ceiling, never a barrier and never a
;    record.
(in-package "ACL2")
(include-book "store-reclaim-pack")
(include-book "replay")

; Definitions closed by default: the codecs, the reclaim decision, the
; record accessors and the whole-state recognizers open only in hints.
(local (in-theory (disable fn-rcl-tombstone-of fn-rcl-tombstonep fn-rcl-reclaimable
                           fn-rclp-ctx-reclaimable fn-record-p
                           fn-record-result-okp fn-record-result-record
                           fn-record-msgid fn-record-payload fn-record-groups
                           fn-record-obligation-id fn-record-content-subject
                           fn-record-release-evidence fn-record-charge
                           fn-record-stamp fn-record-txid fn-record-generation
                           fn-record-sequence
                           fn-node-statep fn-statep fn-retain-statep
                           fn-retain-admissiblep fn-accept-prepare fn-accept-complete
                           fn-node-stagep fn-held-p fn-hstxa-p
                           fn-store-event-p fn-store-event-sequence fn-store-event-txid
                           fn-stxe-p fn-stxk-p fn-stxa-p fn-store-retention-event-p
                           fn-cpe-eventp fn-th-topic-eventp
                           fn-replay-composite-record fn-replay-composite-held
                           fn-replay-apply-retention-event fn-replay-apply-identity-neutral
                           fn-replay-advance-txid)))

; -----------------------------------------------------------------------------
; 1. Knowledge over the event history.

(defconst *fn-hkn-states*
  '(:not-accepted :accepted-retained :accepted-reclaimed
    :outcome-unresolved :history-unavailable))

; Whether an event decodes to a record, and the record it holds (read only
; when it does).
(defun fn-hkn-event-okp (octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-result-okp (fn-record-decode-exact octets)))

(defun fn-hkn-record-of (octets)
  (declare (xargs :guard t :verify-guards nil))
  (fn-record-result-record (fn-record-decode-exact octets)))

; The first event whose record names MSGID (the one the walk of
; `fn-find-article' binds, books/store-reclaim-pack.lisp
; fn-rclp-article-index-finds-the-article), wrapped in a one-element list,
; or NIL when no event names it.
(defun fn-hkn-find-event (events msgid)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp events)
      (if (and (fn-hkn-event-okp (car events))
               (equal (fn-record-msgid (fn-hkn-record-of (car events))) msgid))
          (list (car events))
        (fn-hkn-find-event (cdr events) msgid))
    nil))

; AVAILABLE: the history can be read (nil past a dropped segment, a damaged
; checkpoint, a store the node cannot open).  STAGED: the Message-ID of the
; node's staged proposal, or NIL (books/node.lisp fn-node-stage-msgid).
(defun fn-hkn-knowledge (available events staged msgid)
  (declare (xargs :guard t :verify-guards nil))
  (if (not available)
      :history-unavailable
    (let ((found (fn-hkn-find-event events msgid)))
      (cond ((consp found)
             (if (fn-rcl-tombstonep (fn-record-payload (fn-hkn-record-of (car found))))
                 :accepted-reclaimed
               :accepted-retained))
            ((equal staged msgid) :outcome-unresolved)
            (t :not-accepted)))))

(defthm fn-hkn-knowledge-is-one-of-the-five-states
  (member-eq (fn-hkn-knowledge available events staged msgid) *fn-hkn-states*))

(local
 (defthm fn-hkn-record-make-is-a-cons
   (consp (fn-record-make sequence txid generation msgid payload groups
                          obligation-id content-subject release-evidence
                          charge stamp))
   :hints (("Goal" :in-theory (enable fn-record-make)))))

(defthm fn-hkn-tombstoned-keeps-the-identity
  (and (consp (fn-rclp-tombstoned r))
       (equal (fn-record-msgid (fn-rclp-tombstoned r)) (fn-record-msgid r))
       (equal (fn-record-obligation-id (fn-rclp-tombstoned r)) (fn-record-obligation-id r))
       (equal (fn-record-content-subject (fn-rclp-tombstoned r))
              (fn-record-content-subject r))
       (equal (fn-record-release-evidence (fn-rclp-tombstoned r))
              (fn-record-release-evidence r))
       (equal (fn-record-txid (fn-rclp-tombstoned r)) (fn-record-txid r))
       (equal (fn-record-groups (fn-rclp-tombstoned r)) (fn-record-groups r))
       (equal (fn-record-charge (fn-rclp-tombstoned r)) *fn-rclp-history-unit*)
       (equal (fn-record-payload (fn-rclp-tombstoned r))
              (fn-rcl-tombstone-of (fn-record-payload r)
                                   (fn-record-string-octets (fn-record-msgid r)))))
  :hints (("Goal" :in-theory (enable fn-rclp-tombstoned))))

(local (in-theory (disable fn-rclp-tombstoned)))

; The tombstone of a payload is a tombstone (books/store-reclaim.lisp
; fn-rcl-tombstone-of-fields names its shape); stated here as the fact the
; knowledge reads.
(defthm fn-hkn-tombstone-of-is-a-tombstone
  (fn-rcl-tombstonep (fn-rcl-tombstone-of payload agent))
  :hints (("Goal" :in-theory (enable fn-rcl-tombstonep fn-rcl-tombstone-of))))

; What the rewrite does to one event's record.
(local
 (defthm fn-hkn-rewrites-p-decodes
   (implies (fn-rclp-rewrites-p octets ctx)
            (fn-hkn-event-okp octets))
   :hints (("Goal" :in-theory (enable fn-rclp-rewrites-p)))))

(local
 (defthm fn-hkn-rewrites-p-is-not-a-tombstone
   (implies (fn-rclp-rewrites-p octets ctx)
            (not (fn-rcl-tombstonep (fn-record-payload (fn-hkn-record-of octets)))))
   :hints (("Goal" :in-theory (enable fn-rclp-rewrites-p)))))

(defthm fn-hkn-record-of-a-rewritten-event
  (implies (fn-rclp-rewrites-p octets ctx)
           (and (fn-hkn-event-okp (fn-rclp-event octets ctx))
                (equal (fn-hkn-record-of (fn-rclp-event octets ctx))
                       (fn-rclp-tombstoned (fn-hkn-record-of octets)))))
  :hints (("Goal" :use fn-rclp-event-decodes-to-the-tombstoned-record
                  :in-theory (e/d () (fn-rclp-event fn-rclp-tombstoned
                                      fn-rclp-event-decodes-to-the-tombstoned-record)))))

(defthm fn-hkn-record-of-an-unrewritten-event
  (implies (not (fn-rclp-rewrites-p octets ctx))
           (and (equal (fn-hkn-event-okp (fn-rclp-event octets ctx))
                       (fn-hkn-event-okp octets))
                (equal (fn-hkn-record-of (fn-rclp-event octets ctx))
                       (fn-hkn-record-of octets))))
  :hints (("Goal" :in-theory (disable fn-hkn-record-of fn-hkn-event-okp))))

(local
 (defthm fn-hkn-rclp-event-names-the-same-msgid
   (and (equal (fn-hkn-event-okp (fn-rclp-event octets ctx))
               (fn-hkn-event-okp octets))
        (equal (fn-record-msgid (fn-hkn-record-of (fn-rclp-event octets ctx)))
               (fn-record-msgid (fn-hkn-record-of octets))))
   :hints (("Goal" :cases ((fn-rclp-rewrites-p octets ctx))
                   :in-theory (disable fn-hkn-record-of fn-hkn-event-okp fn-rclp-event
                                       fn-rclp-rewrites-p)))))

(defthm fn-hkn-find-event-after-rewrite
  (equal (fn-hkn-find-event (fn-rclp-events events ctx) msgid)
         (if (consp (fn-hkn-find-event events msgid))
             (list (fn-rclp-event (car (fn-hkn-find-event events msgid)) ctx))
           nil))
  :hints (("Goal" :induct (fn-hkn-find-event events msgid)
                  :in-theory (disable fn-hkn-record-of fn-hkn-event-okp fn-rclp-event
                                      fn-rclp-rewrites-p))))

;  KEYSTONE (PRF-997).  The host's rewrite of the history (fn-rclp-events,
; the function fn-store-log-reclaim-event applies per record) changes the
; knowledge of a Message-ID in exactly one way: :accepted-retained may
; become :accepted-reclaimed.  It never answers :not-accepted where the
; history answered an acceptance, never invents an acceptance, and leaves
; :outcome-unresolved and :history-unavailable as they were.
(defthm fn-hkn-reclamation-never-forgets-an-acceptance
  (let ((before (fn-hkn-knowledge available events staged msgid))
        (after (fn-hkn-knowledge available (fn-rclp-events events ctx) staged msgid)))
    (and (equal (equal after :not-accepted) (equal before :not-accepted))
         (equal (equal after :outcome-unresolved) (equal before :outcome-unresolved))
         (equal (equal after :history-unavailable) (equal before :history-unavailable))
         (implies (equal before :accepted-reclaimed) (equal after :accepted-reclaimed))
         (implies (equal before :accepted-retained)
                  (member-eq after '(:accepted-retained :accepted-reclaimed)))))
  :hints (("Goal" :in-theory (disable fn-hkn-record-of fn-hkn-event-okp fn-rclp-event
                                      fn-rclp-events fn-hkn-find-event fn-rclp-rewrites-p)
                  :cases ((fn-rclp-rewrites-p (car (fn-hkn-find-event events msgid)) ctx)))))

; -----------------------------------------------------------------------------
; 2. Acknowledgement identifies commitment.

; The plain article-record branch of the replay step: not a retention event,
; not an identity or configuration or topic event, not a retained composite
; row (those carry the article inside; the theorem for them is
; books/store-intern.lisp's).
(defun fn-hkn-plain-article-record-p (record)
  (declare (xargs :guard t :verify-guards nil))
  (and (not (fn-store-retention-event-p record))
       (not (fn-stxe-p record)) (not (fn-stxk-p record))
       (not (fn-cpe-eventp record)) (not (fn-th-topic-eventp record))
       (not (fn-hstxa-p record))))

; The replay step advances an idle node over a known-aborted gap before it
; prepares (books/replay.lisp fn-replay-advance-txid): nothing is staged
; after the advance, so the stage the completion reads is the prepare's.
(local
 (defthm fn-hkn-advance-keeps-an-empty-stage
   (implies (not (fn-node-stage node))
            (equal (fn-node-stage (fn-replay-advance-txid node txid)) nil))
   :hints (("Goal" :in-theory (enable (:definition fn-replay-advance-txid))))))

;  KEYSTONE (PRF-997).  Accepted(op) => Recorded(op, subject, principal,
; policy context, undertakings).  When the replay step accepts a plain
; article record, the node it reaches binds the record's Message-ID to the
; record's content subject and obligation id, holds the pin with the
; record's own evidence and charge under the :archive undertaking, and has
; nothing staged.  Every bound value is the record's: none is the replay's.
(defthm fn-hkn-acceptance-records-subject-principal-and-undertaking
  (let ((n (fn-replay-apply-record node record)))
    (implies (and n (fn-hkn-plain-article-record-p record))
             (and (equal (fn-node-find-binding (fn-record-msgid record)
                                               (fn-node-bindings n))
                         (fn-node-make-binding (fn-record-msgid record)
                                               (fn-record-content-subject record)
                                               (fn-record-obligation-id record)))
                  (equal (fn-retain-find-id (fn-record-obligation-id record)
                                            (fn-retain-pins (fn-node-retention n)))
                         (fn-retain-make-obligation (fn-record-obligation-id record)
                                                    (fn-record-content-subject record)
                                                    :archive
                                                    (fn-record-release-evidence record)
                                                    (fn-record-charge record)))
                  (equal (fn-node-stage n) nil))))
  :hints (("Goal" :in-theory (enable fn-replay-apply-record fn-node-prepare
                                     fn-node-complete fn-node-pending-matchesp
                                     fn-retain-admit))))

; 3 (provenance).  The replay's own inputs -- the node it stands at, the
; groups and capacity of the open -- decide only WHETHER the record is
; accepted; what is bound is the record's.  Replaying under today's policy
; cannot invent yesterday's authorization: the evidence in the pin is the
; evidence in the history, or there is no pin.
(defthm fn-hkn-replay-binds-the-recorded-evidence-not-the-policy
  (let ((n (fn-replay-apply-record node record)))
    (implies (and n (fn-hkn-plain-article-record-p record))
             (equal (fn-retain-obligation-evidence
                     (fn-retain-find-id (fn-record-obligation-id record)
                                        (fn-retain-pins (fn-node-retention n))))
                    (fn-record-release-evidence record))))
  :hints (("Goal" :use fn-hkn-acceptance-records-subject-principal-and-undertaking
                  :in-theory (disable fn-hkn-acceptance-records-subject-principal-and-undertaking
                                      fn-replay-apply-record))))

; -----------------------------------------------------------------------------
; 3. The logical release and the continuation language.

; The pin with its charge at the one permanent history unit.
(defun fn-hkn-reduce-pin (pin)
  (declare (xargs :guard t :verify-guards nil))
  (fn-retain-make-obligation (fn-retain-obligation-id pin)
                             (fn-retain-obligation-subject pin)
                             (fn-retain-obligation-kind pin)
                             (fn-retain-obligation-evidence pin)
                             *fn-rclp-history-unit*))

(defun fn-hkn-reduce-pins (pins id)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pins)
      (cons (if (equal (fn-retain-obligation-id (car pins)) id)
                (fn-hkn-reduce-pin (car pins))
              (car pins))
            (fn-hkn-reduce-pins (cdr pins) id))
    pins))

; The retention ledger after the logical release of obligation ID: the pin
; stays (every bound article keeps a live pin, fn-node-statep), at the
; history unit; the reserved sum drops by the content charge.
(defun fn-hkn-release-retention (r id)
  (declare (xargs :guard t :verify-guards nil))
  (let ((pin (fn-retain-find-id id (fn-retain-pins r))))
    (if (consp pin)
        (fn-retain-make-state (fn-retain-capacity r)
                              (+ *fn-rclp-history-unit*
                                 (- (fn-retain-reserved r)
                                    (fn-retain-obligation-charge pin)))
                              (fn-hkn-reduce-pins (fn-retain-pins r) id)
                              (fn-retain-releases r))
      r)))

; The node after the logical release of MSGID's content: the acceptance
; reclaimed (the payload at the tombstone handle TOMB), the article's pin
; released to the history unit, the stage and the bindings untouched.
(defun fn-hkn-release (node msgid tomb)
  (declare (xargs :guard t :verify-guards nil))
  (let ((b (fn-node-find-binding msgid (fn-node-bindings node))))
    (fn-node-make-state
     (fn-rcl-reclaim-state (fn-node-acceptance node) msgid tomb)
     (if b
         (fn-hkn-release-retention (fn-node-retention node) (fn-node-binding-id b))
       (fn-node-retention node))
     (fn-node-stage node)
     (fn-node-bindings node))))

(defthm fn-hkn-release-keeps-the-stage-and-the-bindings-by-definition
  (and (equal (fn-node-stage (fn-hkn-release node msgid tomb)) (fn-node-stage node))
       (equal (fn-node-bindings (fn-hkn-release node msgid tomb))
              (fn-node-bindings node))))

(defthm fn-hkn-reduce-pins-keeps-the-ids
  (equal (fn-retain-obligation-ids (fn-hkn-reduce-pins pins id))
         (fn-retain-obligation-ids pins))
  :hints (("Goal" :in-theory (enable fn-retain-obligation-ids))))

(defthm fn-hkn-reduce-pin-keeps-the-identifying-fields
  (and (consp (fn-hkn-reduce-pin pin))
       (equal (fn-retain-obligation-id (fn-hkn-reduce-pin pin))
              (fn-retain-obligation-id pin))
       (equal (fn-retain-obligation-subject (fn-hkn-reduce-pin pin))
              (fn-retain-obligation-subject pin))
       (equal (fn-retain-obligation-kind (fn-hkn-reduce-pin pin))
              (fn-retain-obligation-kind pin))
       (equal (fn-retain-obligation-evidence (fn-hkn-reduce-pin pin))
              (fn-retain-obligation-evidence pin))
       (equal (fn-retain-obligation-charge (fn-hkn-reduce-pin pin))
              *fn-rclp-history-unit*))
  :hints (("Goal" :in-theory (enable fn-hkn-reduce-pin))))

(local (in-theory (disable fn-hkn-reduce-pin)))

; The walk finds the same position after the reduction (every element keeps
; its id), so the found pin is the reduced one exactly when it is the one
; reduced.  No hypothesis: over any list.
(defthm fn-hkn-find-id-after-reduce
  (equal (fn-retain-find-id x (fn-hkn-reduce-pins pins id))
         (if (and (equal x id) (fn-retain-pin-id-scanp id pins))
             (fn-hkn-reduce-pin (fn-retain-find-id id pins))
           (fn-retain-find-id x pins)))
  :hints (("Goal" :induct (fn-retain-find-id x pins))))

(defthm fn-hkn-a-found-pin-is-scanned
  (implies (consp (fn-retain-find-id id pins))
           (fn-retain-pin-id-scanp id pins)))

; A receipt or a release matches by id, subject, kind and evidence, never
; by charge: the reduced pin matches exactly what the pin matched.
(defthm fn-hkn-matching-release-ignores-the-charge
  (implies (consp pin)
           (equal (fn-retain-matching-releasep (fn-hkn-reduce-pin pin)
                                               id subject kind evidence)
                  (fn-retain-matching-releasep pin id subject kind evidence)))
  :hints (("Goal" :in-theory (enable fn-hkn-reduce-pin))))

; Continuation: a new obligation id.  Known after the release exactly when
; known before, so admission by identity is unchanged.
(defthm fn-hkn-release-keeps-every-known-id
  (equal (fn-retain-known-idp x
                              (fn-retain-pins (fn-hkn-release-retention r id))
                              (fn-retain-releases (fn-hkn-release-retention r id)))
         (fn-retain-known-idp x (fn-retain-pins r) (fn-retain-releases r))))

; Continuation: a receipt or a release (books/retention.lisp
; fn-retain-release).  After the logical release of ID the request
; discharges the same obligation it discharged before, or none: the second
; failure shape ("dropping one dependency lets a later receipt discharge
; the wrong obligation") cannot occur, because the release keeps every pin
; and every identifying field of it.
(defthm fn-hkn-release-discharges-the-same-obligation
  (equal (fn-retain-matching-releasep
          (fn-retain-find-id x (fn-retain-pins (fn-hkn-release-retention r id)))
          x subject kind evidence)
         (fn-retain-matching-releasep
          (fn-retain-find-id x (fn-retain-pins r))
          x subject kind evidence))
  :hints (("Goal" :cases ((equal x id)))))

; The one observable change, exactly: the reserved sum drops by the content
; charge less the history unit, and nothing else of the ledger moves.
(defthm fn-hkn-release-frees-exactly-the-content-charge
  (implies (consp (fn-retain-find-id id (fn-retain-pins r)))
           (and (equal (fn-retain-reserved (fn-hkn-release-retention r id))
                       (+ *fn-rclp-history-unit*
                          (- (fn-retain-reserved r)
                             (fn-retain-obligation-charge
                              (fn-retain-find-id id (fn-retain-pins r))))))
                (equal (fn-retain-capacity (fn-hkn-release-retention r id))
                       (fn-retain-capacity r))
                (equal (fn-retain-releases (fn-hkn-release-retention r id))
                       (fn-retain-releases r)))))

; What the release newly enables, and only that: a request the ledger
; refused before and admits after was refused for capacity alone -- every
; other conjunct of admissibility held -- and fits the freed charge.  This
; is the explicit logical change reclamation makes (STO-017, D03); the
; naive equivalence of every continuation is false exactly here.
(defthm fn-hkn-release-enables-only-what-the-freed-charge-affords
  (implies (and (fn-retain-statep r)
                (not (fn-retain-admissiblep r x subject kind evidence charge))
                (fn-retain-admissiblep (fn-hkn-release-retention r id)
                                       x subject kind evidence charge))
           (and (stringp x) (stringp subject) (fn-retain-kindp kind)
                (fn-provp evidence) (posp charge)
                (not (fn-retain-known-idp x (fn-retain-pins r) (fn-retain-releases r)))
                (< (fn-retain-capacity r) (+ (fn-retain-reserved r) charge))
                (<= (+ (fn-retain-reserved (fn-hkn-release-retention r id)) charge)
                    (fn-retain-capacity r))))
  :hints (("Goal" :in-theory (enable fn-retain-admissiblep fn-hkn-release-retention)
                  :use ((:instance fn-hkn-release-keeps-every-known-id)))))

; Continuation: a retry of the original identity, or a conflicting retry
; (the same Message-ID with any payload and any groups).  Refused after the
; release exactly as before: the acceptance keeps the duplicate history
; (books/store-reclaim.lisp fn-rcl-reclaim-keeps-the-duplicate-history), so
; the first failure shape ("reclaiming an identity record lets a
; conflicting retry be accepted later") cannot occur.
(local
 (defthm fn-hkn-articles-of-reclaim-state
   (equal (fn-acceptedp m (fn-state-articles (fn-rcl-reclaim-state s msgid tomb)))
          (fn-acceptedp m (fn-state-articles s)))
   :hints (("Goal" :in-theory (enable fn-rcl-reclaim-state)))))

(local
 (defthm fn-hkn-accept-prepare-refuses-a-duplicate
   (implies (fn-acceptedp msgid (fn-state-articles s))
            (equal (fn-accept-prepare s generation msgid payload groups stamp) s))
   :hints (("Goal" :in-theory (enable fn-accept-prepare)))))

(defthm fn-hkn-retry-refused-after-release-as-before
  (implies (fn-acceptedp msgid (fn-state-articles (fn-node-acceptance node)))
           (and (equal (fn-node-prepare (fn-hkn-release node m tomb)
                                        generation msgid payload groups
                                        id subject evidence charge stamp)
                       (fn-hkn-release node m tomb))
                (equal (fn-node-prepare node generation msgid payload groups
                                        id subject evidence charge stamp)
                       node)))
  :hints (("Goal" :in-theory (e/d (fn-node-prepare) (fn-hkn-release-retention
                                                     fn-rcl-reclaim-state)))))

; -----------------------------------------------------------------------------
; 4. Refusal footprints.

; A prepare either stages (a stage is present afterwards) or is the
; identity: the refused prepare has no footprint.
(defthm fn-hkn-refused-prepare-is-the-identity-by-definition
  (or (equal (fn-node-prepare s generation msgid payload groups
                              id subject evidence charge stamp)
             s)
      (consp (fn-node-stage (fn-node-prepare s generation msgid payload groups
                                             id subject evidence charge stamp))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-node-prepare))))

(defthm fn-hkn-unmatched-complete-is-the-identity-by-definition
  (implies (not (fn-node-pending-matchesp s txid generation))
           (equal (fn-node-complete s txid generation completion-status) s))
  :hints (("Goal" :in-theory (enable fn-node-complete))))

(defthm fn-hkn-unmatched-release-is-the-identity-by-definition
  (implies (not (fn-retain-matching-releasep
                 (fn-retain-find-id id (fn-retain-pins s)) id subject kind evidence))
           (equal (fn-retain-release s id subject kind evidence) s))
  :hints (("Goal" :in-theory (enable fn-retain-release))))

; The full-store POST's footprint is one transaction id
; (books/refusal-effect.lisp fn-rfx-refused-post-consumes-one-txid).  The
; steps of that path -- the frontier's four results and the refusal -- keep
; the recovery barriers: the refused path never spends the recovery
; reserve.
(defthm fn-hkn-refusal-keeps-the-recovery-barriers
  (and (equal (fn-sf-barriers (fn-sf-start-frontier s)) (fn-sf-barriers s))
       (equal (fn-sf-barriers (fn-sf-frontier-file-result s result)) (fn-sf-barriers s))
       (equal (fn-sf-barriers (fn-sf-frontier-replace-result s result)) (fn-sf-barriers s))
       (equal (fn-sf-barriers (fn-sf-frontier-dir-result s result)) (fn-sf-barriers s))
       (equal (fn-sf-barriers (fn-sf-refuse-reservation s txid)) (fn-sf-barriers s)))
  :hints (("Goal" :in-theory (enable fn-sf-start-frontier fn-sf-frontier-file-result
                                     fn-sf-frontier-replace-result
                                     fn-sf-frontier-dir-result
                                     fn-sf-refuse-reservation))))

; The bound: a frontier at the ceiling reserves nothing more.
(defthm fn-hkn-frontier-at-the-ceiling-reserves-nothing
  (implies (not (< (fn-sf-frontier s) *fn-sf-max-uint*))
           (equal (fn-sf-start-frontier s) s))
  :hints (("Goal" :in-theory (enable fn-sf-start-frontier))))
