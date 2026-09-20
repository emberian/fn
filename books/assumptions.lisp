; fn's named assumptions as constrained functions.
;
; specs/failures.md names eight assumptions.  Until this book existed they were
; prose, which the 2026-09-18 independent review recorded as an assurance
; discipline gap: "There is no `encapsulate' in the tree.  A-DURABILITY,
; A-HOST, A-CRYPTO, A-PEER, A-POLICY exist only as prose."  A named assumption
; is now an `encapsulate' with a local witness and the minimal constraint the
; theorems that depend on it would need as a hypothesis.
;
; Three things each encapsulate buys, and one it does not:
;
;   * The assumption is mechanically listable.  `tools/ledger.py' counts
;     encapsulates; a grep for `fn-assume-' finds every dependent.
;   * Its satisfiability is proved once, by the local witness.  An assumption
;     no function can satisfy is a proof that the deployment is impossible, and
;     ACL2 refuses the encapsulate rather than letting it stand.
;   * Functional instantiation is the platform-qualification hook.  A
;     qualification profile supplies a concrete function and discharges the
;     constraints; `:functional-instance' then carries every theorem that took
;     the assumption as a hypothesis down to that profile.  See
;     docs/proofs.md, "Qualifying a platform against A-DURABILITY".
;
;   * It does not make any theorem depend on the assumption.  Each constraint
;     below carries a comment naming the theorems that should eventually take
;     it as a hypothesis.  Until they do, this book states the assumptions; it
;     does not yet discharge or apply them.  That is C1-14 and C1-15 work.
;
; Until 2026-09-20 this book deliberately included nothing: its constraints were
; about abstract values, not about any particular book's state representation,
; so that a later refinement could instantiate them wherever the corresponding
; theorem lives.  A-CRASH-IMAGE and A-CRYPTO-TRAILER break that, and are the
; first assumptions in the tree that are NOT strawmen: they constrain
; `fn-bs-crash-imagep' and `fn-bs-torn-variantp', the byte model's own
; predicates, so that the theorems depending on them are about the storage this
; node actually runs on.  The price is one include-book: `byte-store-invariants',
; which carries `books/byte-store' and `books/frame'.  There is no cycle --
; nothing in the byte-store closure includes this book -- and the alternative,
; a second assumptions book, is the twin the review told us to delete.
;
; A-CRYPTO is not here.  `books/crypto-seam.lisp' owns the digest and signature
; seam (`fn-digest', `fn-sig-verify'); defining a second constrained crypto
; function would be exactly the twin the review told us to delete.

(in-package "ACL2")
(include-book "byte-store-invariants")

; -----------------------------------------------------------------------------
; A-DURABILITY.  "A completed platform barrier preserves the named bytes and
; necessary namespace updates across a modeled crash."
;
; The crash image is a function of what a completed barrier made stable and
; what was written without one.  Two constraints: a crash cannot lose a
; barriered record, and a crash cannot invent one.
;
; Theorems that should take this as a hypothesis, rather than building it into
; `fn-sf-crash' (books/store-files.lisp:463) as the review's D5 records:
;   fn-sf-stable-records-prefix-of-crash          books/store-files.lisp
;   fn-sf-prior-success-has-record-after-one-crash books/store-files.lisp
;   fn-sf-crash-preserves-state                   books/store-files.lisp
;   fn-sf-prior-emitted-success-retained-by-run-trace  books/store-files-traces.lisp
;   fn-snrt-acknowledged-history-retained-through-mixed-trace
;                                                 books/store-node-resolution-traces.lisp
; The five-barrier gate `fn-sf-phase-shapep' (books/store-files.lisp:167) is
; what decides which records are in the BARRIERED argument at a crash point.

(encapsulate
  (((fn-assume-durability-image * *) => *))

  (local (defun fn-assume-durability-image (barriered unbarriered)
           (declare (ignore unbarriered))
           barriered))

  ; A completed barrier is what survives.  This is the whole positive content
  ; of A-DURABILITY; the platform qualification must establish it for the
  ; selected device, filesystem and barrier call.
  (defthm fn-assume-durability-retains-barriered
    (implies (member-equal record barriered)
             (member-equal record (fn-assume-durability-image barriered unbarriered))))

  ; A crash invents nothing.  Without this, a "surviving" record need not have
  ; been written at all, and record survival would say nothing about history.
  (defthm fn-assume-durability-invents-nothing
    (implies (member-equal record (fn-assume-durability-image barriered unbarriered))
             (or (member-equal record barriered)
                 (member-equal record unbarriered)))
    :rule-classes nil))

; -----------------------------------------------------------------------------
; A-WRITE-ISOLATION.  "Later incomplete writes cannot damage previously durable
; committed storage outside the modeled write unit."
;
; Stated over write units so that the sector-sharing case specs/failures.md
; warns about (appending after a committed record in the same physical sector)
; is the case the qualification has to rule out: a unit that shares a sector
; with a pending write is not isolated, and the layout must say so.
;
; Theorems that should take this as a hypothesis:
;   fn-sf-stable-records-prefix-of-crash          books/store-files.lisp
;   fn-sf-surviving-candidate-is-exact-and-dominated  books/store-files.lisp
;   fn-sn-open-observed-success-exact-history     books/store-observed.lisp
; and every recovery gate that reads a record written before the pending one.

(encapsulate
  (((fn-assume-write-isolation-observe * *) => *))

  (local (defun fn-assume-write-isolation-observe (committed pending)
           (declare (ignore pending))
           committed))

  ; A committed unit is still there after an unrelated incomplete write.
  (defthm fn-assume-write-isolation-retains-committed
    (implies (member-equal unit committed)
             (member-equal unit (fn-assume-write-isolation-observe committed pending))))

  ; Nothing appears that was neither committed nor pending: an incomplete write
  ; cannot fabricate a committed unit out of a torn neighbour.
  (defthm fn-assume-write-isolation-adds-nothing-foreign
    (implies (and (member-equal unit (fn-assume-write-isolation-observe committed pending))
                  (not (member-equal unit pending)))
             (member-equal unit committed))
    :rule-classes nil))

; -----------------------------------------------------------------------------
; A-HOST.  "The adapter preserves event identity/order contracts, reports
; outcomes honestly, and does not mutate logical data behind the core."
;
; Two constrained functions: what the adapter reports for an outcome the core
; produced, and what event sequence it presents.  The outcome constraint is
; deliberately partial -- refusal classification is the adapter's business --
; but success and uncertainty are not negotiable.  D13 of the review is exactly
; the failure this rules out: `BpDeletePending', a durable acceptance, exiting
; with the code for an uncertain result.
;
; Theorems that should take this as a hypothesis:
;   fn-sn-new-success-requires-actual-matching-durable-node-completion
;                                                 books/store-node.lisp
;   fn-sn-actual-durable-completion-installs-record  books/store-node.lisp
;   fn-node-trace-preserves-state                 books/node-traces.lisp
;   fn-bp-trace-preserves-node                    books/bp-workflow-invariants.lisp
; and every theorem whose statement is rooted at a host-supplied event list.

(encapsulate
  (((fn-assume-host-report *) => *)
   ((fn-assume-host-events *) => *))

  (local (defun fn-assume-host-report (outcome) outcome))
  (local (defun fn-assume-host-events (events) events))

  ; The adapter never reports a durable success the core did not produce.
  ; `:rule-classes nil': the conclusion is an equality on a variable, which
  ; ACL2 refuses as a rewrite rule.  A constraint is part of the encapsulate's
  ; constraint whatever its rule classes, so this costs the assumption nothing;
  ; a user discharges it by `:use', as PRF-012 will.
  (defthm fn-assume-host-success-is-earned
    (implies (equal (fn-assume-host-report outcome) :success)
             (equal outcome :success))
    :rule-classes nil)

  ; An uncertain core outcome stays uncertain: it is never collapsed into a
  ; refusal (which would license a retry that double-commits) or a success.
  (defthm fn-assume-host-keeps-uncertainty
    (implies (equal outcome :indeterminate)
             (equal (fn-assume-host-report outcome) :indeterminate)))

  ; Event identity and order survive the adapter.  Position-wise equality is
  ; the contract the trace theorems need: they quantify over raw event lists.
  (defthm fn-assume-host-preserves-event-order
    (equal (nth n (fn-assume-host-events events))
           (nth n events))))

; -----------------------------------------------------------------------------
; A-PEER.  "A peer whose retention undertaking is relied upon follows that
; undertaking within the declared node-failure model."
;
; The handoff argument in specs/retention.md is five steps; A-PEER covers step
; 2 and step 5 only.  The constraint is the one that keeps the assumption from
; swallowing the theorem: reliance requires a receipt.  A missing, empty or
; absent receipt is not a cooperative peer, it is no evidence at all, so the
; conclusion "the sender may reclaim" cannot be reached by assuming cooperation
; in the absence of the thing the cooperation was supposed to produce.
;
; Theorems that should take this as a hypothesis:
;   fn-bpo-receipt-success-is-actual-journal-preparation  books/bp-outbound.lisp
;   fn-bp-transport-trace-preserves-receipt       books/bp-workflow-transport-invariants.lisp
;   fn-retain-release-preserves-independent-pin   books/retention-invariants.lisp
; and PRF-012, whose statement is conditional on exactly this.

(encapsulate
  (((fn-assume-peer-retainsp * *) => *))

  (local (defun fn-assume-peer-retainsp (receipt failures)
           (declare (ignore failures))
           (consp receipt)))

  ; No receipt, no undertaking.  A-PEER is a hypothesis about a peer that
  ; issued one, never a source of the receipt itself.
  (defthm fn-assume-peer-needs-a-receipt
    (implies (not (consp receipt))
             (not (fn-assume-peer-retainsp receipt failures)))))

; -----------------------------------------------------------------------------
; A-IDENTITY.  "Origin/incarnation allocation and restore procedures avoid
; unrecognized reuse, subject to their explicit freshness assumptions."
;
; OBJ-006 (specs/objects.md:57): "bytes and causal identity do not depend on
; wall-clock ordering.  An origin's incarnation and counter cannot be reused
; for a different event ... freshness is not inferred from the current time."
; The signature carries that: `fn-assume-identity-freshp' takes the identity
; and the issued set and NO clock.  A candidate that needs the time of day to
; decide freshness cannot be functionally instantiated here at all.
;
; Theorems that should take this as a hypothesis: PRF-017 has none yet; when it
; does, they belong in the origin-sequence book, and `fn-node-new-msgid-not-bound'
; (books/node-invariants.lisp) is the acceptance-layer analogue that already
; proves the corresponding fact for Message-IDs rather than assuming it.

(encapsulate
  (((fn-assume-identity-freshp * *) => *))

  (local (defun fn-assume-identity-freshp (identity issued)
           (not (member-equal identity issued))))

  ; An identity already issued is never fresh.  A restore that reuses one is an
  ; explicit fork, which the recovery procedure must declare and which leaves
  ; both branches as evidence; it is not a fresh allocation.
  (defthm fn-assume-identity-issued-is-not-fresh
    (implies (member-equal identity issued)
             (not (fn-assume-identity-freshp identity issued)))))

; -----------------------------------------------------------------------------
; A-POLICY.  "The evaluated policy context is authorized and identified;
; accepting one signed statement does not establish arbitrary authority."
;
; The review's D9 is the reason this signature has three arguments and not one
; boolean: "The A-POLICY verdict is not durable.  Sender replay passes literal
; `t'; the FNWF record has no policy field; FNRJ stores the constant `t'.  On
; disk, 'record exists' is the authorization."  A decision bit cannot be
; re-verified later; a policy identifier, a policy term and the evidence can.
; ATLAS law 12: bind the policy term, not the decision bit.
;
; Theorems that should take this as a hypothesis, replacing their bare boolean:
;   fn-bpo-receipt-success-requires-local-policy  books/bp-outbound.lisp:282
;       (today: `(equal policy-authorizedp t)', a bit supplied by the caller)
;   fn-bp-unchecked-receipt-is-no-op              books/bp-workflow-invariants.lisp
;   fn-bprv-replayed-receipt-is-grounded          books/bp-receiver-trace-invariants.lisp
;       (today: `fn-bpr-request-acceptablep' takes AUTHORIZED, and every live
;        call site passes the literal `t')
;   fn-retain-wrong-evidence-does-not-release / the RET-004 release predicate
;       books/retention.lisp, whose evidence test is string equality today.

(encapsulate
  (((fn-assume-policy-authorizedp * * *) => *))

  (local (defun fn-assume-policy-authorizedp (policy-id terms evidence)
           (and (consp policy-id) (consp terms) (consp evidence))))

  ; No evidence authorizes nothing.  This is what makes a durable `t'
  ; insufficient: the stored bit is not the evidence it stood for.
  (defthm fn-assume-policy-needs-evidence
    (implies (not (consp evidence))
             (not (fn-assume-policy-authorizedp policy-id terms evidence))))

  ; An identifier is not a term.  Authority follows from what the policy says,
  ; not from the name under which it was filed.
  (defthm fn-assume-policy-needs-terms
    (implies (not (consp terms))
             (not (fn-assume-policy-authorizedp policy-id terms evidence)))))

; -----------------------------------------------------------------------------
; A-FAIRNESS.  "For liveness only: useful contacts, capacity, scheduling,
; retries, and permitted routes eventually occur as stated."
;
; The entire content is that "eventually" is a finite number of steps for a
; route the policy permits.  Nothing here makes a contact happen, and no safety
; property may take this as a hypothesis: FLR-004 says safety must not require
; a synchronized global clock, and the same goes for a contact schedule.
;
; Theorems that should take this as a hypothesis: PRF-018 has none yet.  When a
; scheduling model exists, its progress theorem takes a contact index from this
; function and must remain conditional on it; `fn-bp-trace-preserves-state'
; (books/bp-workflow-invariants.lisp) is the safety half and must not.

(encapsulate
  (((fn-assume-fairness-contact-index * *) => *))

  (local (defun fn-assume-fairness-contact-index (route schedule)
           (declare (ignore route schedule))
           0))

  ; Eventual contact is a natural number of steps away.  An unbounded or
  ; non-numeric index is not an eventual contact, and a progress theorem that
  ; quantified over one would be vacuous.
  (defthm fn-assume-fairness-contact-index-is-finite
    (natp (fn-assume-fairness-contact-index route schedule))))

; -----------------------------------------------------------------------------
; A-CRASH-IMAGE and A-CRYPTO-TRAILER (design §3.6), moved here from
; books/byte-store-invariants.lisp on 2026-09-20.
;
; These two are the first assumptions in the book that constrain a real model
; rather than an abstract value: their subjects are fn-bs-crash-imagep and
; fn-bs-torn-variantp.  The byte model's transitions and its crash are
; withdrawn by books/byte-store.lisp's export theory, so the witness proofs
; below re-enable exactly what they open, locally.
(local (in-theory (enable fn-bs-statep fn-bs-view fn-bs-lookup fn-bs-content
                          fn-bs-durable-content fn-bs-durable-entry
                          fn-bs-fencedp fn-bs-dir-quietp fn-bs-crash)))

; A torn variant of a written frame: some unit-aligned pieces replaced by
; their old content, zeros or garbage, or the whole truncated to a unit
; boundary.  Defined through the crash machinery on a one-inode store so
; that "torn" means exactly what fn-bs-crash means.
(defun fn-bs-torn-variantp (unit observed written)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s (fn-bs-make unit (list (cons 0 nil)) nil
                       (list (list :write 0 0 written)) 1)))
    (fn-bs-crash-imagep s (fn-bs-make unit (list (cons 0 observed)) nil nil 1))))

; A-CRASH-IMAGE.  The platform's crash, whatever it does, leaves an image the
; byte model admits.  ORACLE is the platform's freedom (power timing, drive
; cache, scheduler); the constraint is over every oracle.  This one
; constraint carries: fenced data survives (fn-bs-crash-keeps-fenced-content),
; quiet directories survive (fn-bs-crash-keeps-quiet-directory), per-entry
; atomic namespace with no dangling entries
; (fn-bs-crash-entry-is-old-or-a-pending-target), and that fsync :ok means
; drained (the definition of fn-bs-fsync-file; on darwin that is F_FULLFSYNC,
; review D12).  Qualification: functional instantiation with the development
; profile's crash function (P10), evidenced by the campaign (process death
; only; no power-loss claim).
(encapsulate
  (((fn-assume-physical-crash * *) => *))
  (local (defun fn-assume-physical-crash (s oracle)
           (declare (ignore oracle))
           (fn-bs-crash s nil)))                ; the lose-everything image
  (defthm fn-assume-physical-crash-is-admissible
    (implies (fn-bs-statep s)
             (fn-bs-crash-imagep s (fn-assume-physical-crash s oracle)))))

; A-CRYPTO-TRAILER.  The tears the platform produces are a subset of the
; model's tears, and none of them validates unless it is the exact write.
; Its qualification is statistical: the campaign's garble and truncate
; variants over SHA-256 never validate; a 2^-256 event is not modeled.
;
; The local witness is "no tears, of an empty write".  The natural witness
; "no tears" (observed = written for every written) needs
; fn-bs-view-is-an-admissible-image, which is OPEN above; the constraints,
; which are what every dependent theorem uses, do not change with the
; witness.
(encapsulate
  (((fn-assume-crash-tearp * * *) => *))
  (local (defun fn-assume-crash-tearp (unit observed written)
           (declare (ignore unit))
           (and (equal observed written) (null written))))
  (defthm fn-assume-crash-tear-is-a-model-tear
    (implies (fn-assume-crash-tearp unit observed written)
             (fn-bs-torn-variantp unit observed written))
    :hints (("Goal" :in-theory (enable fn-bs-crash-imagep-suff)
             :use ((:instance fn-bs-crash-imagep-suff
                              (s (fn-bs-make unit (list (cons 0 nil)) nil
                                             (list (list :write 0 0 written)) 1))
                              (image (fn-bs-make unit (list (cons 0 observed)) nil nil 1))
                              (choices nil))))))
  (defthm fn-assume-crash-tear-never-validates-unless-exact
    (implies (and (fn-assume-crash-tearp unit observed written)
                  (not (equal observed written)))
             (not (fn-frame-result-okp (fn-frame-open observed max-payload))))))

; -----------------------------------------------------------------------------
; Export theory (docs/proof-style.md section 2).  This book withdraws
; nothing: every event in it is a constraint on a named assumption, and a
; theorem that takes an assumption as a hypothesis needs its constraints.

; fn-bs-torn-variantp is a recognizer over the byte model, not a constraint:
; it is withdrawn, as books/byte-store-invariants.lisp withdrew it.
(in-theory (disable fn-bs-torn-variantp))

(in-theory (current-theory :here))
