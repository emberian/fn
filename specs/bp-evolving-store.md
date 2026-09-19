# Receiver relation over an evolving Store

Status: design for the next proof wave (packet C1-04 in
[the independent review](../planning/review-2026-09-18-independent.md), §4 row
"bp-receiver-*" and naivety 6 in §6). This document restates the receiver
invariant so that it can be true of the Store the host actually passes. It
contains theorem statements, not proofs. Nothing here changes a registry
status.

## The defect, precisely

The receiver theorems in `books/bp-receiver-*-invariants.lisp` take the Store
as a positional parameter `store` that appears identically on both sides of
every relation theorem, for example
`fn-bprv-apply-record-preserves-relation`:

```lisp
(implies (fn-bprv-relationalp store st)
         (fn-bprv-relationalp store (cadr (fn-bprr-apply-record st store r))))
```

The host does not hold the Store fixed. `host/bp-receipt-journal-host.lisp`
reads `(f-get-global 'fn-store-sn state)` afresh in `fn-bprj-install` (line
12), `fn-bprj-preflight` (18 to 19) and `fn-bprj-apply` (22 to 23), and the
ingress path (`host/bp-ingress-host.lisp`, `tools/run_bp_receive.py`) replaces
that global between receiver calls as it runs the composed store machine
`fn-sn-prepare`, `fn-sn-io`, `fn-sn-finish`, `fn-sn-crash`, `fn-sn-recover`.

`fn-bprv-relationalp` grounds every retained context through
`fn-bprv-context-backedp`, which searches `(fn-sf-records (fn-sn-files store))`
for a record satisfying `fn-bprv-record-binds`, which is
`fn-bpr-request-acceptablep`, which contains
`fn-bpr-store-record-acceptedp` (`books/bp-receipt.lisp:107-117`):

```lisp
(and (fn-sn-statep store) (fn-record-p record)
     (equal (fn-sf-phase (fn-sn-files store)) :ready)
     (member-equal record (fn-sf-records (fn-sn-files store)))
     (fn-bpi-node-record-committedp (fn-sn-node store) record))
```

Two conjuncts make the relation false of a Store in motion:

- `(equal (fn-sf-phase ...) :ready)` fails in every phase between
  `fn-sf-start-frontier` and the fifth recovery barrier, so while ingress of
  any later article is in flight the relation is false for every context
  already retained;
- `(fn-bpi-node-record-committedp (fn-sn-node store) record)` fails after
  `fn-sn-crash`, which installs `fn-node-initial-state`, until `fn-sn-recover`
  has rebuilt the node from the records.

So the seam is not a missing hypothesis discharge. The relation cannot be
stated for the evolving case; it must be restated over what does not move.

## What does not move

Two facts about the composed store machine make the restatement possible.

1. **The record history is append-only.** `fn-sf-records` changes in exactly
   two transitions of `books/store-files.lisp`: `fn-sf-record-dir-result` with
   `:ok` appends the candidate after the record-directory barrier, and
   `fn-sf-crash` appends the candidate when the crash observation says the
   linked record is present. Every other transition, including
   `fn-sf-recover` and every barrier, copies `(fn-sf-records s)`. This is
   already a theorem over file traces:
   `fn-sf-stable-records-prefix-of-run-events`
   (`books/store-files-traces.lisp:526`) with `fn-sf-prefixp` and
   `fn-sf-prefixp-transitive`, and `fn-sf-stable-records-prefix-of-crash`.
2. **In idle phases the node is the replay of the history.**
   `fn-snt-ready-or-recovered-node-is-exact-replay`
   (`books/store-node-traces.lisp`) gives, under `fn-snt-relation`, that in
   `:ready`, `:recovering` and `:fenced-recovery` the node equals
   `fn-sf-replay-node` of `(fn-sf-records (fn-sn-files s))`, and
   `fn-snt-mixed-trace-preserves-live-history-relation` keeps `fn-snt-relation`
   through every `fn-snt-step`. Across a process restart,
   `fn-sn-open-observed-success-exact-history`
   (`books/store-observed.lisp:280`) makes the observed records the history of
   the opened Store.

The restatement grounds contexts in the history alone. Node-committedness is
then a derived fact available whenever the Store is idle, and the receipt
grounding theorem says so in two steps rather than baking `:ready` into the
invariant.

## The Store as an evolving object

The receiver sees the Store through three projections:

```lisp
(defun fn-bprv-history (store) (fn-sf-records (fn-sn-files store)))
(defun fn-bprv-phase (store) (fn-sf-phase (fn-sn-files store)))
;; node view: (fn-sn-node store), used only under fn-snt-relation
```

Store extension is history extension:

```lisp
(defun fn-bprv-extendsp (old new)
  (fn-sf-prefixp (fn-bprv-history old) (fn-bprv-history new)))
```

`fn-sf-prefixp` is the existing list-prefix predicate of
`books/store-files-traces.lisp`; only `member-equal` preservation is used below,
so a proof lane may weaken `fn-bprv-extendsp` to subset if that is more
convenient, at the cost of not reusing `fn-sf-stable-records-prefix-of-run-events`
directly.

## The restated relation

Grounding of one context is `fn-bpr-request-acceptablep` with the Store
conjunct replaced by history membership and the trusted-policy argument
already at `t`:

```lisp
(defun fn-bprv-record-grounds (config context record)
  (let ((request (fn-bpr-context-request context)))
    (and (consp record) (fn-record-p record)
         (fn-bpa-requestp request)
         (equal (fn-bpa-request-destination-eid request)
                (fn-bpr-config-destination config))
         (equal (fn-bpa-request-policy-id request)
                (fn-bpr-config-policy-id config))
         (equal (fn-bpa-request-subject request)
                (fn-record-content-subject record))
         (equal (fn-bpa-request-article request) (fn-record-payload record))
         (equal context (fn-bpr-context-from-request record request)))))

(defun fn-bprv-find-grounding-record (config context history)
  (if (consp history)
      (if (fn-bprv-record-grounds config context (car history))
          (car history)
        (fn-bprv-find-grounding-record config context (cdr history)))
    nil))

(defun fn-bprv-context-groundedp (config context history)
  (consp (fn-bprv-find-grounding-record config context history)))

(defun fn-bprv-contexts-groundedp (config contexts history)
  (if (consp contexts)
      (and (fn-bprv-context-groundedp config (car contexts) history)
           (fn-bprv-contexts-groundedp config (cdr contexts) history))
    t))
```

The relation `R(history, receiver-state)`:

```lisp
(defun fn-bprv-history-relationalp (history st)
  (and (fn-bprv-contexts-groundedp (fn-bpr-state-config st)
                                   (fn-bpr-state-contexts st) history)
       (fn-bprv-entries-linkedp (fn-bpr-state-config st)
                                (fn-bpr-state-contexts st)
                                (fn-bpr-state-receipts st))
       (fn-bprv-pending-linkedp (fn-bpr-state-config st)
                                (fn-bpr-state-contexts st)
                                (fn-bpr-state-receipts st)
                                (fn-bpr-state-pending st))))

(defun fn-bprv-evolving-invariantp (store st journal)
  (and (fn-bpr-statep st)
       (fn-bprv-history-relationalp (fn-bprv-history store) st)
       (fn-bprv-entries-decidedp (fn-bpr-state-receipts st) journal)))
```

`fn-bprv-entries-linkedp`, `fn-bprv-pending-linkedp` and
`fn-bprv-entries-decidedp` are the existing definitions, unchanged. The
relation mentions neither `fn-sf-phase` nor `fn-sn-node`; that is what makes it
tolerant of non-ready phases and of the empty post-crash node for records
already committed. The live gate `fn-bpr-request-acceptablep` is not weakened:
accepting a new context still requires a `:ready` Store whose node commits the
record. The gate is the receiver's own step; the invariant is what survives
between steps.

## Lemmas

Each lemma is stated as it should be admitted. `h`, `h1`, `h2` range over
record lists; `store`, `st`, `journal` as in the existing books.

### Store-side monotonicity

L1. Every composed transition extends the history.

```lisp
(defthm fn-bprv-snt-step-extends-history
  (fn-sf-prefixp (fn-bprv-history s) (fn-bprv-history (fn-snt-step s event))))
```

No `fn-sn-statep` hypothesis: a refused transition returns `s`. Proof by
cases on `(car event)` over `fn-sn-prepare`, `fn-sn-io`, `fn-sn-finish`,
`fn-sn-crash`, `fn-sn-recover`, each reducing to a `fn-sf-*` transition that
copies or appends. The same statement for `fn-snrt-step` adds
`fn-sn-refuse-reservation` and `fn-sn-known-abort`, both copies.

L2. Runs extend the history (from L1 and `fn-sf-prefixp-transitive`).

```lisp
(defthm fn-bprv-snt-run-extends-history
  (fn-sf-prefixp (fn-bprv-history s) (fn-bprv-history (fn-snt-run s events))))
```

L3. Prefix preserves membership.

```lisp
(defthm fn-bprv-prefix-preserves-member
  (implies (and (fn-sf-prefixp h1 h2) (member-equal x h1)) (member-equal x h2)))
```

### Relation monotonicity

L4. Grounding is monotone.

```lisp
(defthm fn-bprv-grounded-monotone
  (implies (and (fn-bprv-context-groundedp config context h1)
                (fn-sf-prefixp h1 h2))
           (fn-bprv-context-groundedp config context h2)))
```

Proof: the found record is a member of `h1` (analogue of
`fn-bprv-found-record-is-member`), hence of `h2` by L3, and
`fn-bprv-find-grounding-record` finds some grounding record whenever one is a
member (analogue of `fn-bprv-find-record-from-member`).

L5. List version, by induction on `contexts`.

```lisp
(defthm fn-bprv-contexts-grounded-monotone
  (implies (and (fn-bprv-contexts-groundedp config contexts h1)
                (fn-sf-prefixp h1 h2))
           (fn-bprv-contexts-groundedp config contexts h2)))
```

L6. The relation is monotone under extension.

```lisp
(defthm fn-bprv-history-relational-monotone
  (implies (and (fn-bprv-history-relationalp h1 st) (fn-sf-prefixp h1 h2))
           (fn-bprv-history-relationalp h2 st)))
```

L7. A Store step preserves the invariant with the receiver state unchanged.

```lisp
(defthm fn-bprv-store-step-preserves-evolving-invariant
  (implies (fn-bprv-evolving-invariantp store st journal)
           (fn-bprv-evolving-invariantp (fn-snt-step store event) st journal)))
```

From L1 and L6. This is the theorem the current books cannot state.

### Receiver-side preservation

L8. The live gate implies grounding in the history it inspected.

```lisp
(defthm fn-bprv-acceptable-implies-grounded
  (implies (fn-bpr-request-acceptablep store config record request authorized)
           (fn-bprv-context-groundedp
            config (fn-bpr-context-from-request record request)
            (fn-bprv-history store))))
```

Proof: `fn-bpr-store-record-acceptedp` contains the membership; the other
conjuncts of `fn-bprv-record-grounds` are conjuncts of
`fn-bpr-request-acceptablep`; then `fn-bprv-find-grounding-record` finds it.
Replaces `fn-bprv-derived-context-backed`.

L9. Accept preserves the relation against the Store it consulted.

```lisp
(defthm fn-bprv-accept-preserves-history-relation
  (implies (fn-bprv-history-relationalp (fn-bprv-history store) st)
           (fn-bprv-history-relationalp
            (fn-bprv-history store)
            (cadr (fn-bpr-accept-request st store record request authorized)))))
```

The same `store` on both sides is the receiver step's atomicity: ingress does
not run inside `fn-bprj-apply`. Proof as `fn-bprv-accept-preserves-relation`
with L8 in place of `fn-bprv-derived-context-backed` and the existing
`fn-bprv-entries-linked-fresh-context`.

L10, L11. Prepare and commit are Store-independent; statements and proofs of
`fn-bprv-prepare-preserves-relation` and `fn-bprv-commit-preserves-relation`
with `fn-bprv-relationalp store` replaced by
`fn-bprv-history-relationalp h` for an arbitrary `h`.

L12. The actual journal transition preserves the invariant.

```lisp
(defthm fn-bprv-apply-record-preserves-evolving-invariant
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (member-equal r journal))
           (fn-bprv-evolving-invariantp
            store (cadr (fn-bprr-apply-record st store r)) journal)))
```

From L9 to L11, `fn-bprr-apply-record-preserves-statep` (unchanged) and
`fn-bprv-apply-record-preserves-decisions` (unchanged).

### Interleaving

The composed system is a pair `(store st)`; an event is either a Store event
or a receiver record:

```lisp
(defun fn-bprv-system-step (store st event)
  (case (car event)
    (:store (list (fn-snt-step store (cadr event)) st))
    (:receiver (list store (cadr (fn-bprr-apply-record st store (cadr event)))))
    (otherwise (list store st))))

(defun fn-bprv-system-run (store st events)
  (if (consp events)
      (let ((next (fn-bprv-system-step store st (car events))))
        (fn-bprv-system-run (car next) (cadr next) (cdr events)))
    (list store st)))

(defun fn-bprv-system-events-journaledp (events journal)
  (if (consp events)
      (and (or (not (equal (car (car events)) :receiver))
               (member-equal (cadr (car events)) journal))
           (fn-bprv-system-events-journaledp (cdr events) journal))
    t))
```

L13. One system step preserves the invariant.

```lisp
(defthm fn-bprv-system-step-preserves-evolving-invariant
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (or (not (equal (car event) :receiver))
                    (member-equal (cadr event) journal)))
           (let ((next (fn-bprv-system-step store st event)))
             (fn-bprv-evolving-invariantp (car next) (cadr next) journal))))
```

L14. Any interleaving preserves it.

```lisp
(defthm fn-bprv-system-run-preserves-evolving-invariant
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (fn-bprv-system-events-journaledp events journal))
           (let ((final (fn-bprv-system-run store st events)))
             (fn-bprv-evolving-invariantp (car final) (cadr final) journal))))
```

L15. The initial receiver state satisfies it against every Store.

```lisp
(defthm fn-bprv-initial-evolving-invariant
  (implies (fn-bpr-configp config)
           (fn-bprv-evolving-invariantp store (fn-bpr-initial-state config) journal)))
```

L16. A successful replay at open satisfies it against every later Store.

```lisp
(defthm fn-bprv-successful-replay-has-evolving-invariant
  (implies (and (car (fn-bprr-replay store records))
                (fn-sf-prefixp (fn-bprv-history store) (fn-bprv-history later)))
           (fn-bprv-evolving-invariantp
            later (cadr (fn-bprr-replay store records)) records)))
```

With `later := store` this is the restatement of
`fn-bprv-successful-replay-has-invariant`; with `later := (fn-snt-run store
events)` and L2 it is the open-then-ingest case the host runs.

### Grounded receipt

L17. A grounded context has an actual history record, in every phase.

```lisp
(defthm fn-bprv-grounded-context-has-history-record
  (implies (fn-bprv-context-groundedp config context h)
           (let ((record (fn-bprv-find-grounding-record config context h)))
             (and (fn-record-p record)
                  (member-equal record h)
                  (equal context (fn-bpr-context-from-request
                                  record (fn-bpr-context-request context)))
                  (equal (fn-bpa-request-article (fn-bpr-context-request context))
                         (fn-record-payload record))
                  (equal (fn-bpa-request-subject (fn-bpr-context-request context))
                         (fn-record-content-subject record))))))
```

L18. An emitted receipt is history-grounded and journal-decided, in every
phase. This is `fn-bprv-replayed-receipt-is-grounded` without the `:ready`
and node conjuncts, and stated for any state satisfying the invariant rather
than only for a fresh replay.

```lisp
(defthm fn-bprv-evolving-output-is-history-grounded
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (fn-bpr-receipt-adu st request))
           (let* ((context (fn-bpr-find-context (fn-bpa-request-work-id request)
                                                (fn-bpr-state-contexts st)))
                  (entry (fn-bpr-find-receipt (fn-bpr-context-work-id context)
                                              (fn-bpr-state-receipts st)))
                  (record (fn-bprv-find-grounding-record
                           (fn-bpr-state-config st) context (fn-bprv-history store))))
             (and (consp context)
                  (equal request (fn-bpr-context-request context))
                  (fn-record-p record)
                  (member-equal record (fn-bprv-history store))
                  (equal context (fn-bpr-context-from-request record request))
                  (equal (fn-bpa-request-article request) (fn-record-payload record))
                  (equal (fn-bpa-request-subject request)
                         (fn-record-content-subject record))
                  (member-equal entry (fn-bpr-state-receipts st))
                  (fn-bprv-entry-decidedp entry journal)
                  (equal (fn-bpr-receipt-entry-receipt entry)
                         (fn-bpr-receipt-for context (fn-bpr-state-config st)
                                             (fn-bpa-receipt-id
                                              (fn-bpr-receipt-entry-receipt entry))))
                  (equal (fn-bpr-receipt-adu st request)
                         (fn-bpa-encode (fn-bpr-receipt-entry-receipt entry)))))))
```

L19. Every history record is node-committed whenever the Store is idle. This
is the lemma that does not exist today and is the one piece of real new proof
work; the review (§4, `node-traces.lisp:329`) notes that article-record
persistence is currently one-step only.

```lisp
(defthm fn-bprv-history-record-is-node-committed-when-idle
  (implies (and (fn-snt-relation store)
                (member-equal (fn-bprv-phase store) '(:ready :recovering :fenced-recovery))
                (member-equal record (fn-bprv-history store)))
           (fn-bpi-node-record-committedp (fn-sn-node store) record)))
```

Proof plan: `fn-snt-ready-or-recovered-node-is-exact-replay` reduces the node
to `fn-sf-replay-node` of the history; then

```lisp
(defthm fn-bprv-replay-installs-every-record
  (implies (and (fn-replay-okp (fn-replay groups capacity records))
                (member-equal record records))
           (fn-bpi-node-record-committedp
            (fn-replay-result-node (fn-replay groups capacity records)) record)))
```

by induction over `fn-replay-loop`: the step that applies `record`
(`fn-replay-apply-record`, which calls the actual `fn-node-prepare` and
`fn-node-complete`) installs its article and binding with the record's
payload, groups, subject and obligation id (one-step, from
`fn-complete-preserves-existing-message-id-binding` and the install lemmas of
`books/acceptance-invariants.lisp`), and every later `fn-replay-apply-record`
preserves an existing article and binding (multi-step; bindings from
`fn-node-trace-preserves-old-bindings`, articles need the same statement for
`fn-find-article`, which is the missing lemma). `fn-replay-advance-txid`
changes only the transaction counter, so the final advance in
`fn-sf-replay-node` preserves committedness.

L20. The original conclusion, under the relation the Store actually
maintains instead of a `:ready` hypothesis on a positional argument.

```lisp
(defthm fn-bprv-evolving-output-is-node-grounded-when-idle
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (fn-snt-relation store)
                (member-equal (fn-bprv-phase store) '(:ready :recovering :fenced-recovery))
                (fn-bpr-receipt-adu st request))
           (fn-bpi-node-record-committedp
            (fn-sn-node store)
            (fn-bprv-find-grounding-record
             (fn-bpr-state-config st)
             (fn-bpr-find-context (fn-bpa-request-work-id request)
                                  (fn-bpr-state-contexts st))
             (fn-bprv-history store)))))
```

L21. A grounding record survives every later Store run, so the receipt it
grounds is node-committed in every later idle Store.

```lisp
(defthm fn-bprv-grounding-record-survives-store-run
  (implies (member-equal record (fn-bprv-history store))
           (member-equal record (fn-bprv-history (fn-snt-run store events)))))
```

From L2 and L3.

### Process restart

L22. Across a restart the host reopens through `fn-sn-open-observed`, whose
history is exactly the records it was given
(`fn-sn-open-observed-success-exact-history`). The invariant survives the
restart when the observed records extend the history at the last receiver
step:

```lisp
(defthm fn-bprv-evolving-invariant-survives-open-observed
  (implies (and (fn-bprv-evolving-invariantp store st journal)
                (fn-sn-open-okp (fn-sn-open-observed groups capacity frontier records))
                (fn-sf-prefixp (fn-bprv-history store) records))
           (fn-bprv-evolving-invariantp
            (fn-sn-open-state (fn-sn-open-observed groups capacity frontier records))
            st journal)))
```

The prefix hypothesis is the boundary with the crash model: in the model it
is `fn-sf-stable-records-prefix-of-crash`; in reality it is A-DURABILITY plus
the two syscall-returned-unobserved crash points the review lists as D4. This
design does not close D4; it makes the dependency a single named hypothesis.

## Existing theorems: survive, restate, retire

Survive unchanged (no Store in the hypothesis, or Store only as a free
parameter):

- `books/bp-receiver-state-invariants.lisp`: all of it, including
  `fn-bpr-accept-request-preserves-statep`,
  `fn-bpr-prepare-receipt-preserves-statep`,
  `fn-bpr-commit-receipt-preserves-statep`,
  `fn-bprr-apply-record-preserves-statep`,
  `fn-bprr-replay-rest-preserves-statep`, `fn-bprr-successful-replay-has-statep`.
- `books/bp-receiver-context-invariants.lisp`: `fn-bprv-entry-linkedp`,
  `fn-bprv-entries-linkedp`, `fn-bprv-pending-linkedp` and their lemmas
  (`fn-bprv-find-context-cons`, `fn-bprv-fresh-context-preserves-lookup`,
  `fn-bprv-entry-linked-fresh-context`, `fn-bprv-entries-linked-fresh-context`,
  `fn-bprv-new-entry-linked`, `fn-bprv-new-entry-pending-linked`, the
  constructor and selector lemmas).
- `books/bp-receiver-journal-invariants.lisp`: `fn-bprv-decision-for-entryp`,
  `fn-bprv-entry-decidedp`, `fn-bprv-entries-decidedp`,
  `fn-bprv-journal-subsetp`, `fn-bprv-entry-decided-from-member`,
  `fn-bprv-decision-addition-covered`, `fn-bprv-apply-record-preserves-decisions`,
  `fn-bprv-replay-rest-preserves-decisions`, `fn-bprv-accept-receipts-unchanged`,
  `fn-bprv-prepare-receipts-unchanged`.
- `books/bp-receiver-invariants.lisp`: `fn-bprv-replay-receipts-have-committed-decisions`,
  `fn-bprv-no-committed-decisionsp`, `fn-bprv-no-commit-no-decided-entry`,
  `fn-bprv-no-commit-no-committed-receipts`, `fn-bprv-no-committed-receipts-no-adu`,
  `fn-bprv-replay-no-receipt-before-committed-decision`, the journal-subset lemmas.
- `books/bp-receiver-retention-invariants.lisp`:
  `fn-bprv-accept-preserves-existing-context`, `fn-bprv-prepare-contexts-unchanged`,
  `fn-bprv-commit-contexts-unchanged`, `fn-bprv-apply-record-preserves-existing-context`,
  `fn-bprv-replay-rest-preserves-existing-context`, `fn-bprv-found-receipt-linked`,
  `fn-bprv-found-receipt-work-id`, `fn-bprv-found-receipt-decided`,
  `fn-bprv-found-receipt-member`.
- `books/bp-receiver-trace-invariants.lisp`: `fn-bprv-output-implies-statep`.

Restate by substituting `(fn-bprv-history store)` for `store` in the
hypothesis; proofs unchanged because only the linked and pending conjuncts are
used:

- `fn-bprv-commit-preserves-existing-receipt`,
  `fn-bprv-apply-record-preserves-existing-receipt`,
  `fn-bprv-replay-rest-preserves-existing-receipt`,
  `fn-bprv-output-has-linked-committed-entry` (its `fn-bprv-context-backedp`
  conjunct becomes `fn-bprv-context-groundedp`),
  `fn-bprv-replay-rest-preserves-receipt-adu`,
  `fn-bprv-prepare-preserves-relation`, `fn-bprv-commit-preserves-relation`,
  `fn-bprv-initial-relational`, `fn-bprv-nil-relational`,
  `fn-bprv-replay-has-context-and-store-relation`,
  `fn-bprv-replay-rest-preserves-relation`.

Restate with new content (L8, L9, L12 to L16, L18, L20):

- `fn-bprv-derived-context-backed`, `fn-bprv-accept-preserves-relation`,
  `fn-bprv-apply-record-preserves-relation`, `fn-bprv-invariantp`,
  `fn-bprv-initial-invariant`, `fn-bprv-actual-record-preserves-invariant`,
  `fn-bprv-actual-finite-replay-preserves-invariant`,
  `fn-bprv-successful-replay-has-invariant`,
  `fn-bprv-backed-context-has-actual-ready-record` (split into L17 and L20),
  `fn-bprv-replayed-receipt-is-grounded` (L18 plus L20).

Retire (they bake `:ready` into the relation through
`fn-bpr-request-acceptablep`): `fn-bprv-record-binds`, `fn-bprv-find-record`,
`fn-bprv-context-backedp`, `fn-bprv-contexts-backedp`,
`fn-bprv-record-binds-consp`, `fn-bprv-find-record-from-member`,
`fn-bprv-acceptable-record-is-member`, `fn-bprv-found-record-binds`,
`fn-bprv-found-record-is-member`, `fn-bprv-contexts-backed-cons`,
`fn-bprv-found-context-backed`, `fn-bprv-context-backed-implies-consp`,
`fn-bprv-nonnil-found-context-backed`, `fn-bprv-nonnil-found-context-consp`.
Each has a direct analogue over `fn-bprv-find-grounding-record`.

Executable definitions in `books/bp-receipt.lisp` and
`books/bp-receipt-records.lisp` do not change. `fn-bpr-store-record-acceptedp`
keeps its `:ready` conjunct as the live gate.

## Teeth for the next wave

The test book must contain, over one real Store built by
`fn-sn-initial`, `fn-sn-prepare`, `fn-sn-io` and `fn-sn-finish`:

- a receiver state with one context grounded in the first record, then the
  Store stepped through the ingress of a second record; at every intermediate
  phase, `fn-bprv-evolving-invariantp` holds and the retired
  `fn-bprv-invariantp` fails (the separation witness that shows the
  restatement is necessary, not a rephrasing);
- the same after `fn-sn-crash` with the second record observed present, then
  `fn-sn-recover` and five barriers; the first context stays grounded
  throughout, and after recovery both records are node-committed;
- a receiver step interleaved between two Store steps;
- must-fail per hypothesis: a context whose record is in no history is not
  grounded (L17); a history that drops a record is not a prefix, and
  groundedness does not carry to it (L4); a receiver record outside the
  journal breaks `fn-bprv-entries-decidedp` (L13); a Store in `:replaying`
  with the post-crash empty node makes the conclusion of L20 false while L18
  still holds (the phase-tolerance the design is for).

## Host obligations and scope

- The host calls `fn-bprj-apply` with the current Store and does not run
  ingress inside it. This is the atomicity L9 assumes (A-HOST).
- `fn-bprj-install` may run in any phase: the relation it establishes is
  history-based. The live `:request-context` records it replays still pass
  the `:ready` gate, so the host must open the receiver journal after the
  Store's recovery barriers, as it does today; the design does not relax that.
- Nothing here proves the two D4 crash points, `F_FULLFSYNC`, or that the
  observed records at open extend the pre-crash history; L22 names that as its
  hypothesis and C1-14 owns discharging it.
- Nothing here changes the sender books, the ADU codec, or the receipt
  encoder.

## Execution order for the proof lane

1. New book `books/bp-receiver-history-invariants.lisp` including
   `bp-receipt-records` and `store-node-traces`: definitions, L3 to L6, L8 to
   L12, L15, L17, L18. No dependency on new Store lemmas.
2. New book `books/bp-receiver-store-evolution-invariants.lisp` including
   the above and `store-node-resolution-traces`: L1, L2, L7, L13, L14, L16, L21.
3. L19 with `fn-bprv-replay-installs-every-record` in `books/replay-invariants.lisp`
   or a new `replay-content-invariants` book; then L20. This is the only step
   with proof risk and it is independent of steps 1 and 2.
4. L22 last, after C1-14 lands or with its prefix hypothesis as stated.
5. Test book `tests/acl2/bp-receiver-evolving-tests.lisp` as above; Makefile
   roots; `specs/bp-receiver-proofs.md` rewritten to cite the new keystones and
   drop the words "fixed Store"; `planning/proofs.json` PRF-001, PRF-007 and
   PRF-012 events updated by the ledger.

## Proof status (wave 2, lane w2/evolving-store)

The lemmas above are admitted in three books; the deviations from the plan are
listed so the design and the books say the same thing.

| Book | Lemmas |
| --- | --- |
| `books/bp-receiver-evolving-history-invariants.lisp` | definitions; L3 to L6 (`fn-bprv-prefix-preserves-member`, `fn-bprv-grounded-monotone`, `fn-bprv-contexts-grounded-monotone`, `fn-bprv-history-relational-monotone`); L8 to L12 (`fn-bprv-acceptable-implies-grounded`, `fn-bprv-accept-preserves-history-relation`, `fn-bprv-prepare-preserves-history-relation`, `fn-bprv-commit-preserves-history-relation`, `fn-bprv-apply-record-preserves-evolving-invariant`); L15 to L18 (`fn-bprv-initial-evolving-invariant`, `fn-bprv-successful-replay-has-evolving-invariant`, `fn-bprv-grounded-context-has-history-record`, `fn-bprv-evolving-output-is-history-grounded`); the retention restatements `fn-bprv-evolving-*-preserves-existing-receipt` and `fn-bprv-evolving-replay-rest-preserves-receipt-adu` |
| `books/bp-receiver-evolving-node-invariants.lisp` | L19 (`fn-bprv-history-record-is-node-committed-when-idle`) with its one-step install lemma `fn-bprv-apply-record-installs-record`, the multi-step `fn-bprv-apply-record-keeps-committed`, the loop lemmas and `fn-bprv-replay-node-commits-history-record` (the plan's `fn-bprv-replay-installs-every-record`); L20 (`fn-bprv-evolving-output-is-node-grounded-when-idle`); `fn-bprv-acceptable-at-ready-extension` |
| `books/bp-receiver-evolving-store-invariants.lisp` | L1, L2, L7, L21 (`fn-bprv-snrt-step-extends-history`, `fn-bprv-snrt-run-extends-history`, `fn-bprv-store-step-preserves-evolving-invariant`, `fn-bprv-grounding-record-survives-store-run`); L13, L14 (`fn-bprv-system-step-preserves-invariant`, `fn-bprv-system-run-preserves-invariant`); L22 (`fn-bprv-evolving-invariant-survives-observed-reopen`); the live trace model `fn-bpr-live-step`, `fn-bpr-live-run`, `fn-bpr-live-install` with `fn-bprv-apply-record-agrees-at-ready-extension`, `fn-bpr-live-state-is-replay-of-journal` and `fn-bpr-live-receipt-regenerated-after-restart` |

Deviations:

- The Store step is `fn-snrt-step` (store-node-resolution-traces), not
  `fn-snt-step`: it covers `fn-sn-refuse-reservation` and `fn-sn-known-abort`
  as well, which the host also runs between receiver calls.
- L1 and L7 carry `fn-snt-relation` on the Store rather than no hypothesis.
  The kernel's own prefix theorems (`fn-snrt-step-records-prefix`) need it,
  and a refused transition on an untyped Store whose record list is improper
  is not its own prefix. Every process holds the relation from its reopen
  entry, so nothing the host does is excluded. The system invariant
  `fn-bprv-system-invariantp` carries it alongside the receiver relation.
- L22 takes `fn-sf-crash-imagep` (A-DURABILITY as a hypothesis, as in D5)
  rather than a bare prefix hypothesis, and concludes both that the reopen
  succeeds and that the invariant holds against the reopened Store.
- L19 lives in the receiver's own node book rather than in
  `replay-invariants`; it carries the idle-node predicate
  `fn-bprv-node-idlep` through `fn-replay-loop` because
  `fn-replay-apply-record` on a node with a stage could complete a stale
  proposal.
- The live trace model adds what the plan did not state: the journal in the
  live state holds exactly the records `fn-bprj-apply` accepted (the host
  preflights, writes, then applies against the same Store and state:
  `tools/receipt_journal.py` lines 56 to 79), and replay against a later
  ready related Store agrees with the live step
  (`fn-bprv-apply-record-agrees-at-ready-extension`), which is what turns
  "byte-identical receipt after restart" from a process-death test into
  `fn-bpr-live-receipt-regenerated-after-restart`.
