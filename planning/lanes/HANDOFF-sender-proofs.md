# HANDOFF: lane `sender-proofs`

Branch `lane/sender-proofs`, worktree `/Users/ember/dev/fn/build/lanes/sender-proofs`,
branched from `0bd0b5c`. Code commit: `d7602736b18402b97823bc4681b40e2f97b7cbe1`. This file is committed
separately after it; the final section records the full `make certify` gate.

## Files changed

- `books/bp-workflow.lisp`: `fn-bp-live-statusp`, `fn-bp-status-rank`, and
  `fn-bp-transport-transition-okp` replaced (F11).
- `books/bp-workflow-invariants.lisp`: effect formulas
  (`fn-bp-result-effects-of-make-result`, `fn-bp-complete-effects-formula`,
  `fn-bp-recover-effects-formula`, `fn-bp-step-effects-formula`,
  `fn-bp-nth-0-of-cons`, `fn-bp-effect-for-pending-kind`,
  `fn-bp-effect-for-pending-attempt-unfolds`) and the D8 step keystone; one
  hint hardened against the new definitions.
- `books/bp-workflow-transport-invariants.lisp`: `fn-bph-find-of-replace`,
  rank facts, and the two F11 keystones.
- `books/bp-workflow-binding-invariants.lisp`: one hint hardened.
- `books/bp-workflow-records-invariants.lisp` (new, Makefile root added after
  `books/bp-workflow-records`): D7 and the record-level D8 keystone.
- `tests/acl2/bp-workflow-tests.lisp`, `tests/acl2/bp-workflow-binding-invariants-tests.lisp`,
  `tests/acl2/bp-workflow-records-tests.lisp`: witnesses and `must-fail` teeth
  (`std/testing/must-fail` from the system books).
- `specs/bp-workflow.md`, `specs/bp-workflow-host.md`, `specs/bp-outbound.md`:
  lifecycle order, D7 denotation, D8 statement and A-HOST remainder.
- `specs/bp-evolving-store.md` (new): design for the receiver restatement.
- `Makefile`: one root.

Not touched: `host/*.lisp`, `tools/*.py`, receiver books, `bp-adu`,
`bp-ingress`, `planning/proofs.json`, `tests/evidence/*`.

## Keystones

Each theorem is quoted verbatim from the book at the code commit. "One level
down" unfolds each hypothesis once. The host line names the call whose
subject the theorem is about.

### `fn-bp-replay-journal-is-trace-when-ok` (books/bp-workflow-records-invariants.lisp)

D7 keystone. Subject: `fn-bp-replay-journal`, called at
`host/workflow-host.lisp:9` (`fn-workflow-install-replay`, the image the host
installs on open) and `:35` (`fn-workflow-preflight-history`).
Hypothesis `(car (fn-bp-replay-journal node records))` one level down:
`records` is a cons whose first element satisfies `fn-bp-config-recordp`,
`(fn-bp-initial-state node (fn-bp-config-from-record (car records)))`
satisfies `fn-bp-statep` (so `node` is `fn-node-statep` and the config is
`fn-bp-configp`), and `(fn-bp-replay-records s0 (cdr records) nil)` returned
`t` in its first position, which by `fn-bp-replay-records` means every record
after the configuration passed `fn-bp-journal-recordp`, was not `:config`,
changed the state, and (for non-outcome records) passed
`fn-bp-record-contextp`, and every `:outcome` record matched the pending
transaction pair. The conclusion's `fn-bp-journal-denotation` is
`(fn-bp-journal-events (cdr records))`: each record's `fn-bp-record-events`
(a fabricated `:storage-complete ... :indeterminate` before every
`:recovery` outcome, then the record's own event) followed by `(:restart)`.

```lisp
(defthm fn-bp-replay-journal-is-trace-when-ok
  (implies (car (fn-bp-replay-journal node records))
           (equal (fn-bp-journal-nth 1 (fn-bp-replay-journal node records))
                  (fn-bp-trace
                   (fn-bp-initial-state
                    node (fn-bp-config-from-record (car records)))
                   (fn-bp-journal-denotation records))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-replay-records-is-trace-when-ok
                     (s (fn-bp-initial-state
                         node (fn-bp-config-from-record (car records))))
                     (records (cdr records))
                     (effects nil)))
    :in-theory (e/d (fn-bp-replay-journal fn-bp-journal-denotation)
                    (fn-bp-replay-records-is-trace-when-ok)))))
```

### `fn-bp-replay-records-is-trace-when-ok` (books/bp-workflow-records-invariants.lisp)

The induction behind the keystone, over arbitrary `s`, `records`, `effects`.

```lisp
(defthm fn-bp-replay-records-is-trace-when-ok
  (implies (car (fn-bp-replay-records s records effects))
           (equal (fn-bp-journal-nth 1 (fn-bp-replay-records s records effects))
                  (fn-bp-trace s (fn-bp-journal-events records))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records fn-bp-journal-events
                              fn-bp-record-live-event fn-bp-trace))))
```

### `fn-bp-replay-journal-effects-are-actionable-trace-effects-when-ok` (books/bp-workflow-records-invariants.lisp)

Companion: the replayed effect list is the trace's effects with the
fabricated fences' `:recover-required` demands removed
(`fn-bp-actionable-effects`), because the next denoted event is their
recorded resolution. The host discards replay effects
(`host/workflow-host.lisp:14`); this theorem says what it discards.

```lisp
(defthm fn-bp-replay-journal-effects-are-actionable-trace-effects-when-ok
  (implies (car (fn-bp-replay-journal node records))
           (equal (fn-bp-journal-nth 2 (fn-bp-replay-journal node records))
                  (fn-bp-actionable-effects
                   (fn-bp-trace-effects
                    (fn-bp-initial-state
                     node (fn-bp-config-from-record (car records)))
                    (fn-bp-journal-denotation records)))))
  :hints
  (("Goal"
    :use ((:instance
           fn-bp-replay-records-effects-are-actionable-trace-effects-when-ok
           (s (fn-bp-initial-state
               node (fn-bp-config-from-record (car records))))
           (records (cdr records))
           (effects nil)))
    :in-theory
    (e/d (fn-bp-replay-journal fn-bp-journal-denotation)
         (fn-bp-replay-records-effects-are-actionable-trace-effects-when-ok)))))
```

### `fn-bp-apply-journal-record-is-step-when-ok` (books/bp-workflow-records-invariants.lisp)

D7 live entry point. Subject: `fn-bp-apply-journal-record`, called at
`host/workflow-host.lisp:27` (`fn-workflow-preflight-record`) and `:40`
(`fn-workflow-apply-record`). Hypothesis one level down: the record passed
`fn-bp-journal-recordp`, is not `:config`, its event changed the state, and
(non-outcome) `fn-bp-record-contextp` held. `fn-bp-record-live-event` is the
record's event with no fabricated fence: a live `:recovery` outcome is
`fn-bp-storage-recover-event` alone, which `fn-bp-recover` refuses unless the
image is already fenced (after a restart it is, by the trailing `:restart`).

```lisp
(defthm fn-bp-apply-journal-record-is-step-when-ok
  (implies (car (fn-bp-apply-journal-record s r))
           (and (equal (fn-bp-journal-nth 1 (fn-bp-apply-journal-record s r))
                       (fn-bp-result-state
                        (fn-bp-step s (fn-bp-record-live-event r))))
                (equal (fn-bp-journal-nth 2 (fn-bp-apply-journal-record s r))
                       (fn-bp-result-effects
                        (fn-bp-step s (fn-bp-record-live-event r))))))
  :hints (("Goal" :in-theory
           (enable fn-bp-apply-journal-record fn-bp-record-live-event))))
```

### `fn-bp-replay-journal-success-is-binding-state` (books/bp-workflow-records-invariants.lisp)

State and binding-state preservation over arbitrary record lists. Same
hypothesis as the trace keystone. Siblings in the book:
`fn-bp-replay-records-preserves-state`, `-preserves-binding-state`,
`-preserves-node`, `fn-bp-replay-journal-success-preserves-node`,
`fn-bp-apply-journal-record-preserves-state`, `-preserves-binding-state`,
`-preserves-node`.

```lisp
(defthm fn-bp-replay-journal-success-is-binding-state
  (implies (car (fn-bp-replay-journal node records))
           (fn-bp-binding-statep
            (fn-bp-journal-nth 1 (fn-bp-replay-journal node records))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-statep-of-initial-state-implies-inputs
                     (config (fn-bp-config-from-record (car records))))
          (:instance fn-bp-initial-state-is-binding-state
                     (config (fn-bp-config-from-record (car records))))
          (:instance fn-bp-replay-records-preserves-binding-state
                     (s (fn-bp-initial-state
                         node (fn-bp-config-from-record (car records))))
                     (records (cdr records))
                     (effects nil)))
    :in-theory (e/d (fn-bp-replay-journal)
                    (fn-bp-initial-state-is-binding-state
                     fn-bp-replay-records-preserves-binding-state
                     fn-bp-statep-of-initial-state-implies-inputs)))))
```

### `fn-bp-replay-journal-rejects-any-malformed-record` (books/bp-workflow-records-invariants.lisp)

Malformed records are rejected loudly. Hypotheses one level down:
`(member-equal r (cdr records))` is list membership;
`(fn-bp-replay-rejected-recordp r)` is `(not (fn-bp-journal-recordp r))` or
`(equal (fn-bp-journal-nth 0 r) :config)`. The induction is
`fn-bp-replay-records-rejects-any-malformed-record`. The one-record
statement `fn-bp-apply-journal-record-malformed-unfolds` is the definition's
first branch and is named as such; it is not a keystone.

```lisp
(defthm fn-bp-replay-journal-rejects-any-malformed-record
  (implies (and (member-equal r (cdr records))
                (fn-bp-replay-rejected-recordp r))
           (not (car (fn-bp-replay-journal node records))))
  :hints
  (("Goal"
    :use ((:instance fn-bp-replay-records-rejects-any-malformed-record
                     (s (fn-bp-initial-state
                         node (fn-bp-config-from-record (car records))))
                     (records (cdr records))
                     (effects nil)))
    :in-theory (e/d (fn-bp-replay-journal)
                    (fn-bp-replay-records-rejects-any-malformed-record)))))
```

### `fn-bp-step-submit-requires-matching-durable-attempt-completion` (books/bp-workflow-invariants.lisp)

D8 over the dispatcher. Subject: `fn-bp-step`, reached from
`host/workflow-host.lisp:40` through `fn-bp-apply-journal-record` and read
back by `fn-workflow-take-submit` at `:60-68`. Hypotheses one level down:
`(member-equal e effects)` is list membership in
`(fn-bp-result-effects (fn-bp-step s event))`, which by
`fn-bp-step-effects-formula` is the effects of `fn-bp-complete` for a
`:storage-complete` event, of `fn-bp-recover` for `:storage-recover`, and
`nil` otherwise; `(equal (fn-bp-nth 0 e) :submit)` is the effect's tag. The
conclusion `(fn-bp-statep s)` comes from `fn-bp-pending-matchesp`, which
`fn-bp-complete` requires. The word durable is the host's; the model can only
refuse to grant earlier (A-HOST in `specs/bp-workflow-host.md`).

```lisp
(defthm fn-bp-step-submit-requires-matching-durable-attempt-completion
  (implies (and (member-equal e (fn-bp-result-effects (fn-bp-step s event)))
                (equal (fn-bp-nth 0 e) :submit))
           (let ((pending (fn-bp-state-pending s)))
             (and (fn-bp-statep s)
                  (not (fn-bp-state-fenced s))
                  (consp pending)
                  (equal (fn-bp-pending-kind pending) :attempt)
                  (equal (fn-bp-event-kind event) :storage-complete)
                  (equal (fn-bp-nth 1 event) (fn-bp-pending-txid pending))
                  (equal (fn-bp-nth 2 event) (fn-bp-pending-generation pending))
                  (equal (fn-bp-nth 3 event) :durable)
                  (equal (fn-bp-result-effects (fn-bp-step s event)) (list e))
                  (equal e
                         (list :submit
                               (fn-bp-work-id (fn-bp-pending-work pending))
                               (fn-bp-attempt-id
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending)))
                               (fn-bp-attempt-generation
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending)))
                               (fn-bp-config-local-eid (fn-bp-state-config s))
                               (fn-bp-config-peer-eid (fn-bp-state-config s))
                               (fn-bp-attempt-lifetime
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending))))))))
  :rule-classes nil
  :hints
  (("Goal" :in-theory
    (e/d (fn-bp-step-effects-formula fn-bp-complete-effects-formula
          fn-bp-recover-effects-formula fn-bp-pending-matchesp
          fn-bp-effect-for-pending-kind
          fn-bp-effect-for-pending-attempt-unfolds member-equal)
         (fn-bp-step fn-bp-complete fn-bp-recover fn-bp-effect-for-pending
          fn-bp-statep fn-bp-state-pending fn-bp-state-fenced
          fn-bp-pending-kind fn-bp-pending-txid fn-bp-pending-generation
          fn-bp-pending-work fn-bp-work-id fn-bp-work-attempt
          fn-bp-attempt-id fn-bp-attempt-generation fn-bp-attempt-lifetime
          fn-bp-state-config fn-bp-config-local-eid fn-bp-config-peer-eid
          fn-bp-event-kind fn-bp-nth fn-bp-result-effects)))))
```

### `fn-bp-apply-journal-record-submit-requires-ordinary-durable-attempt-outcome` (books/bp-workflow-records-invariants.lisp)

D8 over the live entry point. Subject: `fn-bp-apply-journal-record` at
`host/workflow-host.lisp:40`. Hypotheses as above with the effects taken from
the record application. The conclusion adds that the record is an `:outcome`
record with `:ordinary :durable` naming the pending attempt's transaction
pair, and that the application succeeded.

```lisp
(defthm fn-bp-apply-journal-record-submit-requires-ordinary-durable-attempt-outcome
  (implies (and (member-equal
                 e (fn-bp-journal-nth 2 (fn-bp-apply-journal-record s r)))
                (equal (fn-bp-nth 0 e) :submit))
           (let ((pending (fn-bp-state-pending s)))
             (and (car (fn-bp-apply-journal-record s r))
                  (fn-bp-journal-recordp r)
                  (equal (car r) :outcome)
                  (equal (fn-bp-journal-nth 3 r) :ordinary)
                  (equal (fn-bp-journal-nth 4 r) :durable)
                  (fn-bp-statep s)
                  (not (fn-bp-state-fenced s))
                  (consp pending)
                  (equal (fn-bp-pending-kind pending) :attempt)
                  (equal (fn-bp-journal-nth 1 r) (fn-bp-pending-txid pending))
                  (equal (fn-bp-journal-nth 2 r)
                         (fn-bp-pending-generation pending))
                  (equal (fn-bp-journal-nth 2 (fn-bp-apply-journal-record s r))
                         (list e))
                  (equal e
                         (list :submit
                               (fn-bp-work-id (fn-bp-pending-work pending))
                               (fn-bp-attempt-id
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending)))
                               (fn-bp-attempt-generation
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending)))
                               (fn-bp-config-local-eid (fn-bp-state-config s))
                               (fn-bp-config-peer-eid (fn-bp-state-config s))
                               (fn-bp-attempt-lifetime
                                (fn-bp-work-attempt
                                 (fn-bp-pending-work pending))))))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           fn-bp-step-submit-requires-matching-durable-attempt-completion
           (event (fn-bp-record-live-event r))))
    :in-theory
    (enable fn-bp-apply-journal-record fn-bp-record-live-event
            fn-bp-storage-complete-event fn-bp-storage-recover-event
            fn-bp-event-kind fn-bp-nth-of-cons fn-bp-nth-of-atom
            fn-bp-outcome-record-outcome-shape))))
```

### `fn-bp-observe-transport-never-moves-status-backward` (books/bp-workflow-transport-invariants.lisp)

F11 keystone, no hypotheses. Subject: `fn-bp-observe-transport`, the
`:transport` and `:no-contact` cases of `fn-bp-step`, reached from
`host/workflow-host.lisp:40` when `tools/workflow_journal.py` applies a
`:transport` record. `fn-bp-status-rank` is the lifecycle order below.

```lisp
(defthm fn-bp-observe-transport-never-moves-status-backward
  (<= (fn-bp-status-rank
       (fn-bp-attempt-status
        (fn-bp-work-attempt (fn-bp-find-work id (fn-bp-state-works s)))))
      (fn-bp-status-rank
       (fn-bp-attempt-status
        (fn-bp-work-attempt
         (fn-bp-find-work
          id (fn-bp-state-works
              (fn-bp-observe-transport s work-id attempt-id generation
                                       status)))))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance fn-bph-transition-okp-rank
                     (old (fn-bp-attempt-status
                           (fn-bp-work-attempt
                            (fn-bp-find-work work-id (fn-bp-state-works s)))))
                     (new status))
          (:instance fn-bph-find-of-replace
                     (work (fn-bp-work-with-status
                            (fn-bp-find-work work-id (fn-bp-state-works s))
                            status))
                     (works (fn-bp-state-works s)))
          (:instance fn-bph-attempt-implies-work-consp
                     (work (fn-bp-find-work work-id (fn-bp-state-works s)))))
    :in-theory (enable fn-bp-observe-transport))))
```

### `fn-bp-observe-transport-never-returns-to-intent` (books/bp-workflow-transport-invariants.lisp)

The rank-free F11 statement, from the rank keystone with
`fn-bph-rank-positive-unless-intent` and `fn-bph-rank-of-intent`.
`fn-bpo-request-adu` keys on `:intent` (`books/bp-outbound.lisp:29-35`), so
this is what keeps the one-shot ADU projection from reopening.

```lisp
(defthm fn-bp-observe-transport-never-returns-to-intent
  (implies (not (equal (fn-bp-attempt-status
                        (fn-bp-work-attempt
                         (fn-bp-find-work id (fn-bp-state-works s))))
                       :intent))
           (not (equal (fn-bp-attempt-status
                        (fn-bp-work-attempt
                         (fn-bp-find-work
                          id (fn-bp-state-works
                              (fn-bp-observe-transport
                               s work-id attempt-id generation status)))))
                       :intent)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance fn-bp-observe-transport-never-moves-status-backward))
    :in-theory (disable fn-bp-observe-transport))))
```

### `fn-bp-transport-transition-okp` (books/bp-workflow.lisp), the fixed relation

```lisp
(defun fn-bp-live-statusp (x)
  (declare (xargs :guard t))
  (member-equal x '(:intent :bpa-submit-replied :bpa-accepted :attempted
                    :forwarded :inbound-persisted :dequeued)))

(defun fn-bp-status-rank (x)
  (declare (xargs :guard t))
  (cond ((equal x :intent) 0)
        ((equal x :bpa-submit-replied) 1)
        ((equal x :bpa-accepted) 2)
        ((equal x :attempted) 3)
        ((equal x :forwarded) 4)
        ((equal x :inbound-persisted) 5)
        ((equal x :dequeued) 6)
        ((equal x :delivered) 7)
        (t 8)))

(defun fn-bp-transport-transition-okp (old new)
  (declare (xargs :guard t))
  (and (fn-bp-transport-statusp new)
       (or (equal old new)
           (and (fn-bp-live-statusp old)
                (< (fn-bp-status-rank old) (fn-bp-status-rank new))))))
```

The previous relation admitted any non-retryable, non-`:delivered` status to
move to any status, including back to `:intent`. Placing `:inbound-persisted`
and `:dequeued` between forwarding and delivery is a local choice for two
statuses the adapter never emits (`tools/workflow_journal.py:71-74` lists
them; no test or host path produces them); a BPA reporting them in another
order is refused as stale.

## Teeth

`tests/acl2/bp-workflow-tests.lisp` (includes `std/testing/must-fail`):

- F11: `*bp-accepted*` (`:bpa-accepted`) is refused back to `:intent`
  (`must-fail` on `fn-bp-transport-transition-okp :bpa-accepted :intent`);
  `*bp-forwarded*` is refused back to `:bpa-submit-replied` and
  `:bpa-accepted` (`must-fail` on `:forwarded :attempted`); forward to
  `:delivered` is accepted and a repeat is a no-op, so the relation is not
  "refuse everything"; `:delivered` to `:expired` and `:unknown` to
  `:delivered` remain refused (`must-fail` each); the rank conclusion is
  executed on a refused and on an accepted observation.
- D8: `*bp-attempt-pending*` (prepared intent, no outcome) yields no `:submit`
  under `:aborted`, `:indeterminate`, a wrong transaction pair, a transport
  event, `:restart`, and (`must-fail`) committed recovery after restart; the
  `:durable` completion yields exactly one `:submit`. Teeth per hypothesis:
  an `:enqueue-ack` effect from a pending `:enqueue` (`must-fail` that its
  pending kind is `:attempt`); the initial state emits nothing and has no
  pending intent (`must-fail`).

`tests/acl2/bp-workflow-binding-invariants-tests.lisp`:

- Item 4: `*bpb-wrong-subject*` and `*bpb-wrong-archive*` are `fn-bp-statep`,
  name an article that is present and bound, agree with the binding in the
  other field, fail `fn-bp-work-boundp`, and (`must-fail`) fail
  `fn-bp-binding-statep`; the control `*bpb-shaped-right*` is bound;
  `fn-bp-prepare-enqueue` cannot construct either because it derives both
  fields from the binding.

`tests/acl2/bp-workflow-records-tests.lisp` (now includes the new book):

- D7 witness `*bpr-all-kinds*`: every record kind (`:config :enqueue :outcome
  :attempt :transport :retry-request :receipt-intent`, asserted by
  `subsetp-equal` over the kinds) and every outcome kind (`:ordinary
  :durable`, `:ordinary :aborted`, `:recovery :committed`, `:recovery
  :absent`); replay succeeds, is `fn-bp-binding-statep`, leaves the node
  exact, and equals `fn-bp-trace` over `fn-bp-journal-denotation`; the effect
  list equals the actionable trace effects; the denotation contains the
  fabricated fences and ends in `:restart`; the unfiltered trace demands
  recovery at a fence and the replay does not.
- Teeth: a failing journal (`[config enqueue enqueue]`) is not its trace
  (`must-fail`); a refused image is not a state (`must-fail`); a malformed
  record, a second `:config`, and a bad transport status are refused wherever
  they occur; the same journal without them succeeds (`must-fail` on its
  refusal).
- Live entry point equals one step; D8 over the live entry point with the
  same non-durable cases including the refused live `:recovery` on an
  unfenced image and the `:unknown` install after restart (`must-fail`);
  teeth for the `:submit` hypothesis via `:enqueue-ack`.
- Binding hypothesis teeth: a structurally valid unbound image stays
  `fn-bp-statep` through a successful live `:attempt` record and
  (`must-fail`) is not `fn-bp-binding-statep`.

## Commands run

- `make certify` baseline at `0bd0b5c`: reached 102 of 113 roots, then
  `books/article-properties` exceeded the runner's 600 s per-book ceiling
  under ten-lane load (its log ends mid-proof with no error), cascading to
  the article-work family; `tests/acl2/bp-workflow-records-tests` failed only
  because I had already edited it to include the not-yet-certified new book.
  Evidence: `build/acl2/certify-20260919T033252Z-69430`.
- `python3 tools/certify_books.py` over the owned roots:
  `build/acl2/certify-20260919T053342Z-95003` passed `bp-workflow`,
  `bp-workflow-invariants`, `bp-workflow-transport-invariants`,
  `bp-workflow-binding-core`, `bp-workflow-binding-invariants`,
  `bp-workflow-binding-invariants-tests`, `bp-workflow-tests`,
  `bp-workflow-records` (the runner was killed with my shell before the
  ninth root); the new book was iterated with a direct `certify-book`
  (three fixes: a closed default theory, two binding recognizers added to it,
  `true-listp` of `append`, and the evaluated `'(:restart)` form of the
  restart-emits-nothing rule); `build/acl2/certify-20260919T060643Z-16632`
  passed `bp-workflow-records-tests`, `bp-outbound`, `bp-outbound-tests`.
- `make check`: `Scaffold OK: 77 Markdown files, 49 requirements, 18 proof
  targets, 18 scenario specifications.`
- `python3 -m unittest tests.test_workflow_journal tests.test_workflow_faults
  tests.test_workflow_live tests.test_workflow_boundary -v`: `Ran 27 tests`,
  `OK` (`build/pytest-workflow.log`).
- Full `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` after the changes: see
  the final section.

## Known defects and observations

- Replay drops the `:recover-required` effect of every fabricated fence.
  This is stated, not hidden (`fn-bp-actionable-effects`); the host discards
  replay effects anyway. If a future host acts on replay effects, the
  actionable filter is the contract.
- A live `:recovery` outcome record is refused on an unfenced image
  (`fn-bp-recover` requires `fenced = t`), while disk replay fabricates the
  fence. The asymmetry is by design and now proved on both sides; the spec
  says so.
- `fn-bp-pendingp` does not require a pending `:attempt`'s status to be
  `:intent`, so the D8 conclusion names the attempt id and generation but
  not the status. Every reachable pending attempt has `:intent`
  (`fn-bp-prepare-attempt` sets it); tightening `fn-bp-pendingp` would break
  `fn-bp-recovery-pending-preserves-pendingp`.
- Eight new proof-only functions in the records-invariants book are
  `:verify-guards nil`, matching the records book they describe; they are not
  executed by the host.
- The rank theorem is about `fn-bp-status-rank`, a definition introduced
  here; `fn-bp-observe-transport-never-returns-to-intent` is the rank-free
  check that the order is not rigged.

## Remaining gaps

- D9 (A-POLICY verdict not durable) is untouched; the `:receipt-intent`
  record still carries no policy term.
- A-HOST is prose in `specs/bp-workflow-host.md`, not an `encapsulate`
  (C1-15).
- The evolving-store restatement is a design (`specs/bp-evolving-store.md`);
  L19 (`fn-bprv-replay-installs-every-record`) is the one lemma with proof
  risk and does not exist yet.
- No theorem relates `fn-bp-record-contextp` to what the host writes; the
  host-event refinement remains open as before.

## Proposals for files I do not own

- `planning/proofs.json`: PRF-012 events add
  `fn-bp-replay-journal-is-trace-when-ok`,
  `fn-bp-apply-journal-record-is-step-when-ok`,
  `fn-bp-replay-journal-success-is-binding-state`,
  `fn-bp-replay-journal-rejects-any-malformed-record`,
  `fn-bp-step-submit-requires-matching-durable-attempt-completion`,
  `fn-bp-apply-journal-record-submit-requires-ordinary-durable-attempt-outcome`,
  `fn-bp-observe-transport-never-moves-status-backward`; PRF-001 events add
  `fn-bp-apply-journal-record-preserves-binding-state` and
  `fn-bp-replay-records-preserves-binding-state`; evidence lists add
  `books/bp-workflow-records-invariants.lisp`. The ledger rule says these
  come from `tools/ledger.py`, which does not exist in the tree.
- `tests/evidence/`: a record for the certification runs named above.
- `specs/bp-path.md:124-125`: "durable intent before submission" can now
  cite the two D8 theorems.
- Receiver books: execute `specs/bp-evolving-store.md` in the order its last
  section gives; `fn-bpr-store-record-acceptedp` keeps its `:ready` gate.
- `tools/certify_books.py`: the per-book ceiling should scale with load or
  the runner should record a timeout distinctly from a proof failure; the
  baseline's `article-properties` log has no error line at all.

## Full gate

(pending: appended when `make certify` finishes)
