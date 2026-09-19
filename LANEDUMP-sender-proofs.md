# LANEDUMP: sender-proofs

Branch `lane/sender-proofs`, worktree `/Users/ember/dev/fn/build/lanes/sender-proofs`,
from `0bd0b5c`. Code commit `d760273`; HANDOFF commit `484e86b`; HEAD before this
dump `484e86bcfe33c9a27f44cee84e222bc9c306bc95`. HANDOFF.md in this worktree is the fuller narrative; this file is
the state at hand-over to Codex.

## Packet as understood

1. D7: theorems about `fn-bp-apply-journal-record` and `fn-bp-replay-journal`
   (the host's calls, `host/workflow-host.lisp:9,27,35,40`): state and
   binding-state preservation over arbitrary record lists, malformed records
   rejected loudly, a journal denotation (with the fabricated `:indeterminate`
   fence and trailing `:restart`) and replay = `fn-bp-trace` over it when
   replay succeeds; witness journal with every record kind; must-fail per
   hypothesis.
2. D8: "durable intent before submission" as theorems over `fn-bp-step` and
   `fn-bp-apply-journal-record`; must-fail that a pending non-durable intent
   yields no `:submit`; A-HOST remainder in the spec.
3. F11: fix `fn-bp-transport-transition-okp` (regression to `:intent`), prove
   no transport observation moves status backward, teeth.
4. Strengthen the fabricated-work witness: wrong subject, wrong archive id,
   article present.
5. Design `specs/bp-evolving-store.md`.
Gate: `make check`; full `make certify`; filtered workflow Python tests.

## DONE

All five packet items are implemented and certified in this worktree.

- `books/bp-workflow.lisp`: `fn-bp-live-statusp`, `fn-bp-status-rank`,
  `fn-bp-transport-transition-okp` (F11).
- `books/bp-workflow-invariants.lisp`: effect formulas and the D8 step keystone
  (`:rule-classes nil`); hint of `fn-bp-observe-transport-preserves-state`
  hardened with `fn-bp-live-statusp fn-bp-status-rank` in its disable list.
- `books/bp-workflow-transport-invariants.lisp`: `fn-bph-find-of-replace`,
  `fn-bph-transition-okp-rank`, `fn-bph-rank-natp`, `fn-bph-rank-of-intent`,
  `fn-bph-rank-positive-unless-intent`, the two F11 keystones; two names added
  to its local disable list.
- `books/bp-workflow-binding-invariants.lisp`: same hint hardening.
- `books/bp-workflow-records-invariants.lisp` (new; Makefile root inserted
  after `books/bp-workflow-records`): D7, record-level D8.
- Tests: `tests/acl2/bp-workflow-tests.lisp` (F11 + D8 teeth),
  `tests/acl2/bp-workflow-binding-invariants-tests.lisp` (item 4),
  `tests/acl2/bp-workflow-records-tests.lisp` (D7 witness, replay = trace
  executed, D8 record teeth, binding teeth). All use
  `(include-book "std/testing/must-fail" :dir :system)`.
- Specs: `specs/bp-workflow.md`, `specs/bp-workflow-host.md`,
  `specs/bp-outbound.md` updated; `specs/bp-evolving-store.md` written in
  full (design with lemma statements L1-L22, survive/restate/retire lists,
  teeth plan, execution order). `make check` passes with it.
- `HANDOFF.md` written and committed (`484e86b`).

Verbatim keystone statements and the fixed relation:

`fn-bp-replay-journal-is-trace-when-ok` (books/bp-workflow-records-invariants.lisp):

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

`fn-bp-replay-records-is-trace-when-ok` (books/bp-workflow-records-invariants.lisp):

```lisp
(defthm fn-bp-replay-records-is-trace-when-ok
  (implies (car (fn-bp-replay-records s records effects))
           (equal (fn-bp-journal-nth 1 (fn-bp-replay-records s records effects))
                  (fn-bp-trace s (fn-bp-journal-events records))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records fn-bp-journal-events
                              fn-bp-record-live-event fn-bp-trace))))
```

`fn-bp-replay-journal-effects-are-actionable-trace-effects-when-ok` (books/bp-workflow-records-invariants.lisp):

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

`fn-bp-apply-journal-record-is-step-when-ok` (books/bp-workflow-records-invariants.lisp):

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

`fn-bp-replay-journal-success-is-binding-state` (books/bp-workflow-records-invariants.lisp):

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

`fn-bp-replay-records-preserves-binding-state` (books/bp-workflow-records-invariants.lisp):

```lisp
(defthm fn-bp-replay-records-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-journal-nth 1 (fn-bp-replay-records s records effects))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records))))
```

`fn-bp-apply-journal-record-preserves-binding-state` (books/bp-workflow-records-invariants.lisp):

```lisp
(defthm fn-bp-apply-journal-record-preserves-binding-state
  (implies (fn-bp-binding-statep s)
           (fn-bp-binding-statep
            (fn-bp-journal-nth 1 (fn-bp-apply-journal-record s r))))
  :hints (("Goal" :in-theory (enable fn-bp-apply-journal-record))))
```

`fn-bp-replay-journal-rejects-any-malformed-record` (books/bp-workflow-records-invariants.lisp):

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

`fn-bp-replay-records-rejects-any-malformed-record` (books/bp-workflow-records-invariants.lisp):

```lisp
(defthm fn-bp-replay-records-rejects-any-malformed-record
  (implies (and (member-equal r records)
                (fn-bp-replay-rejected-recordp r))
           (not (car (fn-bp-replay-records s records effects))))
  :hints (("Goal" :induct (fn-bp-replay-records s records effects)
           :in-theory (enable fn-bp-replay-records
                              fn-bp-replay-rejected-recordp))))
```

`fn-bp-step-submit-requires-matching-durable-attempt-completion` (books/bp-workflow-invariants.lisp):

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

`fn-bp-apply-journal-record-submit-requires-ordinary-durable-attempt-outcome` (books/bp-workflow-records-invariants.lisp):

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

`fn-bp-observe-transport-never-moves-status-backward` (books/bp-workflow-transport-invariants.lisp):

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

`fn-bp-observe-transport-never-returns-to-intent` (books/bp-workflow-transport-invariants.lisp):

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

`fn-bp-live-statusp` (books/bp-workflow.lisp):

```lisp
(defun fn-bp-live-statusp (x)
  (declare (xargs :guard t))
  (member-equal x '(:intent :bpa-submit-replied :bpa-accepted :attempted
                    :forwarded :inbound-persisted :dequeued)))
```

`fn-bp-status-rank` (books/bp-workflow.lisp):

```lisp
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
```

`fn-bp-transport-transition-okp` (books/bp-workflow.lisp):

```lisp
(defun fn-bp-transport-transition-okp (old new)
  (declare (xargs :guard t))
  (and (fn-bp-transport-statusp new)
       (or (equal old new)
           (and (fn-bp-live-statusp old)
                (< (fn-bp-status-rank old) (fn-bp-status-rank new))))))
```

## IN-PROGRESS

- Full recertification after the changes. Run `build/acl2/certify-20260919T061726Z-23936`
  (log `build/certify-gate2.log`, `FN_ACL2_TIMEOUT_SECONDS=1800`) reached
  111 of 113 roots before the harness SIGTERMed it (`make: *** [certify] Terminated: 15`).
  Every root it reached passed except: books--article-properties books--article-public-bound books--article-public-work books--article-work-primitives books--article-work-scanners books--article-work tests--acl2--article-work-tests . The two unreached roots are the
  last two of the Makefile list (`books/nntp-effects`, `tests/acl2/nntp-tests`).
  All twelve owned roots passed in that run and earlier in
  `build/acl2/certify-20260919T053342Z-95003` and
  `build/acl2/certify-20260919T060643Z-16632`.
- Running now: background task basowdtvl (harness-tracked), stdout log build/certify-gate3.log, evidence dir build/acl2/certify-20260919T061726Z-23936, roots done so far: 111, runner alive: yes. It certifies the two unreached roots and retries
  `books/article-properties`. Its six dependents
  (`article-work-primitives`, `article-work-scanners`, `article-work`,
  `article-public-work`, `article-public-bound`, `tests/acl2/article-work-tests`)
  still need one runner invocation after it if it passes.
- The `article-properties` failure is upstream and load-dependent, not from
  this lane: the book is byte-identical to the main tree and unchanged since
  `a5a30d8`; `FN-AP-PARSE-LINES-FIELD-COUNT-BOUND` passed in the review run
  (313.82 s, 190,583,014 prover steps, `/Users/ember/dev/fn/build/acl2/certify-20260919T021623Z-57755`)
  and in lanes `hygiene`, `host-repair`, `assurance-tooling` around 05:45Z, but
  failed in my two gate runs (cut at 1,544,097 and 63,105,525 steps, no
  error text, plain "proof failed" with checkpoints) and in `host-repair`'s
  06:18Z run. No `with-prover-time-limit` or step limit exists in the driver
  or the article books. Treat as environmental; rerun when the box is quiet.

## NOT-STARTED

- Nothing in the packet. `specs/bp-evolving-store.md` is complete as a
  design; its proofs (L1-L22) are the next wave's work. L19
  (`fn-bprv-replay-installs-every-record`) is the only lemma with real risk.
- `planning/proofs.json` and `tests/evidence/` were not edited (not owned);
  proposals are in HANDOFF.md.

## Design decisions (do not redo)

- F11 relation: strict rank order over live statuses; `:delivered` terminal
  for transport (leaves only via `fn-bp-request-retry`); retryable statuses
  terminal (leave only via a new attempt). `:inbound-persisted`/`:dequeued`
  placed between forwarding and delivery: never emitted by the adapter
  (`tools/workflow_journal.py:71-74`), a local choice, documented in
  `specs/bp-workflow.md`.
- D7 theorems live in a new `-invariants` book rather than in
  `bp-workflow-records.lisp`, so the host-loaded book keeps exactly its
  executable surface and `bp-outbound`'s proofs are not perturbed by new
  rewrite rules. The new book closes every workflow definition and unfolding
  rule by default (local disable list copied from
  `bp-workflow-transport-invariants.lisp` plus the records functions,
  `fn-bp-binding-statep`, `fn-bp-pending-boundp`, and the effect/state
  formula rules) and enables per proof. Without this the first attempt split
  into 23,882 subgoals.
- Two denotations: `fn-bp-record-live-event` (live apply: no fence) and
  `fn-bp-record-events` = fence events ++ live event (disk replay). Replay
  effects equal `fn-bp-actionable-effects` of the trace effects because
  replay drops each fabricated fence's `:recover-required`; stated, not
  hidden.
- `fn-bp-record-fence-events`/`fn-bp-record-events` stay opaque in the two
  replay inductions and are bridged by `fn-bp-trace-of-fence-events`,
  `fn-bp-trace-of-record-events`,
  `fn-bp-actionable-trace-effects-of-record-events`; the restart-emits-nothing
  fact is stated both on `(fn-bp-restart-event)` and on the evaluated
  constant `'(:restart)`, because ACL2 evaluates the ground call.
- D8 conclusion does not claim the pending attempt's status is `:intent`
  because `fn-bp-pendingp` does not require it; tightening it would break
  `fn-bp-recovery-pending-preserves-pendingp`.
- Teeth are `must-fail` around `assert-event` on concrete witnesses (tested:
  `(must-fail (assert-event nil))` succeeds under ACL2 8.7), never
  `(must-fail (defthm ...))`.
- The evolving-store relation grounds contexts in
  `(fn-sf-records (fn-sn-files store))` only, never in the phase or the node,
  because `fn-sn-crash` installs `fn-node-initial-state` and every phase
  between `fn-sf-start-frontier` and the fifth barrier is non-ready;
  node-committedness is derived under `fn-snt-relation` in idle phases (L19,
  L20). The live gate `fn-bpr-store-record-acceptedp` keeps `:ready`.

## Gate commands and last results

- `make check`: Scaffold OK: 77 Markdown files, 49 requirements, 18 proof
  targets, 18 scenario specifications.
- `python3 -m unittest tests.test_workflow_journal tests.test_workflow_faults
  tests.test_workflow_live tests.test_workflow_boundary -v`: Ran 27 tests, OK
  (`build/pytest-workflow.log`), run before the full certify so only one
  ACL2 ran in the lane.
- Owned roots: all twelve green (evidence dirs above).
- Full `make certify`: see IN-PROGRESS. The runner's per-book ceiling must be
  `FN_ACL2_TIMEOUT_SECONDS=1800` on this box.

## Known defects

- Upstream `books/article-properties` fails nondeterministically under
  ten-lane load (details above); its six dependents then lack certificates.
- Harness shell kills (exit 144) also terminate detached children, even in a
  new session with a scrubbed environment; only harness-tracked
  `run_in_background` runs survive a turn boundary.
- Eight new proof-only functions are `:verify-guards nil`.

## Proposals for files not owned

See HANDOFF.md "Proposals": `planning/proofs.json` PRF-001/PRF-012 events,
`tests/evidence/` record, `specs/bp-path.md:124-125` citation, receiver
books per `specs/bp-evolving-store.md`, `tools/certify_books.py` timeout
reporting.

## Dirty and untracked files at dump time

```
(clean before this dump; only LANEDUMP-sender-proofs.md is new)
```
Untracked and deliberately not committed: `build/` (logs and evidence),
`.cert`/`.port`/`.fasl` artefacts if any appear under `books/` and
`tests/acl2/` (they are ignored by the tree's `.gitignore` when they exist).
