# Lane handoff: `assurance-tooling`

Branch `lane/assurance-tooling`, branched from `0bd0b5c`.
Worktree `/Users/ember/dev/fn/build/lanes/assurance-tooling`.

`git rev-parse HEAD`: **27580aadcc656d30ec2783f687f1c5130b965a5a**
(unsigned; 1Password refused the signing key while the lane ran unattended).

The lane adopts the two assurance-discipline gaps at the end of §6 of
[the independent review](planning/review-2026-09-18-independent.md): there was
no `encapsulate` in the tree, so every named assumption was prose; and there
was no teeth discipline, so the registry's `events` lists were hand-maintained
and pointed at corollaries. Packets C1-15 and C1-16.

## Files changed

New:

| Path | What it is |
| --- | --- |
| `books/assumptions.lisp` | Seven `A-*` assumptions as `encapsulate`s with local witnesses |
| `tests/acl2/assumptions-tests.lisp` | A non-witness per constraint, each refuted at a ground point |
| `tools/ledger.py` | s-expression reader, ledger generator, suspect detector, registry check |
| `tests/test_ledger.py` | 26 unit checks of the reader, the detector and the registry validation |
| `planning/proof-events.json` | The curated map from proof target to supporting events |
| `planning/ledger.json`, `planning/ledger.md` | Generated; never edited by hand |
| `tests/acl2/<cluster>-teeth-tests.lisp` × 13 | acceptance, node, retention, store-files, store-node, records, cbor, bp-workflow, bp-receiver, exchange, nntp, article, wildmat |

Modified: `tools/check_scaffold.py` (calls the ledger check), `docs/proofs.md`
(new "The generated ledger" section; count-bearing prose replaced by a pointer;
"Registry states" says the `events` arrays are generated), `planning/proofs.json`
(`events` arrays only — ids, titles, statuses and evidence lists untouched),
`Makefile` (15 new certification roots).

## The assumption table

`books/assumptions.lisp`. A-CRYPTO is deliberately absent: `books/crypto-seam.lisp`
(the `substrate` lane) owns `fn-digest` and `fn-sig-verify`, and a second
constrained crypto function would be exactly the twin §4 says to delete.

| Assumption | Constrained function | Constraint | Local witness | Theorems that should take it |
| --- | --- | --- | --- | --- |
| A-DURABILITY | `(fn-assume-durability-image barriered unbarriered)` | A barriered record survives the crash image; the image invents nothing | `barriered` | `fn-sf-stable-records-prefix-of-crash`, `fn-sf-prior-success-has-record-after-one-crash`, `fn-sf-crash-preserves-state`, `fn-sf-prior-emitted-success-retained-by-run-trace`, `fn-snrt-acknowledged-history-retained-through-mixed-trace` |
| A-WRITE-ISOLATION | `(fn-assume-write-isolation-observe committed pending)` | A committed unit survives an unrelated incomplete write; nothing foreign appears | `committed` | `fn-sf-stable-records-prefix-of-crash`, `fn-sf-surviving-candidate-is-exact-and-dominated`, `fn-sn-open-observed-success-exact-history` |
| A-HOST | `(fn-assume-host-report outcome)`, `(fn-assume-host-events events)` | Success is earned; uncertainty is never collapsed; event identity and order survive position-wise | identity on both | `fn-sn-new-success-requires-actual-matching-durable-node-completion`, `fn-sn-actual-durable-completion-installs-record`, `fn-node-trace-preserves-state`, `fn-bp-trace-preserves-node` |
| A-PEER | `(fn-assume-peer-retainsp receipt failures)` | No receipt, no undertaking | `(consp receipt)` | `fn-bpo-receipt-success-is-actual-journal-preparation`, `fn-bp-transport-trace-preserves-receipt`, `fn-retain-release-preserves-independent-pin`; PRF-012 |
| A-IDENTITY | `(fn-assume-identity-freshp identity issued)` | An identity already issued is never fresh; the signature carries **no clock**, which is OBJ-006 expressed in the arity | `(not (member-equal identity issued))` | PRF-017 has none yet; `fn-node-new-msgid-not-bound` is the acceptance-layer analogue that proves rather than assumes |
| A-POLICY | `(fn-assume-policy-authorizedp policy-id terms evidence)` | No evidence authorizes nothing; an identifier is not a term | `(and (consp policy-id) (consp terms) (consp evidence))` | `fn-bpo-receipt-success-requires-local-policy` (today a bare bit), `fn-bp-unchecked-receipt-is-no-op`, `fn-bprv-replayed-receipt-is-grounded` (today `authorized` is the literal `t` at every call site), the RET-004 release predicate |
| A-FAIRNESS | `(fn-assume-fairness-contact-index route schedule)` | The contact index is a natural number: "eventually" is finite | `0` | PRF-018 has none yet; the safety half (`fn-bp-trace-preserves-state`) must never take it |

The encapsulates **state** the assumptions; no theorem in the tree takes one as
a hypothesis yet. That wiring is C1-14 and C1-15 work. `docs/proofs.md`
§"Qualifying a platform against A-DURABILITY" describes the functional
instantiation that a platform qualification would use.

## The suspect list, with a verdict on each

24 theorems, all proved, none citable as registry evidence. Detector shapes and
their limits are documented in `docs/proofs.md#the-generated-ledger`; the table
is regenerated in `planning/ledger.md`.

| Theorem | Where | Shape | Verdict |
| --- | --- | --- | --- |
| `fn-af-message-id-equalp-is-exact` | `article-fields.lisp:311` | definition restated under its own hypotheses | Correct flag. §4 names this row: it is `(and idp idp equal)` with the two `idp`s assumed. Rename `-by-definition`; OBJ-002 needs a theorem about the *host's* comparison path, not this one. |
| `fn-bpr-context-from-request-is-constructor` | `bp-receiver-state-invariants.lisp:86` | definition restated | Correct flag, and the name is already honest. Keep as a rewrite lemma; not evidence. |
| `fn-exchange-ingest-refusal-is-no-op` | `exchange.lisp:364` | branch of the definition | Correct flag. Real content lives in `fn-exchange-invalid-batch-refuses-atomically`, which discharges the branch test from a weaker premise and is **not** flagged. |
| `fn-index-build-sound`, `fn-index-build-complete`, `fn-index-build-correspondence`, `fn-index-build-subset-self` | `index.lisp:194-209` | `X ⊆ X` after unfolding | Correct flag; this is §4's index row verbatim. `fn-index-build-correspondence` was cited by PRF-010 and is now dropped, leaving `fn-index-range-query-correct`, the one theorem with content. C1-09 should restate soundness and completeness against an independent enumeration. |
| `fn-node-capacity-refusal-is-no-op` | `node.lisp:367` | branch of the definition | Correct flag. Was cited by PRF-004; dropped. |
| `fn-node-{prepare,complete,recover}-preserves-committed-archive-pins` | `node-invariants.lisp:124-152` | closed-theory corollary | Correct flag; §4's PRF-002 row. The keystones are `fn-node-prepare-preserves-state` and `fn-node-state-has-committed-archive-pins`, and the latter is not flagged. |
| `fn-node-stale-completion-is-no-op` | `node.lisp:390` | branch of the definition | Correct flag. The property worth having is that a stale *generation* cannot publish; that needs the generation to be a value the caller cannot choose, which is §4's `:durable` row and is not yet true. |
| `fn-node-step-{prepare,complete,recover,no-event}-reduction` | `node-traces.lisp:156-191` | branch of the definition | Correct flag, and these are honest plumbing: they are the dispatcher's case split, used to drive the trace induction. Rename `-unfolds`. The trace theorems they feed are not flagged. |
| `fn-record-result-okp-is-parse-okp` | `records-canonicality.lisp:596` | `(equal X X)` after unfolding | Correct flag: both sides are the same body. An alias lemma; rename `-is-an-alias`. |
| `fn-retain-admission-refusal-is-no-op`, `fn-retain-wrong-evidence-does-not-release` | `retention.lisp:322, 359` | branch of the definition | Correct flag; the second is §4 row 1, cited by PRF-004 with A-POLICY and now dropped. PRF-004 cites `fn-retain-exact-release-records-its-evidence` instead, which has teeth (see `retention-teeth-tests.lisp`). |
| `fn-sn-finish-disabled-is-no-op`, `fn-sn-known-abort-disabled-is-no-op`, `fn-sn-refuse-reservation-disabled-is-no-op`, `fn-sn-open-observed-invalid-history-refuses` | `store-node-invariants.lisp:129`, `store-node-resolution.lisp:92-97`, `store-observed.lisp:319` | branch of the definition | Correct flags. None was cited. The load-bearing store theorems (`fn-sn-new-success-requires-actual-matching-durable-node-completion`, `fn-sn-actual-durable-completion-installs-record`) are not flagged and now have teeth. |
| `fn-wire-feed-closed-noop` | `wire.lisp:393` | branch of the definition | Correct flag. Not cited. Note `fn-wire-next-closed-noop`, which **is** cited by PRF-006, is not flagged — but it carries a `pending_subject` note for a different reason (below). |

No flag was judged a false positive. Two near-misses were tuned out during
development and are worth knowing about, because they are the shapes the
detector deliberately does **not** call suspect:

- `(equal t t)` conjuncts that appear only because a call site passes a literal
  — `fn-bpr-request-acceptablep`'s `authorized` argument is the constant `t` at
  every live call site, so unfolding the receiver relation produces `(equal t t)`.
  That is the review's D9, a finding about the call site, not a vacuous theorem.
  The detector requires a reflexive conjunct's sides to contain a function call.
- A local `defun` inside an `encapsulate` is a witness, not a definition. The
  detector excludes local functions from unfolding; otherwise every assumption
  in `books/assumptions.lisp` would be flagged as trivially true.

## Hypotheses found unnecessary

Eight, across five keystones. None was given a forged witness. Each is written
out in the corresponding teeth book with the argument, and each is a candidate
repair for the lane that owns the book.

| Theorem | Hypothesis | Why it cannot be refuted |
| --- | --- | --- |
| `fn-allocate-at-watermark` | `(fn-nexts-for-p configured nexts)` | `fn-allocate-memberships` and `fn-memberships-at-watermarkp` both read the group's number with `fn-next-number`, which returns `0` for an absent group; `fn-bump-number` rebuilds its argument unchanged for an absent group. Under no-duplicates the two agree whether or not `nexts` is well formed. |
| `fn-allocate-at-watermark` | `(fn-subsetp groups configured)` | Same argument: `configured` appears nowhere in either side's computation. |
| `fn-retain-known-obligation-id-is-not-reused` | `(fn-retain-statep s)` | `fn-retain-admit` refuses unless `fn-retain-admissiblep` holds, whose first conjunct is `(fn-retain-statep s)` (`retention.lisp:202-213`). Admission is already a no-op on every non-state. |
| `fn-sf-stable-records-prefix-of-crash` | `(fn-sf-crash-choicep frontier-choice record-choice)` | `fn-sf-crash` returns its argument unchanged for a choice outside the predicate, and under `fn-sf-statep` the record list is a true list, so `fn-sf-prefixp` is reflexive on it. The choice hypothesis is load-bearing for what a crash may *change*, not for what it may not *drop*. |
| `fn-nntp-step-preserves-consistent-session` | `(fn-nntp-projectionp archive)` | `fn-nntp-step` re-runs `fn-nntp-projectionp` over the whole archive on every command and answers 503 without touching the session when it fails (`nntp.lisp:1115-1116`). A non-projectable archive makes the step a session no-op, so the conclusion follows from the consistency hypothesis alone. **This is the review's D3 priced as a hypothesis**: the reason the premise is free is the availability bug. Fixing D3 should make it load-bearing. |
| `fn-exchange-admitted-ingest-retains-conflicting-evidence` | `(fn-exchange-object-for-messagep message-id stored)` | Scope-only. |
| " | `(fn-exchange-object-for-messagep message-id incoming)` | Scope-only. |
| " | `(not (equal (fn-exchange-content-id stored) (fn-exchange-content-id incoming)))` | Scope-only. `fn-exchange-ingest` retains every stored fact and adds every batch fact whatever their Message-IDs are, so the conclusion follows from the first three hypotheses. Dropping these three leaves a theorem that is still true and no longer about conflicting evidence — which is why they are written. Not a defect; worth saying out loud, because the name promises more than the statement needs. |

`fn-wildmat-pattern-matchp-is-anchored-reference` and `fn-bp-trace-preserves-node`
have **no** hypotheses, so they have no must-fail siblings. Their teeth books
instead exhibit both poles (a target each side accepts and a target each side
rejects; a trace that demonstrably changes the state while the node is
preserved), because the way an unconditional equality goes vacuous is both
sides being constant.

## Registry corrections applied

`planning/proof-events.json` is the curated half; `planning/proofs.json` `events`
is regenerated from it.

- **PRF-002** now cites `fn-install-preserves-state`, `fn-watermark-does-not-conflict`,
  `fn-allocate-at-watermark` and `fn-state-has-fresh-local-numbers` — the
  keystones — and no longer cites `fn-complete-preserves-local-number-uniqueness`
  or `fn-recover-preserves-local-number-uniqueness`, which are those keystones
  instantiated at the post-transition state.
- **PRF-004** no longer cites `fn-retain-wrong-evidence-does-not-release` or
  `fn-node-capacity-refusal-is-no-op` (both SUSPECT); it now cites
  `fn-retain-exact-release-records-its-evidence`.
- **PRF-007** no longer cites the four `journal.lisp` theorems. §4: none of the
  nine mentions `fn-journal-crash`, and the book is the historical isolated-slot
  experiment, not the adapter model.
- **PRF-010** no longer cites `fn-index-build-correspondence` (SUSPECT).
- **pending_subject** notes, which the check records but does not fail on, mark
  a cited theorem whose subject is not a function the host calls:
  `fn-wire-feed-proper-append` (PRF-006; the host calls `fn-wire-next`),
  `fn-transfer-missing-ranges-is-correct` (PRF-011),
  `fn-transfer-missing-ranges-work-public-bound` and
  `fn-transfer-missing-work-cost-bound` (PRF-016).

## Commands run

```
$ python3 -m unittest tests.test_ledger tests.test_certify_runner -v
...
Ran 30 tests in 0.458s

OK
```

```
$ make check
python3 tools/check_scaffold.py
Scaffold OK: 77 Markdown files, 49 requirements, 18 proof targets, 18 scenario specifications.
Ledger OK: cited events exist, are not SUSPECT, and planning/ledger.md is current.
Structural checks only; no ACL2 certification or scenario execution performed.
```

```
$ python3 tools/ledger.py
128 books, 1430 theorems, 1262 functions, 128 certification roots.
guards: verified=685, declared-off=34, default-guarded=178, default-unguarded=365
1537 assert-event, 43 must-fail, 7 encapsulate.
24 theorems flagged SUSPECT by shape.
```

The `declared-off` figure of 34 is `bp-outbound` 2, `bp-receipt-records` 9,
`bp-workflow-records` 10 and `checkpoint` 13 — the four books §2 of the review
lists, reproduced by the tool from the source rather than by hand.

`make certify`: see "Gate" below. It was run as
`FN_ACL2_TIMEOUT_SECONDS=3000 make certify`, not bare. The runner's default is
600 seconds per book, and `books/article-properties` exceeds that on this
machine while ten lanes are certifying concurrently: the first attempt in this
lane timed out there and took the six `article-work*` roots that include it
down with it. That is box contention, not a defect in any book -- the review's
own run certified 113 roots in 25m44s on an unloaded machine. Any lane running
the full batch during a swarm should raise the timeout the same way.

A second operational note, paid for twice in this lane: a certification started
with a trailing `&` inside a tool-call shell is killed by SIGTERM when the turn
ends. One run died at 84 of 128 roots that way, with `make: *** [certify]
Terminated: 15` as the only evidence. Start long certifications
harness-tracked, or fully detached from the shell's process group.

## Gate

GATE-RESULT-PLACEHOLDER

## Known defects

- The suspect detector's limits are real and documented in
  `docs/proofs.md#the-generated-ledger`: bounded unfolding of non-recursive
  definitions only, no tracking of binding forms beyond inlining `let`, `let*`
  and literal lambdas, `make-event` invisible, and no ability to see a theorem
  that is true, non-trivial and about the wrong subject. The absence of a flag
  is not evidence of strength.
- `default-guarded` in the ledger is an **inference** about what ACL2 does under
  the default `set-verify-guards-eagerness` of 1, not an observation. The check
  therefore accepts only `verified` for a function cited as evidence, and the
  guard-audit test books remain the authority on `:common-lisp-compliant`.
- `tools/ledger.py` parses `ACL2_BOOKS` out of the Makefile with a regexp. A
  different assignment syntax would silently produce an empty root list and the
  closure check would pass vacuously. A generated root list shared by the
  Makefile and the tool would be better.
- The teeth books' `must-fail` forms are `local`. That is the documented fix for
  the `must-fail` caveat (proofs are skipped during `include-book`, so a failing
  theorem would appear to succeed), and certification is the gate — but it does
  mean the teeth are evidence produced by `make certify`, not facts recorded in
  the world of an included book.
- `books/assumptions.lisp` is not yet included by any book. Nothing depends on
  it, so nothing can regress it except its own test book.

## Remaining gaps

- **No theorem takes an assumption as a hypothesis.** That is the whole of
  C1-14 and C1-15 after this lane. The comments in `books/assumptions.lisp` name
  the targets book by book.
- **Teeth cover one keystone per cluster**, the ones §5 names, plus the receiver
  grounding theorem. Every other theorem in the tree still has none. The
  clusters not covered at all: wire, transfer, checkpoint, index, replay,
  journal, bp-adu, bp-ingress, bp-outbound, store-observed.
- **`pending_subject` is recorded, not enforced.** `make check` does not fail on
  a citation whose subject the host never calls; it only records the note. Making
  it fail needs a machine-readable map from host call sites to core functions,
  which does not exist.
- **The ledger does not read the ACL2 world.** Everything is from the source
  text: it cannot tell you that a book certified, only that it is a Makefile
  root. `tools/certify_books.py` remains the authority on certification.

## Proposals for files this lane does not own

1. **`docs/prefixes.md`** — add a row, since `books/assumptions.lisp` introduces
   a tag and "a tag with no row is a review finding":

   | `fn-assume-` | `assumptions` | Named `A-*` assumptions as constrained functions with local witnesses; the functional-instantiation hook for platform qualification |

   The `substrate` lane will need a row for `fn-digest`/`fn-sig-verify` in
   `crypto-seam` at the same time; one edit covering both avoids a conflict.

2. **`books/crypto-seam.lisp`** (`substrate`) — give A-CRYPTO the same shape:
   an `encapsulate` with a local witness and constraints that are *not*
   unrestricted injectivity (`docs/proofs.md` forbids that), plus a test book
   with a non-witness per constraint. `books/assumptions.lisp` names the seam in
   its header and defines nothing crypto, so the two will not collide.

3. **Rename the flagged lemmas honestly**, per the review's "Name such lemmas
   honestly (`-unfolds`, `-by-definition`)". Concretely:
   `fn-node-step-*-reduction` → `-unfolds`; `fn-retain-wrong-evidence-does-not-release`
   → `fn-retain-release-non-matching-branch-by-definition`;
   `fn-af-message-id-equalp-is-exact` → `-by-definition`;
   `fn-record-result-okp-is-parse-okp` → `-is-an-alias`. A rename removes nothing
   and stops the name from outrunning the statement.

4. **`books/index.lisp`** (C1-09) — `fn-index-soundp` and `fn-index-completep`
   instantiated at `(fn-index-build articles)` are `X ⊆ X`. State them against
   the independent reference enumeration `fn-index-reference-range` that the
   book already has, the way `fn-index-range-query-correct` does.

5. **`books/nntp.lisp`** (C1-07, D3) — fixing the per-command whole-archive
   `fn-nntp-projectionp` re-validation would make that hypothesis of
   `fn-nntp-step-preserves-consistent-session` load-bearing instead of free.

6. **`tests/evidence/`** — nothing in this lane writes evidence files. A
   run-scoped evidence summary for the certify below belongs with whoever lands
   the batch; the manifest is at the path named in the gate section.
