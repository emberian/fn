# Lane dump: `assurance-tooling`

Written at the end of the session's usage window, for a Codex root picking this
up. Worktree `/Users/ember/dev/fn/build/lanes/assurance-tooling`, branch
`lane/assurance-tooling`, branched from `0bd0b5c`.

**Nothing in this lane is half-written.** Every file listed under DONE is
complete and individually certified by ACL2. The only unfinished item is the
*whole-batch* `make certify`, which was killed twice by SIGTERM before it could
finish. See "Gate" for exactly how far it got and what to re-run.

See also `HANDOFF.md` in this worktree, which is the packet deliverable and has
the full assumption table, suspect verdicts and proposals. This file is the
operational superset: what is done, what is not, and why each decision was
made, so none of it is re-derived.

---

## 1. The packet as I understood it

Lane `assurance-tooling`, packets C1-15 (assumptions as encapsulates) and C1-16
(teeth ledger) from §8 of `planning/review-2026-09-18-independent.md`. Four
parts:

1. **`books/assumptions.lisp`** — every named assumption in `specs/failures.md`
   except A-CRYPTO as an `encapsulate` with a local witness and the minimal
   constraint the existing theorems would need; a comment per constraint naming
   the theorems that should take it as a hypothesis; a `must-fail` per
   constraint in `tests/acl2/assumptions-tests.lisp` showing a non-witness
   fails it; and a description in `docs/proofs.md` of how a platform
   qualification functionally instantiates A-DURABILITY.
2. **`tools/ledger.py`** — a Python tool with its own s-expression reader
   (never the Lisp reader) that inventories events per book, computes guard
   status per function, flags SUSPECT theorems by shape, validates a curated
   `planning/proof-events.json`, regenerates the `events` arrays of
   `planning/proofs.json` from it, and emits `planning/ledger.json` and
   `planning/ledger.md`. Wired into `tools/check_scaffold.py` so `make check`
   fails on an unknown theorem name, a SUSPECT theorem cited as an event, or a
   stale `ledger.md`. Unit-tested in `tests/test_ledger.py`.
3. **Teeth books** — one `tests/acl2/<cluster>-teeth-tests.lisp` per cluster
   (13 of them) with a reachable non-degenerate witness and one `must-fail` per
   hypothesis showing the conclusion fails when that hypothesis is dropped or
   violated. A hypothesis that turns out to be unnecessary is recorded as a
   finding, never given a forged witness. Added to the Makefile.
4. **`docs/proofs.md`** — count-bearing prose replaced by a pointer to
   `planning/ledger.md`; the ledger, the suspect detector and its limits
   described honestly.

Owned: the files above plus the Makefile root list and `planning/proofs.json`
`events` arrays only (ids, titles, statuses and evidence lists must not move).
Not owned: every existing book. `books/crypto-seam.lisp` belongs to the
`substrate` lane, which defines `fn-digest` and `fn-sig-verify`; A-CRYPTO was
therefore deliberately left out of `books/assumptions.lisp`.

---

## 2. DONE

All committed. `git log --oneline -2`:

```
40abd6f Record the lane handoff and drop three unused ledger helpers
27580aa Generate the assurance ledger and give the keystones teeth
```

### 2.1 `books/assumptions.lisp` — seven encapsulates

Certified: evidence `build/acl2/certify-20260919T053412Z-95528`
("ACL2 certification passed: books/assumptions, tests/acl2/assumptions-tests,
tests/acl2/cbor-teeth-tests").

Verbatim exported constraints, in file order. Signatures and local witnesses
are in the book; every constraint below is proved of its witness by ACL2.

```lisp
;; A-DURABILITY   (((fn-assume-durability-image * *) => *))
;;   witness: (lambda (barriered unbarriered) barriered)
(defthm fn-assume-durability-retains-barriered
  (implies (member-equal record barriered)
           (member-equal record (fn-assume-durability-image barriered unbarriered))))

(defthm fn-assume-durability-invents-nothing
  (implies (member-equal record (fn-assume-durability-image barriered unbarriered))
           (or (member-equal record barriered)
               (member-equal record unbarriered)))
  :rule-classes nil)

;; A-WRITE-ISOLATION   (((fn-assume-write-isolation-observe * *) => *))
;;   witness: (lambda (committed pending) committed)
(defthm fn-assume-write-isolation-retains-committed
  (implies (member-equal unit committed)
           (member-equal unit (fn-assume-write-isolation-observe committed pending))))

(defthm fn-assume-write-isolation-adds-nothing-foreign
  (implies (and (member-equal unit (fn-assume-write-isolation-observe committed pending))
                (not (member-equal unit pending)))
           (member-equal unit committed))
  :rule-classes nil)

;; A-HOST   (((fn-assume-host-report *) => *) ((fn-assume-host-events *) => *))
;;   witnesses: identity on both
(defthm fn-assume-host-success-is-earned
  (implies (equal (fn-assume-host-report outcome) :success)
           (equal outcome :success))
  :rule-classes nil)

(defthm fn-assume-host-keeps-uncertainty
  (implies (equal outcome :indeterminate)
           (equal (fn-assume-host-report outcome) :indeterminate)))

(defthm fn-assume-host-preserves-event-order
  (equal (nth n (fn-assume-host-events events))
         (nth n events)))

;; A-PEER   (((fn-assume-peer-retainsp * *) => *))
;;   witness: (lambda (receipt failures) (consp receipt))
(defthm fn-assume-peer-needs-a-receipt
  (implies (not (consp receipt))
           (not (fn-assume-peer-retainsp receipt failures))))

;; A-IDENTITY   (((fn-assume-identity-freshp * *) => *))
;;   witness: (lambda (identity issued) (not (member-equal identity issued)))
(defthm fn-assume-identity-issued-is-not-fresh
  (implies (member-equal identity issued)
           (not (fn-assume-identity-freshp identity issued))))

;; A-POLICY   (((fn-assume-policy-authorizedp * * *) => *))
;;   witness: (lambda (policy-id terms evidence)
;;              (and (consp policy-id) (consp terms) (consp evidence)))
(defthm fn-assume-policy-needs-evidence
  (implies (not (consp evidence))
           (not (fn-assume-policy-authorizedp policy-id terms evidence))))

(defthm fn-assume-policy-needs-terms
  (implies (not (consp terms))
           (not (fn-assume-policy-authorizedp policy-id terms evidence))))

;; A-FAIRNESS   (((fn-assume-fairness-contact-index * *) => *))
;;   witness: (lambda (route schedule) 0)
(defthm fn-assume-fairness-contact-index-is-finite
  (natp (fn-assume-fairness-contact-index route schedule)))
```

`tests/acl2/assumptions-tests.lisp` gives each constraint a concrete
non-witness and a `(local (must-fail (defthm ...)))` in which the constraint's
own statement is **ground-false** for that candidate — ACL2 computes both sides
and refuses the theorem. Ten such cases: a barrier that drops the oldest
record; a crash image that fabricates `:phantom`; a shared-sector layout that
erases a committed neighbour; an adapter that reports `:success` for
`:indeterminate`; one that collapses `:indeterminate` to `:refused`; one that
reverses the event list; a credulous peer that retains without a receipt; an
always-fresh identity allocator; a policy that authorizes on the stored bit
with no evidence and with no terms; and a contact index of `:eventually`.

### 2.2 `tools/ledger.py` and its wiring

- `tools/ledger.py` — reader, ledger generator, suspect detector, registry
  validator. Modes: bare (report to stdout), `--write`, `--check`.
- `tools/check_scaffold.py` — imports `tools.ledger` and folds
  `ledger.check_problems()` into its `ERRORS` list, so `make check` fails on
  ledger drift and prints the reasons.
- `planning/proof-events.json` — the curated map (14 targets, 167 events).
- `planning/ledger.json`, `planning/ledger.md` — generated; `make check`
  fails if either is stale.
- `planning/proofs.json` — `events` arrays regenerated; ids, titles,
  statuses, evidence, statements, milestones, requirements, depends_on,
  assumptions and progress_note untouched.
- `tests/test_ledger.py` — 26 unit checks.

Last generated figures (`python3 tools/ledger.py`):

```
128 books, 1430 theorems, 1262 functions, 128 certification roots.
guards: verified=685, declared-off=34, default-guarded=178, default-unguarded=365
1537 assert-event, 43 must-fail, 7 encapsulate.
24 theorems flagged SUSPECT by shape.
```

`declared-off=34` reproduces the review's §2 sweep exactly from source:
`bp-outbound` 2, `bp-receipt-records` 9, `bp-workflow-records` 10,
`checkpoint` 13.

### 2.3 Teeth books — all 13 clusters, all certified

Every one of the 13 clusters the packet names has a teeth book, and every one
certifies. **None is missing.** The per-book certification evidence:

| Teeth book | Keystone(s) | Certified in |
| --- | --- | --- |
| `tests/acl2/acceptance-teeth-tests.lisp` | `fn-install-preserves-state`, `fn-watermark-does-not-conflict`, `fn-allocate-at-watermark` | `build/acl2/certify-20260919T053250Z-93873` |
| `tests/acl2/retention-teeth-tests.lisp` | `fn-retain-exact-release-records-its-evidence`, `fn-retain-release-preserves-independent-pin`, `fn-retain-known-obligation-id-is-not-reused` | same |
| `tests/acl2/node-teeth-tests.lisp` | `fn-node-install-stage-preserves-state` | same |
| `tests/acl2/cbor-teeth-tests.lisp` | `fn-cbor-value-round-trip`, `fn-cbor-accepted-input-is-canonical` | `build/acl2/certify-20260919T053412Z-95528` |
| `tests/acl2/records-teeth-tests.lisp` | `fn-record-round-trip`, `fn-record-accepted-input-is-canonical` | `build/acl2/certify-20260919T053602Z-97045` |
| `tests/acl2/article-teeth-tests.lisp` | `fn-article-successful-parse-preserves-source` | same |
| `tests/acl2/exchange-teeth-tests.lisp` | `fn-exchange-admitted-ingest-retains-conflicting-evidence` | same |
| `tests/acl2/wildmat-teeth-tests.lisp` | `fn-wildmat-rightmost-match-is-last-reference-match`, `fn-wildmat-pattern-matchp-is-anchored-reference` | `build/acl2/certify-20260919T053802Z-98835` |
| `tests/acl2/bp-workflow-teeth-tests.lisp` | `fn-bp-trace-preserves-node` | same |
| `tests/acl2/store-node-teeth-tests.lisp` | `fn-sn-actual-durable-completion-installs-record`, `fn-sn-new-success-requires-actual-matching-durable-node-completion` | `build/acl2/certify-20260919T053934Z-112` |
| `tests/acl2/store-files-teeth-tests.lisp` | `fn-sf-success-requires-matching-completion`, `fn-sf-stable-records-prefix-of-crash` | `build/acl2/certify-20260919T054103Z-2098` (after one fix, below) |
| `tests/acl2/nntp-teeth-tests.lisp` | `fn-nntp-step-preserves-consistent-session` | same |
| `tests/acl2/bp-receiver-teeth-tests.lisp` | `fn-bprv-replayed-receipt-is-grounded` | `build/acl2/certify-20260919T054212Z-3245` |

Verbatim keystone statements are quoted in a comment block above the teeth in
each book, so the book and the theorem cannot drift apart silently.

### 2.4 `docs/proofs.md`

- The count-bearing paragraph now opens "No count appears in this document" and
  points at `planning/ledger.md`.
- New section **"The generated ledger"** with subsections "Guard status",
  "The suspect detector and what it cannot see" (six shapes, six named limits),
  and **"Qualifying a platform against A-DURABILITY"**, which spells out the
  `:functional-instance` discharge.
- "Registry states" now says the `events` arrays are generated from
  `planning/proof-events.json` and explains `pending_subject`.

### 2.5 Makefile

15 roots added: `books/assumptions`, `tests/acl2/assumptions-tests`, and the 13
teeth books, each placed immediately after the cluster it tests. The list is
now 128 roots.

---

## 3. IN PROGRESS — only the whole-batch certify

**Everything else is finished.** The single open item is a green whole-batch
`make certify` over all 128 roots.

State: **not achieved in this lane.** Three attempts:

| Attempt | Command | Log | Evidence dir | Outcome |
| --- | --- | --- | --- | --- |
| 1 | `make certify` (started 03:34Z, before the teeth roots existed) | `build/certify-baseline.log` | `build/acl2/certify-20260919T033410Z-70586` | Killed with the shell when the session was cut. 106 of 113 roots had certs afterwards; the 7 without were `books/article-properties` and the six `article-work*` roots that include it. |
| 2 | `FN_ACL2_TIMEOUT_SECONDS=3000 make certify` (05:51Z) | `build/certify-gate.log` (overwritten) | `build/acl2/certify-20260919T055149Z-9396` | Reached **84 of 128** roots, then `make: *** [certify] Terminated: 15`. Killed by SIGTERM at a turn boundary because it was launched with a trailing `&` inside the tool-call shell. |
| 3 | `FN_ACL2_TIMEOUT_SECONDS=1800 make certify` (06:25Z), launched harness-tracked | `build/certify-gate.log` (current) | `build/acl2/certify-20260919T062515Z-27922` | Reached **31 of 128** roots, then `make: *** [certify] Terminated: 15` again when the session's usage window closed. |

**Exact error text, both times, and it is the only failure text in this lane:**

```
make: *** [certify] Terminated: 15
```

That is SIGTERM to the process group, not an ACL2 failure. No `ACL2 Error`, no
`CERTIFICATION FAILED`, and no timeout marker appears in any of the three
evidence directories for a book this lane wrote.

**To finish:** run, fully detached from the tool-call shell,

```
cd /Users/ember/dev/fn/build/lanes/assurance-tooling
FN_ACL2_TIMEOUT_SECONDS=1800 make certify > build/certify-gate.log 2>&1
```

Expect roughly 35–45 minutes under ten-lane contention; `books/article-properties`
alone takes 8–15 minutes there and needs the raised timeout (the runner's
default is 600 s and that book exceeds it under load — another lane's baseline
failed on exactly that book with 112 of 113 roots green). Success looks like

```
ACL2 certification passed: <128 roots>
Certification evidence: build/acl2/certify-<stamp>
```

There is no reason to expect a book from this lane to fail: all 15 new roots
certified individually against the already-certified closure, in the runs
tabulated in §2.3.

---

## 4. NOT STARTED

- **No teeth book is missing.** All 13 clusters named in the packet are done.
- Clusters with no teeth at all, because the packet did not ask for them:
  wire, transfer, checkpoint, index, replay, journal, bp-adu, bp-ingress,
  bp-outbound, store-observed, store-node-resolution, bp-workflow-records.
- **No theorem in the tree takes an assumption as a hypothesis.** The
  encapsulates state the assumptions; wiring them into the theorems is C1-14
  and C1-15 work, and each constraint's comment names its targets.
- `pending_subject` is recorded but not enforced by `make check`.

---

## 5. Design decisions, and why

### 5.1 `books/assumptions.lisp` includes nothing

It sits at the bottom of the tree and its constraints are over abstract values
(lists, outcomes, identities), not over any book's state representation. Two
reasons: it certifies in seconds and cannot be broken by another lane editing a
book; and a later refinement can functionally instantiate a constraint wherever
the corresponding theorem lives rather than being tied to one representation.
The cost is that nothing depends on it yet, so nothing but its own test book
can regress it. That is recorded as a known defect.

### 5.2 A-CRYPTO is deliberately absent

`books/crypto-seam.lisp` (the `substrate` lane) owns `fn-digest` and
`fn-sig-verify`. A second constrained crypto function here would be exactly the
twin §4 of the review says to delete. The book's header says so. **Proposal for
`substrate`:** give A-CRYPTO the same shape there — an encapsulate with a local
witness and constraints that are *not* unrestricted injectivity (which
`docs/proofs.md` forbids), plus a test book with a non-witness per constraint.

### 5.3 `:rule-classes nil` on two constraints

`fn-assume-host-success-is-earned` was first written with default rule classes
and ACL2 refused it: *"A :REWRITE rule generated from
FN-ASSUME-HOST-SUCCESS-IS-EARNED is illegal because it rewrites the variable
symbol OUTCOME."* A constraint is part of an encapsulate's constraint whatever
its rule classes, so `:rule-classes nil` costs the assumption nothing; a user
discharges it with `:use`. The same applies to
`fn-assume-durability-invents-nothing` and
`fn-assume-write-isolation-adds-nothing-foreign`, which are disjunctive.

### 5.4 `must-fail` forms are `local`

std/testing's documented caveat: a non-local form that causes proofs to be done
may not be includable, because proofs are skipped during `include-book`, so a
failing theorem would appear to succeed and `must-fail` would fail. `must-fail!`
does not exist in ACL2 8.7's `std/testing/must-fail`; `must-fail-local` does,
and is exactly `(local (must-fail ...))`. Certification is the gate, so the
teeth are evidence produced by `make certify`. Written as
`(local (must-fail (defthm ...)))` rather than via `must-fail-local` so the
`include-book` line the packet named is the one in the file.

### 5.5 Every negative case is a **ground** term

A `must-fail` around a general weakened theorem only shows "the prover did not
find a proof". A ground instance where ACL2 computes both sides and gets `nil`
is a counterexample. Every negative case in every teeth book and in
`assumptions-tests.lisp` is ground, which also makes them fast.

### 5.6 The suspect detector: six shapes, and why each is sound

The packet named four shapes; two more were added because the review's §4 rows
needed them. All six are *shape* claims, never truth claims. False positives
matter because `--check` hard-fails on citing a flagged theorem, so each
detector was tightened until it fired only on real instances. The tightening
history is worth keeping:

1. **`closed-theory-corollary`** — the theorem's only hint is `:in-theory` over
   an explicit quoted list, every member of which is a `defthm` in the tree.
   Then the statement follows by rewriting and the work is in those lemmas.
   Fires on the three `fn-node-*-preserves-committed-archive-pins`, which is
   §4's PRF-002 row verbatim.
2. **`instance-corollary`** — a `:use (:instance L subs)` hint where `L`'s
   conclusion under `subs` is structurally this conclusion **and** every
   hypothesis of `L` under `subs` already appears among this theorem's
   hypotheses, so nothing was discharged. *The hypothesis-superset condition is
   the whole tightening.* Without it the detector flagged `fn-bpa-round-trip`
   (a genuine case-split keystone the review praises) and
   `fn-exchange-unknown-schema-batch-refuses-atomically` (which enables a
   weaker premise). With it, only `fn-index-build-subset-self` fires.
3. **`reflexive-conclusion`** — a conjunct of the conclusion is `X R X` for
   `R` in `{equal, iff, =, subsetp, subsetp-equal, fn-subsetp}`, checked both
   before and after bounded unfolding of non-recursive definitions, with the
   conjuncts re-flattened after unfolding. *Two tightenings:* the two sides
   must contain a function call, so `(equal t t)` arising from a literal
   argument is not flagged; and unfolding must re-flatten `and`, or
   `fn-index-build-correspondence` escapes.
4. **`definition-restated`** — the conclusion is `(equal (f args) B)` or
   `(iff ...)` where `B` is `f`'s body under the formal substitution, **or**
   that body with the conjuncts the theorem's own hypotheses already assert
   struck out. The second form is what catches
   `fn-af-message-id-equalp-is-exact`, §4's OBJ-002 row.
5. **`recognizer-body-conclusion`** — the conclusion is the body of a
   hypothesis's own recognizer.
6. **`branch-of-definition`** — a hypothesis is a branch test of a function the
   conclusion calls, or its negation, **and** the conclusion is exactly that
   branch's value. *The second conjunct is the tightening.* Without it the
   detector fired 98 times, including on genuinely strong theorems such as
   `fn-exchange-admitted-ingest-retains-conflicting-evidence` whose hypothesis
   merely happens to be an `if` test. With it, 13 fire, each a real definitional
   restatement, including §4 row 1
   (`fn-retain-wrong-evidence-does-not-release`). Seeing that one required
   inlining `let`/`let*`/lambda before collecting `if` triples, because
   `fn-retain-release` names its branch test with a `let` variable.

Two further deliberate exclusions:

- **A local `defun` inside an `encapsulate` is a witness, not a definition.**
  The detector's function table excludes local defuns. Otherwise unfolding the
  witness makes every assumption in `books/assumptions.lisp` look trivially
  true — `fn-assume-host-preserves-event-order` was flagged exactly that way
  before the fix.
- **`(equal t t)` from constant propagation is not a vacuous theorem.**
  `fn-bpr-request-acceptablep`'s `authorized` argument is the literal `t` at
  every live call site, so unfolding the receiver relation produces `(equal t t)`.
  That is the review's D9 — a finding about the call site — and the detector
  says nothing about it.

The detector went 98 → 27 → 24 flags across these tightenings; the 24 are
tabulated with a verdict each in `HANDOFF.md` §"The suspect list". **No flag
was judged a false positive.**

### 5.7 Guard status: four states, only one of them an observation

`verified` (a `verify-guards` event or `:verify-guards t`), `declared-off`,
`default-guarded` (no `:verify-guards` but an explicit `:guard` or `type`
declaration — under the default `set-verify-guards-eagerness` of 1 ACL2
verifies at definition time), `default-unguarded`. Only `verified` is read off
the source; `default-guarded` is an *inference* about what ACL2 did. The
registry check therefore accepts only `verified` for a function cited as
evidence (PRF-014 cites four), and the guard-audit test books remain the
authority on `:common-lisp-compliant`.

### 5.8 `proof-events.json` is the one hand-edited half

`proofs.json` `events` is generated from it. The alternative — generating
citations from the books — cannot work: which theorem supports which target is
a judgment. So the judgment is isolated in one small file and *checked*
mechanically.

### 5.9 The `proof-events.json` corrections — do not redo these

Applied once, from the current `proofs.json` `events` plus the review:

- **PRF-002** — removed `fn-complete-preserves-local-number-uniqueness` and
  `fn-recover-preserves-local-number-uniqueness` (each is
  `fn-state-has-fresh-local-numbers` instantiated at the post-transition
  state); added, in front, `fn-install-preserves-state`,
  `fn-watermark-does-not-conflict`, `fn-allocate-at-watermark` and
  `fn-state-has-fresh-local-numbers`. Kept
  `fn-durable-completion-installs-exact-pending-article`.
- **PRF-004** — removed `fn-retain-wrong-evidence-does-not-release` (SUSPECT,
  §4 row 1) and `fn-node-capacity-refusal-is-no-op` (SUSPECT); added
  `fn-retain-exact-release-records-its-evidence`, which has teeth.
- **PRF-007** — removed all four `journal.lisp` theorems
  (`fn-journal-known-abort-has-no-marker`,
  `fn-journal-scan-missing-dependency-fault`,
  `fn-journal-scan-commit-gap-fault`,
  `fn-journal-recover-torn-anchored-commit-fault`). None mentions
  `fn-journal-crash`; the book is the historical isolated-slot experiment.
- **PRF-010** — removed `fn-index-build-correspondence` (SUSPECT), leaving
  `fn-index-rebuild-correspondence` and `fn-index-range-query-correct`.
- **`pending_subject` notes** added, recorded but not failed on:
  `fn-wire-feed-proper-append` (PRF-006 — the host calls `fn-wire-next`),
  `fn-transfer-missing-ranges-is-correct` (PRF-011),
  `fn-transfer-missing-ranges-work-public-bound` and
  `fn-transfer-missing-work-cost-bound` (PRF-016 — the subject has no caller
  outside the transfer books).

No id, title, status, statement, milestone, requirement link, dependency,
assumption list or evidence path was touched anywhere in `proofs.json`.

### 5.10 Eight hypotheses found unnecessary — recorded, never forged

Full table with arguments in `HANDOFF.md` §"Hypotheses found unnecessary", and
each is written out in the corresponding teeth book. In brief:
`fn-allocate-at-watermark` H1 (`fn-nexts-for-p`) and H2 (`fn-subsetp groups
configured`); `fn-retain-known-obligation-id-is-not-reused` H1
(`fn-retain-statep`); `fn-sf-stable-records-prefix-of-crash` H2
(`fn-sf-crash-choicep`); `fn-nntp-step-preserves-consistent-session` H2
(`fn-nntp-projectionp`) — **this one is the review's D3 priced as a
hypothesis**, free precisely because the step re-validates the whole archive
and 503s without touching the session, so fixing D3 should make it
load-bearing; and the three conflict-scoping hypotheses of
`fn-exchange-admitted-ingest-retains-conflicting-evidence`, which scope the
claim rather than enable it.

`fn-wildmat-pattern-matchp-is-anchored-reference` and
`fn-bp-trace-preserves-node` have **no** hypotheses. Their teeth books instead
exhibit both poles, because the way an unconditional equality goes vacuous is
both sides being constant.

### 5.11 Two bugs found in my own teeth during certification

Both fixed; recorded so the same mistakes are not repeated.

1. `books/assumptions.lisp` — `fn-assume-host-success-is-earned` rejected as a
   rewrite rule on a variable (§5.3).
2. `tests/acl2/store-files-teeth-tests.lisp` — the forged non-state was built
   as a raw 8-element `list`, but an `fn-sf` state is a **9**-element list
   whose head is the tag `:store-files`, so `fn-sf-records` read `nil` and
   `(fn-sf-prefixp nil nil)` was true, which made the `must-fail` fail. Fixed
   by constructing it with `fn-sf-make`. Lesson: build forged states with the
   book's own constructor and break one *field*, never by writing the list
   shape out by hand.

---

## 6. Gate commands and last results

```
$ python3 -m unittest tests.test_ledger tests.test_certify_runner -v
...
Ran 30 tests in 0.458s

OK
```

```
$ make check
python3 tools/check_scaffold.py
Scaffold OK: 78 Markdown files, 49 requirements, 18 proof targets, 18 scenario specifications.
Ledger OK: cited events exist, are not SUSPECT, and planning/ledger.md is current.
Structural checks only; no ACL2 certification or scenario execution performed.
```

The ledger gate red-proofs itself. Injecting a SUSPECT citation, an unknown
theorem name, and a stale `ledger.md` produced, and the tree was restored
afterwards:

```
ERROR: ledger: PRF-001: fn-retain-wrong-evidence-does-not-release is SUSPECT (branch-of-definition: ...)
ERROR: ledger: PRF-001: no such theorem in books/ or tests/acl2/: fn-no-such-theorem-anywhere
ERROR: ledger: planning/proofs.json: stale; run `python3 tools/ledger.py --write`
make: *** [check] Error 1
ERROR: ledger: planning/ledger.md: stale; run `python3 tools/ledger.py --write`
make: *** [check] Error 1
```

`make certify`: see §3. Not green as a whole batch; every new root green
individually. ACL2 8.7 / SBCL, macOS arm64, as recorded in each manifest.

---

## 7. Known defects

- **The whole-batch `make certify` has never completed in this lane.** §3.
- The suspect detector's limits, all documented in
  `docs/proofs.md#the-generated-ledger`: bounded unfolding of non-recursive
  definitions only; substitution does not track binding forms beyond inlining
  `let`, `let*` and literal lambdas; `make-event` invisible; it cannot see a
  theorem that is true, non-trivial and about the wrong subject. **The absence
  of a flag is not evidence of strength.**
- `default-guarded` is an inference, not an observation (§5.7).
- `tools/ledger.py` parses `ACL2_BOOKS` out of the Makefile with a regexp. A
  different assignment syntax would silently produce an empty root list and the
  closure check would pass vacuously. A generated root list shared by the
  Makefile and the tool would be better.
- The teeth `must-fail` forms are `local`, so the teeth are evidence produced
  by `make certify`, not facts in the world of an included book.
- `books/assumptions.lisp` is included by nothing, so nothing but its own test
  book can regress it.
- `pending_subject` is recorded, not enforced.

---

## 8. Proposals for files this lane does not own

1. **`docs/prefixes.md`** — `books/assumptions.lisp` introduces a tag, and "a
   tag with no row is a review finding". Add:

   | `fn-assume-` | `assumptions` | Named `A-*` assumptions as constrained functions with local witnesses; the functional-instantiation hook for platform qualification |

   The `substrate` lane needs a row for `fn-digest`/`fn-sig-verify` in
   `crypto-seam` at the same time; one edit covering both avoids a conflict.
   **This is the one thing left undone that the assurance rules ask for**, and
   it was left to the owner on purpose.

2. **`books/crypto-seam.lisp`** (`substrate`) — A-CRYPTO as an encapsulate with
   the same shape (§5.2).

3. **Rename the flagged lemmas honestly**, per "Name such lemmas honestly
   (`-unfolds`, `-by-definition`)": `fn-node-step-*-reduction` → `-unfolds`;
   `fn-retain-wrong-evidence-does-not-release` →
   `fn-retain-release-non-matching-branch-by-definition`;
   `fn-af-message-id-equalp-is-exact` → `-by-definition`;
   `fn-record-result-okp-is-parse-okp` → `-is-an-alias`. A rename removes
   nothing and stops the name outrunning the statement. **Note for whoever does
   it:** these names appear in `planning/ledger.md`, which is generated — run
   `python3 tools/ledger.py --write` afterwards or `make check` will fail.

4. **`books/index.lisp`** (C1-09) — `fn-index-soundp` and `fn-index-completep`
   instantiated at `(fn-index-build articles)` are `X ⊆ X`. State them against
   the independent reference enumeration `fn-index-reference-range` the book
   already has, the way `fn-index-range-query-correct` does.

5. **`books/nntp.lisp`** (C1-07, D3) — fixing the per-command whole-archive
   `fn-nntp-projectionp` re-validation would make that hypothesis of
   `fn-nntp-step-preserves-consistent-session` load-bearing instead of free.

6. **`tests/evidence/`** — nothing in this lane writes evidence files. A
   run-scoped summary belongs with whoever lands the batch, from the manifest
   of the completed `make certify`.

7. **Operational, for the swarm runner** — raise
   `FN_ACL2_TIMEOUT_SECONDS` to at least 1800 for any full-batch certify while
   lanes share the box, and never launch one with a trailing `&` inside a
   tool-call shell (§3).

---

## 9. Dirty and untracked files

At the time of writing, before the WIP commit:

```
?? LANEDUMP-assurance-tooling.md
```

Everything else this lane produced is committed at `40abd6f`. `git status
--short` showed nothing else — no modified tracked file, no other untracked
file. `build/` is git-ignored and holds the certification logs and evidence
directories named in §2.3 and §3.

Files this lane touched, all committed:

```
books/assumptions.lisp                        (new)
tests/acl2/assumptions-tests.lisp             (new)
tests/acl2/acceptance-teeth-tests.lisp        (new)
tests/acl2/retention-teeth-tests.lisp         (new)
tests/acl2/node-teeth-tests.lisp              (new)
tests/acl2/cbor-teeth-tests.lisp              (new)
tests/acl2/records-teeth-tests.lisp           (new)
tests/acl2/article-teeth-tests.lisp           (new)
tests/acl2/wildmat-teeth-tests.lisp           (new)
tests/acl2/exchange-teeth-tests.lisp          (new)
tests/acl2/nntp-teeth-tests.lisp              (new)
tests/acl2/store-files-teeth-tests.lisp       (new)
tests/acl2/store-node-teeth-tests.lisp        (new)
tests/acl2/bp-workflow-teeth-tests.lisp       (new)
tests/acl2/bp-receiver-teeth-tests.lisp       (new)
tools/ledger.py                               (new)
tests/test_ledger.py                          (new)
planning/proof-events.json                    (new)
planning/ledger.json                          (new, generated)
planning/ledger.md                            (new, generated)
HANDOFF.md                                    (new)
tools/check_scaffold.py                       (modified: imports and calls the ledger check)
docs/proofs.md                                (modified: new ledger section; counts removed)
planning/proofs.json                          (modified: events arrays only)
Makefile                                      (modified: 15 roots added)
```
