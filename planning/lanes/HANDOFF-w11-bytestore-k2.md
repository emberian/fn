# Handoff: lane `w11/bytestore-k2` (K2f, and prefix recoverability)

Branch `w11/bytestore-k2` in `build/lanes/w11-bytestore-k2`, from `dev` at
`38460cf`, merged `dev` at `e67b6cb`. Both packets the kernel lane named,
in its order. Nothing in D14-a or D14-b is reopened: `fn-sf-crash-imagep` is
unchanged byte for byte, so `fn-own-reopen`'s gate and the eleven theorems
that take it as a premise are untouched and `*own-reopened*` still says why.

## 1. K2f: the shape, and why it admits exactly the reachable window

`specs/crash-model-v2.md` K2 was FALSE in the frontier sub-case, as the
kernel lane found. `fn-sf-recovery-crash-imagep` gains a third frontier arm:

```lisp
(and (fn-sf-frontier-rollback-visiblep s)
     (equal frontier (1- (fn-sf-frontier s)))
     (equal records (fn-sf-records s)))
```

with the gate

```lisp
(defun fn-sf-frontier-rollback-visiblep (s)
  (and (fn-sf-recovery-visiblep s)
       (null (fn-sf-successes s))
       (posp (fn-sf-frontier s))
       (fn-sf-record-listp (fn-sf-records s) 0 0 (1- (fn-sf-frontier s)))))
```

and the constructor `fn-sf-crash-frontier-rollback`. **Checked against the
transcribed program before adopting it**, as the kernel lane asked, and two
of the four conjuncts are not in the shape it proposed.

* **The record-list conjunct is the one the kernel lane named**, and it is
  the correspondence rather than a proof convenience. `fn-sf-statep` demands
  every record's txid below the frontier; `advance_frontier` reserves txid
  `frontier-1` for the record published AFTER the rename is durable
  (`fn-sf-candidatep`: the candidate's txid is `frontier-1`). So while the
  rename is pending no record holds that txid, and the moment that record is
  published the conjunct is false and the frontier can no longer roll back.
  It carries three loads: `fn-sf-crash-frontier-rollback-preserves-state`,
  `fn-sf-recovery-admissible-image-facts` over the new arm, and
  replayability at the lower frontier
  (`fn-snt-recovery-admissible-crash-image-is-recoverable`).
* **`posp` is not implied by it.** With frontier `0` the arm offers `-1`,
  and `(fn-sf-record-listp nil 0 0 -1)` is T, so the record-list conjunct
  does not exclude it while `fn-record-uint32p` does. Tooth in the test book.
* **`(null (fn-sf-successes s))` is added and is NOT the record arm's
  reason** -- rolling the frontier back drops no record. It is the only
  kernel-visible mark separating a `:replaying` state built by
  `fn-sn-open-observed` from THIS process's scan, where the rename may still
  be pending, from one reached by `fn-sf-crash`, where the model already
  knows it is not: a crash from `:reserved` has observed
  `(:frontier-directory :ok)`, so `fsync_dir(self.root)` returned; and a
  crash from `:frontier-attempted` is already `fn-sf-crash`'s `:old` choice,
  because `fn-sf-frontier-new-visiblep` holds there. Without it the
  predicate admits, on a crashed `:reserved` state, an image the same model
  refutes. `*fn-so-reserved-crashed*` is that state and is the tooth. It
  costs `K2` nothing: `fn-bs-replay-matches-scan` already carries
  `(equal (fn-sf-successes ks) nil)`.
* **`(equal records (fn-sf-records s))` is EXCLUSIVITY and is new.** The
  image that loses both the rename and the link is one no platform can
  produce: `advance_frontier` sets `self.fenced` before `os.replace` and
  clears it only after `fsync_dir(self.root)`, `publish` refuses while fenced
  (`run_store.py:1339`) and symmetrically, and neither runs before recovery
  completes -- so a dead process leaves at most one un-fenced authority
  entry. Outside the window `fn-bs-pending-matches-phase` gets this for free,
  because `fn-sf-frontier-new-visiblep` and `fn-sf-record-present-visiblep`
  are disjoint phase sets; inside it the phase says nothing, so the arm says
  it and `fn-bs-replay-matches-scan` carries `(null txn-ops)`.

`fn-sf-crash-choicep` gains no choice and `fn-sn-crash` is untouched, for
D14-b's reason in its frontier spelling: a trace that could roll the frontier
back would let a later trace re-issue a txid an earlier process published
under, and a trace event carries no gate.

Recorded as **D14-c** in `planning/decisions.md`; `specs/crash-model-v2.md`
§3.2, §3.3 and §7's K2, K2f and K3 rows are rewritten to match.

## 2. Packet 2: prefix recoverability, and the two theorems it unlocks

`fn-sn-replay-loop-append` gives ok(whole) implies ok(prefix). What was
missing is that the prefix node is IDLE with `next-txid <= frontier` -- which
is exactly `fn-replay-advance-okp`, the one thing `fn-sf-history-recoverablep`
needs beyond a successful replay. `books/store-node-invariants.lisp` gains it.

Proof vocabulary, all `local`: `fn-snt-record-txid-is-a-natural`,
`fn-snt-advance-off-gate-is-identity`,
`fn-snt-apply-record-from-idle-is-idle-at-successor` (one record from an idle
node leaves an idle node at `1+ txid`), its `:linear` half
`fn-snt-apply-record-from-idle-needs-its-txid`,
`fn-snt-replay-loop-ok-was-given-a-node`,
`fn-snt-replay-loop-from-idle-is-idle-and-monotone`, `fn-snt-txids-below`
with `fn-snt-record-listp-gives-txids-below`,
`fn-snt-replay-loop-from-idle-is-under-bound`, `fn-snt-initial-node-is-idle`.

Exported:

* `fn-snt-replayed-history-node-is-idle` -- a successfully replayed history
  leaves an idle node;
* `fn-snt-history-recoverable-under-record-bound` -- a history whose txids
  are all below a bound is recoverable AT that bound. **This is the frontier
  arm discharged**: its `fn-sf-record-listp` hypothesis is literally the gate
  `fn-sf-frontier-rollback-visiblep` carries;
* `fn-snt-history-recoverable-prefix` (`:rule-classes nil`, because the
  suffix is free) and its rewrite corollary
  `fn-snt-history-recoverable-of-but-last` -- **this is the record arm
  discharged**.

On them, two theorems the kernel lane's first widening attempt could not have:

* `fn-snt-recovery-admissible-crash-image-is-recoverable`
  (`books/store-node-traces.lisp`) -- the platform twin of
  `fn-snt-admissible-crash-image-is-recoverable`, which is row 5 of the
  kernel lane's table and the form that failed in its wide run
  `run-20260920T211812Z-1f0a`. Every image the platform may leave is
  replayable at its own frontier.
* `fn-sn-recovery-admissible-image-reopens` (`books/store-observed.lisp`) --
  the host's reopen entry succeeds on every one of them. This is the half of
  `specs/crash-model-v2.md` K4 that the wider predicate makes new.

**The acknowledged-record half of K4 is deliberately NOT restated over the
wider predicate.** On both rollback arms the arm's own
`(null (fn-sf-successes s))` and a `(member-equal pair (fn-sf-successes ...))`
hypothesis are contradictory, so the restatement would be
`fn-sn-acknowledged-record-survives-observed-reopen` with two vacuous arms.
What carries the acknowledged record across the wider predicate is
`fn-sf-recovery-admissible-image-facts`, which says it over every arm with no
vacuous one. Recording this rather than shipping the degenerate theorem is
the AGENTS.md rule applied, not a gap.

## 3. Every theorem that takes a predicate this lane touched as a premise

Enumerated before editing and re-run after, mechanically: every
`defthm`/`defun`/`defun-sk` form in `books/` and `tests/acl2/` whose
STATEMENT mentions each name, classified premise / conclusion / mention by
whether the name occurs inside the `implies` hypothesis. Each row carries a
verdict and a separation witness.

### `fn-sf-recovery-crash-imagep` -- WIDENED. Four premise-takers, all in `books/store-files-invariants.lisp`.

| # | theorem | verdict | separation witness |
| --- | --- | --- | --- |
| 1 | `fn-sf-recovery-crash-realizes-every-admissible-image` | statement unchanged, **re-proved over four arms**; `fn-sf-image-crash` gains a third branch and `fn-sf-crash-frontier-rollback` is its constructor | `*fn-so-gap-opened*`: `(fn-sf-image-crash ... 3 (first second))` IS `fn-sf-crash-frontier-rollback`, and its frontier is 3 with the records intact |
| 2 | `fn-sf-recovery-crash-imagep-implies-state` | unchanged, re-proved (first conjunct only) | inherits |
| 3 | `fn-sf-recovery-admissible-image-facts` | unchanged, re-proved. Clauses 1-4 (`fn-sf-statep`, `fn-record-uint32p`, `fn-sf-record-listp`, `true-listp`) are LIVE on the new arm and the record-list one is exactly what the gate buys. Clause 5 (an acknowledged pair names a record) is **vacuous on both rollback arms by their own gates** -- that vacuity IS K2r's content, so it is recorded here and not marked `unreachable-in-composition`: the ARM is reachable, the clause is trivially true there | `*fn-so-gap-opened*` at `(3, both records)`: `fn-record-uint32p 3` and the record list is ordered below 3 |
| 4 | `fn-sf-recovery-crash-image-extends-stable-records` | unchanged, re-proved; live on the new arm, where `records` is `(fn-sf-records s)` and the stable prefix is a prefix of it | `*fn-so-gap-opened*`: stable records are `(first)`, a proper prefix of the image's `(first second)` |

Conclusion-only, not premises: `fn-sf-crash-rollback-image-is-recovery-admissible`,
the new `fn-sf-crash-frontier-rollback-image-is-recovery-admissible`,
`fn-sf-crash-imagep-implies-recovery-crash-imagep` (still true: arms were only
added).

### `fn-sf-image-crash` -- DEFINITION changed (`if` to `cond`, third branch).

No theorem takes it as a premise. Three use it in a conclusion or by `:use`:
`fn-sf-recovery-crash-realizes-every-admissible-image`,
`fn-sf-image-crash-preserves-state` (re-proved with the third constructor),
`fn-sf-recovery-admissible-image-facts`. One `assert-event`
(`tests/acl2/store-observed-traces-tests.lisp:280`) still holds.

### `fn-bs-replay-matches-scan` / `fn-bs-store-relation` -- CLAUSE added.

`fn-bs-replay-matches-scan` has exactly one caller, the definition
`fn-bs-store-relation`. `fn-bs-store-relation` has **one** premise-taker in
the whole tree: `fn-bs-crash-image-transaction-names`
(`books/byte-store-scan.lisp:758`, `:rule-classes nil`), which is K1's
namespace clause. Verdict: **unchanged and still true, with the proof
unchanged** -- a conjunct added to a premise strengthens it, and the new
conjunct is simply unused there; re-certified in the wide run. K2 to K8 are
open, so there is no other consumer, and the two clauses are an obligation on
K0 rather than a theorem -- labelled so in the book, in §3.2 and in §7's K2
row. (`fn-bs-view-is-an-admissible-image` mentions the relation only in the
commented-out obligation text of `books/byte-store-invariants.lisp`.)

The enumeration also confirms the kernel lane's count for the untouched
predicate: `fn-sf-crash-imagep` has exactly eleven premise-takers (four in `bp-receiver-evolving-store-invariants`, one
in `owner-invariants`, three in `store-files-invariants`, one in
`store-node-traces`, two in `store-observed`) plus the `fn-own-reopen` gate.

### `fn-sf-crash-imagep` -- UNCHANGED, byte for byte.

The kernel lane's eleven premise-takers and its two definitions are untouched
in statement and in proof. They are re-certified in the wide run below; no
verdict of theirs changes, which is the point of not widening it.

## 4. Are K2, K3 and K4 earned?

**K2: no, and it is now waiting on ONE thing.** Its STATEMENT is true of every
image the platform can leave in the recovery window, which it was not before
this lane -- that is what K2f closes. The theorem is still unproved and what
it waits on is **K1's other three scan clauses** (the config entry, the
frontier entry and its content, and no `:fault`); the namespace clause
`w9/storage-3` closed. The byte-side clause this lane added to
`fn-bs-replay-matches-scan` is an obligation on K0, not a theorem, and is
labelled so in the book, in §3.2 and in §7.

**K3: its kernel half is proved and its byte half IS K2.**
`fn-sf-recovery-crash-realizes-every-admissible-image` now covers all four
arms with `fn-sf-image-crash` as the constructor. Given K2, K3 is that
theorem applied; it costs nothing beyond K2.

**K4: its kernel half is earned, its byte half is K2.** The two halves of
K4's conclusion, over the platform predicate rather than over a byte crash
image, are `fn-sn-recovery-admissible-image-reopens` (the reopen succeeds)
and `fn-sf-recovery-admissible-image-facts` clause 5 (an acknowledged pair
names a record of the image). Both are certified. K4 as §3.3 states it needs
`fn-bs-crash-imagep` in the premise, and getting from there to the kernel
premise is exactly K2.

## 5. What is open, with its checkpoint

* **K1's remaining three scan clauses**, in `books/byte-store-scan.lisp`.
  This is the single next packet for this cluster and everything above waits
  on it. The namespace clause and its four defects are in
  `planning/lanes/HANDOFF-w9-storage-3.md` §2 and §3.
* **K0**, which is what discharges the two clauses this lane added to
  `fn-bs-replay-matches-scan` -- the durable frontier is the scanned one
  minus one under a pending `:root` operation, and at most one authority
  directory has a pending entry operation in the window. Both are true of the
  host for reasons named in §1; neither is proved.
* **`fn-sf-crash-choicep` still has no rollback choice**, so a TRACE cannot
  reach the rolled-back states; only `fn-sn-open-observed` can. That is
  deliberate (D14-b, D14-c) and is why the witnesses below are all opened
  states rather than crashed ones.
* **The `(null x)` conclusion trap**, reported on the board: two exported
  theorems in `books/store-node-invariants.lisp`
  (`fn-snt-replayed-node-idle-and-frontier`,
  `fn-snt-prepared-durable-is-idle-at-successor`) have `(null ...)`
  conclusions and therefore contribute no rewrite rules. They are cited by
  `:use` everywhere they are needed, so nothing is broken; but a lint would
  be worth having and the tree has 391 `(null ` occurrences in `defthm`
  statements across 50 books.

## 6. Witnesses, one per conjunct of the new gate

All in `tests/acl2/store-observed-traces-tests.lisp`, beside D14-b's, and all
opened through `fn-sn-open-observed` -- the entry
`host/store-node-host.lisp:27` calls at every process start.

* **Reachable and non-degenerate**: `*fn-so-gap-opened*`, a process opened on
  a two-record image with frontier 4 and records at txids 0 and 2, so txid 3
  is reserved and unconsumed -- exactly the state `advance_frontier` leaves
  when its rename has not been fenced. `fn-sf-recovery-crash-imagep` admits
  `(3, both records)`, `fn-sf-crash-imagep` does not, and
  `fn-sf-crash-frontier-rollback` reproduces it exactly.
* **The RECORD-LIST conjunct**: `*fn-so-tight-opened*`, the same two records
  with frontier 3, so the reservation txid 2 HAS been consumed by
  `*fn-so-second*` and the rename that made frontier 3 durable is long past.
  The frontier arm is closed; **the record arm is still open there**, so the
  witness separates the two arms by more than their weakest clause.
* **The SUCCESS conjunct**: `*fn-so-reserved-crashed*`, which reserves txid 7
  and then crashes. Every other conjunct holds -- the record list IS below 7
  -- and the arm is still closed, because a crash from `:reserved` has
  observed `(:frontier-directory :ok)` and `fn-sf-crash` is what models it.
  The record arm is closed there too, for its own reason.
* **The PHASE conjunct**: `*fn-so-gap-ready*`, five barriers later.
* **The POSITIVITY conjunct**: `*fn-so-empty*` at frontier 0, where
  `(fn-sf-record-listp nil 0 0 -1)` is T -- so the record-list conjunct does
  not exclude it -- and `(fn-record-uint32p -1)` is not.
* **The EXCLUSIVITY conjunct**: `*fn-so-gap-opened*` at `(3, (first))`,
  refused. That `assert-event` was already in the book, written for D14-b
  with the comment "a rolled-back frontier is refused". K2f makes that
  reading wrong and **the comment is corrected in the same commit**; the line
  is now the exclusivity tooth.
* **Packet 2 at a ground state**: the rolled-back image still opens
  (`fn-sn-open-okp` of the reopen at frontier 3) and
  `fn-sf-history-recoverablep` holds of it, which is
  `fn-snt-history-recoverable-under-record-bound` evaluated.

## 7. Five proof-shape traps this lane paid for

The first four are about a rule the world does NOT hold although the theorem
is admitted, exported and counted; the way to catch them is to read the
`Rules:` list of the form that was supposed to use it.

* **A `(null x)` conclusion generates no rewrite rule.** ACL2 answers
  `Warning [Non-rec] ... The previously added rule NULL subsumes a newly
  proposed :REWRITE rule generated from <your theorem>, in the sense that the
  old rule rewrites a more general target`, and declines to store it. Five
  such warnings on one step lemma here; the induction that cited it then
  could not discharge its own step and the failure read as a missing
  induction hypothesis. Spell the conclusion `(equal x nil)`.
* **A `(<= a b)` conclusion becomes a `:rewrite` rule on the literal
  `(< b a)`**, which never appears in an arithmetic goal. That conjunct needs
  its own lemma with `:rule-classes :linear`. Split out here as
  `fn-snt-apply-record-from-idle-needs-its-txid`.
* **A `:forward-chaining` rule whose trigger only APPEARS once a predicate
  in the goal is opened never fires.** Forward chaining runs on a goal's
  hypotheses as they stand when the goal is created; `(fn-record-p (car
  records))` arrives during that goal's simplification, when
  `fn-sf-record-listp` opens, and by then forward chaining is done. The
  field-type rule sat in the world doing nothing through three
  certifications. It is `(:rewrite :forward-chaining)` now, and the forms
  that need it close `fn-record-txid` -- because the record vocabulary is
  open in that book, so an unclosed accessor has already become `(cadr
  record)` in the goal while the rule's left-hand side is stored in accessor
  vocabulary and no longer matches.
* **A `:rule-classes nil` theorem named in a THEORY EXPRESSION is a hard
  error**, not a no-op: `HARD ACL2 ERROR in
  SET-DIFFERENCE-CURRENT-THEORY-FN ... names a theorem but not any rules`,
  and the `defthm` aborts before any proof runs. Exact sibling of
  `w9/storage-3`'s constrained-function-in-a-theory finding.
* And one about induction shape: an ordered-list predicate whose `lower`
  argument the loop's induction does not move gives an induction hypothesis
  at the wrong bound. `fn-snt-txids-below` mentions only the bound, and
  carries the `natp` of each txid, because the contradiction that discharges
  the step is `txid < bound < txid+1` and linear arithmetic sees that only
  over integers.

## 8. Per-root certification

Laptop (Darwin 25.6.0, ACL2 8.7 at `/opt/homebrew/Cellar/acl2/8.7_6/bin/acl2`,
sha256 `36519682f97e83f1aadf9d092f46cb944d6621751595b8abf6b27b74309df324`),
one process at a time through `tools/certify_books.py`. Certificates in this
worktree came from `python3 tools/certs.py install` (`installed 0, kept
identical local 161, no cached pair 115`) and were rebuilt from
`books/store-files` up, because a certificate is not relocatable: the first
attempt failed with `its certificate requires the book
"/home/ember/fn-lanes/w10-dtn-3/books/store-files-invariants.lisp"`.

| root | state | evidence |
| --- | --- | --- |
| `books/store-files` | **certified** | `build/acl2/certify-20260921T010720Z-95694` (4.8 s) |
| `books/store-files-invariants` | **certified** | same run (10.4 s) |
| `books/store-node` | **certified** | same run (0.8 s) |
| `books/store-node-invariants` | **certified** | `build/acl2/certify-20260921T012714Z-28214` |
| `books/store-files-traces` | **certified** | `build/acl2/certify-20260921T012857Z-30559` (3.2 s) |
| `books/store-node-traces` | **certified** | same run (13.5 s) |
| `books/store-node-resolution` | **certified** | same run (3.3 s) |
| `books/store-observed` | **certified** | same run (3.0 s) |
| `books/store-observed-traces` | **certified** | same run (1.9 s) |
| `tests/acl2/store-observed-traces-tests` | **certified**, 137 of 137 `:PASSED` | `build/acl2/certify-20260921T012956Z-31806` |

`tools/teeth_check.py --evaluate` on the test book: **458 probes, prefix ok,
exit 0, 458 values, 0 findings**. It caught one defect before certification --
`fn-record-uint32p` was asserted FALSE once and TRUE nowhere
(`predicate-never-anchored`), so the positivity tooth had no anchor; there is
now an `(assert-event (fn-record-uint32p 3))` beside it.

Ledger, before this lane and after: `defthm` 5559 to 5580, `defun` 3929 to
3932, guard-verified 1461 to 1463, `assert-event` 5400 to 5436, SUSPECT 46 to
46. **The SUSPECT count did not move and that is not a virtue**: the one new
lemma that deserves the flag, `fn-sf-frontier-rollback-visiblep-unfolds`, was
flagged (47) while its conclusion spelled the emptiness conjunct exactly as
the definition does, and stopped being flagged when that conjunct became
`(equal (fn-sf-successes s) nil)` -- which it had to become, since a `(null
x)` conclusion generates no rule. The shape detector compares text; a
`-unfolds` lemma can slip past it by spelling one conjunct differently. Worth
a tooling fix, and the lemma is named honestly in the meantime.

## 9. The wide run

hbox, `run-20260921T013133Z-f968`, `tools/farm.py submit hbox --jobs 8
--remote-root /tank/fn/lanes/w11-bytestore-k2 --affected-by
books/store-files.lisp --closure`, ACL2 8.7 at `/tank/fn/acl2-8.7/saved_acl2`
sha256 `64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`,
through `swarm-build`. Evidence
`build/acl2/certify-20260921T013143Z-1403371` (fetched into this worktree).

**130 roots attempted, 129 certified, 1 failed**, 721.1 s of book wall time.
Cache on submit: `installed 74, kept 44, uncached 158`.

Box chosen by measurement, and the coordinator's correction applied: hbox is
a ZFS box, so `free`'s `used` counts the ARC and under-reports. Measured
before submitting: hbox load 1.26, `AnonPages` 2.5 G, `MemFree` 26 G against
`Slab` 90.7 G of which `SUnreclaim` 85.8 G is ARC; persvati load 3.47 with
61 G available and another lane on it. hbox at `--jobs 8` peaked at four
`sbcl` processes and 1.9 G RSS.

**The one failure is not this lane's, and the reason the previous lane gave
for it is wrong.** `tests/acl2/checkpoint-codec-tests` fails at
`(assert-event (not (fn-cpc-validp *cpc-value* *cpc-groups* 10 (list
*cpc-r0-bad-generation*))))`. `HANDOFF-w10-kernel-freedom.md` §5 says "its
include closure is `books/checkpoint-codec` alone, with no path to
`books/store-files`"; there IS a path -- `checkpoint-codec` includes
`checkpoint`, which includes `store-node-invariants`. The correct argument is
about definitions: `fn-cpc-validp` (`books/checkpoint-codec.lisp:1521`) is
`fn-checkpointp`, `fn-replay` and `fn-replay-okp` and nothing else, an
`assert-event` evaluates rather than rewrites, and **this lane changed no
definition those reach** -- its `books/store-node-invariants` edits are
theorems plus one `local` `defun`, and the two new functions in
`books/store-files` (`fn-sf-frontier-rollback-visiblep`,
`fn-sf-crash-frontier-rollback`) are not reachable from `fn-cpc-validp`. The
previous lane also measured the identical assertion failing under a different
kernel, in a different tree, in both of its runs.

**Everything else in the closure is green**, including the four roots that
were red for the kernel lane: `books/owner-invariants`, `books/owner-config`
and `tests/acl2/owner-tests` (166 of 166 `:PASSED`) all certify now that
`w11/owner-config` is on `dev`. **That closes the kernel lane's open item**:
the OWNER half of D14-b's counterexample, written but never run, is certified
in this tree. So is `books/byte-store-scan` with the new relation clause,
`books/bp-receiver-evolving-store-invariants` and its test book, and
`tests/acl2/store-files-tests`, `-teeth-tests` and `store-node-teeth-tests`.
