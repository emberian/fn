# w11/phantom-cites — the paths this tree cites and no file answers

Branch `w11/phantom-cites` from `dev` `1d2d49a`, `dev` `1e29d82` merged. Documentation-integrity lane:
no theorem, claim or assertion was weakened, deleted or proved. Nothing here
needed ACL2 and nothing here ran it.

## 1. The tool

`tools/cite_check.py`, with `tests/test_cite_check.py` (22 cases) and a line in
`make check` and in `make tooling-test`.

**Why not a `tools/ledger.py` lint.** The ledger's docstring promises that
reading a book cannot run a book, and a text scan keeps that promise, so that
argument does not decide it. Two others do. The ledger's subject is the
s-expressions of `books/`, `tests/acl2/` and the `ld`ed host files; more than
half of what a citation sweep must read — `specs/`, `docs/`, `planning/`,
`tools/`, the Makefile — the ledger never opens, and the citations that matter
live in the COMMENTS the ledger's reader skips. And `ledger.py --check` is a
gate that fails, while this answer is a count. `teeth_check.py`,
`transcribe_check.py` and `session_depth.py` are the precedent: one question,
one file, wired into `make check` beside the ledger.

**What it reports.** Every token shaped like a path into this repository, in
every tracked text file, that no file answers, split two ways:

* by citer — LOAD-BEARING (`books/`, `tests/acl2/`: a claim about evidence,
  made where a reader decides whether to trust a theorem), SPEC, TOOL,
  PLANNING;
* by history — PHANTOM (`git log --all` has never touched the path: there is
  nothing to point at) against DRIFT (it existed, or exists on another ref:
  the repair is a new path).

A third class, ANNOTATED, is a citation whose own prose says the file is not
there and what rests on it, or where it went. That disclosure is the repair
AGENTS.md asks for when there is nothing to point at, and it is counted, not
raised, so the number of disclosed gaps stays readable.

**The false positives it does not make**, each one a rule with a reason in the
source and a case in the tests: an ACL2 community book (`books/` here is FLAT,
so `books/arithmetic/top.lisp` is ACL2's tree, and an `include-book ... :dir
:system` is too); a placeholder (`books/X.lisp`, `tests/acl2/*-teeth-tests.lisp`,
a one-character stem); the Makefile's extensionless spelling of a book; a
`.cert` or `.log` a run produces; a module attribute (`tools/scheduler.plan_from`);
a hyphenated line wrap; an undelimited slash in running prose (`host/grammar
work`, `planning/structural checks` — an extensionless citation must be in
backticks or quotes, and `` `books/nntp-probe` `` is); the fixture data of
`tests/test_*.py`, which name files in a `TemporaryDirectory` (their COMMENT
lines are still read); and `tests/evidence/`, `planning/evidence/`, whose
records name what was certified THEN and must keep naming it.

A fourth, CATALOGUE, is the three files whose subject is absent paths — this
checker, its tests and this triage. They name paths that are not there on
purpose, and counting them would make the tree's number a measure of how much
has been written about the tree's number. The control: the tree's number is
**identical before and after those three files were tracked**.

**Counts on this tree after the repairs below** (`python3 tools/cite_check.py`):

    67 citations of 43 absent paths (52 phantom, 15 drift); by citer:
    0 load-bearing, 35 spec, 1 tool, 31 planning; 32 annotated, 115
    catalogue, 245 placeholder, 1 wrapped, 33 prose, 14 system, 234
    fixture, 115 record not raised.

(On `dev` `1d2d49a` alone it was 74 of 46, with 26 drift and 0 tool. Merging
`dev` `1e29d82` landed `tools/v0_matrix.py` and `planning/v0-matrix.json`, so
eleven of the board's drift citations resolved; the one tool-tier line left is
`tools/run_owner.py:282` citing `planning/evidence/v0-matrix-2026-09-20.md`,
which is DRIFT on the unmerged `w10/v0-matrix` and is not this lane's.)

`make check` runs `--summary --strict`, so a NEW undisclosed load-bearing
phantom fails it. The other three tiers are reported and do not.

**What it cannot see** is in the tool's docstring and is the part to read
before acting on any line of its output. The four that bit this triage:
it checks that a path exists, never that the file says what the citation says
it says; PHANTOM is a fact about the path, not about the work (`books/tcpcl.lisp`
was a phantom while the convergence layer it names was certified under four
other names); it does not read `build/`, because a lane worktree is not a
repository path; and ANNOTATED is a regex over prose, so it is a convention
held by review rather than a proof — which is why its count is printed.

## 2. The load-bearing findings, each named

Five, before repair. Three were already annotated by w11/node-index.

1. **`books/store-node-resolution-traces.lisp`, cited by `books/assumptions.lisp:62`
   — DRIFT. REPAIRED.** This is the one that mattered most: `books/assumptions.lisp`
   is where fn's named assumptions live. A-DURABILITY's comment lists the
   theorems that should take it as a hypothesis, and the fifth,
   `fn-snrt-acknowledged-history-retained-through-mixed-trace`, was cited to a
   book that `8209f27` deleted ("store-node-resolution-traces is folded into
   store-node-resolution"). The theorem is at
   `books/store-node-resolution.lisp:392` and the citation now says so, with the
   commit that moved it. Two evidence records still name the old path and
   correctly so.
   **What this is NOT.** A-DURABILITY is not prose: it is an `encapsulate` with
   a local witness and two constraints at `books/assumptions.lisp:68`, and the
   theorem it cites exists. See the ASK in §5 for what IS open.
2. **`books/stx-transit.lisp`, cited by `books/stx-lace.lisp:148` and
   `books/stx-policy.lisp:36` — PHANTOM. Already annotated** (w11/node-index,
   2026-09-21). No ref has ever held it. Left as it stands; the tool now reads
   both annotations and classes them ANNOTATED.
3. **`tests/acl2/stx-lace-tests.lisp`, cited by `books/stx-lace.lisp:150` —
   PHANTOM. Already annotated.** Same.
4. **`tests/bp-dtn7/golden/`, cited by `tests/acl2/bp-bundle-tests.lisp:9` —
   PHANTOM. NEW; ANNOTATED, and it is an ASK.** The header says the book's
   external vector "is a bundle dtn7-rs 0.21.0 authored and fn received over
   the certified TCPCLv4 layer", that `tests/bp-dtn7/golden/` "holds the
   capture and the run that produced it", and that "the octets are inlined
   below". The directory was written into that header by `a437c32`, the commit
   that created the book, has never existed on any ref, and is named nowhere
   else in the tree. **And no octets are inlined.** Every vector in the book —
   `*bpb-primary*`, `*bpb-bundle*`, `*bpb-bundle-nocrc*`, the three teeth
   bundles, `*bpb-full*` — is built by fn's own constructors and checked by
   round trip through fn's own `fn-bpb-encode`/`fn-bpb-decode`. A round trip of
   fn against fn is a self-consistency check of the codec; it cannot fail on a
   disagreement with dtn7-rs, because no dtn7-rs octets are there to disagree
   with. So "interoperability vectors" in line 1 of that book rests on nothing
   in it. The claim is not deleted: the header now records what is missing and
   what rests on it, and §5 hands the gap to the BP cluster.

Nothing else in `books/` or `tests/acl2/` cites an absent path: the only other
finding from a source is `books/arithmetic/top.lisp` at
`books/injection-invariants.lisp:360`, which is ACL2's own book.

## 3. Triage of the rest: phantom, drift, forward-looking

**SPEC (35 citations, 25 distinct paths).** Almost all forward-looking, and
the packet tables of the designs are where they live. Not defects; the reading
each needs is whether the packet is still owed.

* Deliberately future, packet rows: `books/bpsec(.lisp)`, `books/ltp(.lisp)`
  and `host/native/ltp.lisp` (bp-design packets 8, 9); `books/dtn-channel.lisp`,
  `books/system.lisp`, `books/ideal-node(.lisp)`, `books/ideal-node-host.lisp`,
  `tests/acl2/ideal-node-tests.lisp`, `tests/acl2/ideal-node-guards-tests.lisp`
  (node-functionality P0–P5); `books/feed.lisp`, `host/feed-host.lisp`,
  `books/peer.lisp`, `tests/acl2/peer-tests.lisp` (peering K1, K2);
  `books/bp-receiver-history-invariants.lisp`,
  `books/bp-receiver-store-evolution-invariants.lisp` (bp-evolving-store);
  `books/byte-store-frame.lisp` (crash-model-v2 P4); `books/contact-config.lisp`
  (reconfiguration R7, also BOARD:402); `tests/acl2/reader-fixture.lisp`
  (reconfiguration); `tools/run_container.py` (container, marked "proposed");
  `tools/run_transfer.py` (transfer-journal, marked "proposed", and the spec
  already says its registry rows stay candidates until it exists).
* **Renamed, and now annotated:** `books/statement-field.lisp` and
  `books/statement-transit.lisp` in `specs/substrate-transport.md`. The design's
  names; the cluster landed as `books/stx-*`. §2.1 of that spec already recorded
  it for S3; this lane added the same record under the packet table for S1 and
  S2. Which landed book answers which row is for the substrate cluster.
* **Renamed, and REPAIRED:** `books/tcpcl.lisp` and `books/tcpcl` in
  `specs/bp-design.md` §2 and packet row 4 now name `books/tcpcl-octets.lisp`,
  `books/tcpcl-records.lisp`, `books/tcpcl-session.lisp` and
  `books/tcpcl-invariants.lisp`, which exist, with a line saying the single
  book of that name never did.
* **Landed without its spec — an ASK, §5:** `specs/bp-bundle.md` and
  `specs/bp-node.md`, named as deliverables of bp-design packets 0 and 3.
  `books/bp-bundle.lisp` and `books/bp-node.lisp` exist and certify; the two
  spec files never have. `books/bp-node-records` (bp-design row 1) is the same
  shape: the FNBS replay book is not there under that name.

**PLANNING (39 citations, 20 distinct paths).** Stale handoffs, and one class
that is not stale at all.

* Correct as written, do not "fix": `host/books/anchor-invariants.lisp`
  (`HANDOFF-w3-time-anchor.md:117`) narrates the path ACL2 wrongly resolved to,
  which is the defect the lane fixed; `books/nntp-probe`
  (`planning/deputies/nntp.md:34`) names a scratch book that lane certified and
  did not commit; `host/store-config.lisp` (twins handoffs) is quoted as the
  name the packet used and the lane rejected.
* Unmerged lane work, not absent work: `tools/v0_matrix.py` (10 citations),
  `planning/v0-matrix.json`, `planning/evidence/v0-matrix-2026-09-2{0,1}.md`,
  `planning/lanes/HANDOFF-w11-harness-health.md`. All DRIFT — they exist on
  `w10/v0-matrix` and `w11/harness-health`. The board says so itself. They
  resolve when those lanes merge.
* Historical lane dumps, left alone: the four `tests/acl2/*-teeth-tests.lisp`
  of `LANEDUMP-assurance-tooling.md` and the two
  `books/store-node-resolution-traces` of `LANEDUMP-crash-fidelity.md` are
  DRIFT — those files existed when the dump was written. A LANEDUMP is a record
  of a session, like an evidence file; rewriting one to match today's tree
  falsifies it. Same for `tests/acl2/acceptance-guards-tests.lisp`
  (`HANDOFF-w2-bp-guards.md`) and `books/certify-wire.log`.
* Genuinely stale, low value: `tests/evidence/2026-09-19-wave1.md`
  (`handoff-to-codex-2026-09-19.md:57` asked for it; `2026-09-19-wave1a.md` and
  `-wave1b.md` were written instead), `books/tcpcl.lisp`
  (`DESIGN-bp-summary.md:37`), `tools/run_container.py`, `tools/run_transfer.py`.

**TOOL (0 after repair).** `docs/trust-boundary.md` was the only one: see §4.

**Not raised, and each was on the crude sweep's list.** `tools/run_peer.py`
(`tests/test_feed.py:89`, `tests/test_twonode_gate.py:36`) is CORRECT: both
tests run `tests/twonode_gate_fake/tools/run_peer.py`, which exists, copied
into or named relative to a fixture tree; `tests/test_feed.py`'s own docstring
says so. `host/host/native/io.lisp` is not a doubled prefix anywhere: the tree
has `build/lanes/w3-native-host/host/native/io.lisp` twice
(`specs/bp-design.md:809`, `HANDOFF-w4-tcpcl.md:138`), a path into an
uncommitted lane worktree, which the tool deliberately does not read.
`books/arithmetic/top.lisp` (three citers) is ACL2's own book. The four
`tests/acl2/*-teeth-tests.lisp` of the LANEDUMP are DRIFT and are records.

## 4. What was repaired

| File | What | Class |
| --- | --- | --- |
| `books/assumptions.lisp:62` | `store-node-resolution-traces.lisp` → `store-node-resolution.lisp:392`, with the folding commit | drift |
| `tests/acl2/bp-bundle-tests.lisp:6` | annotation: the directory never existed, no octets are inlined, what rests on it | phantom |
| `tools/run_owner.py:649` | `docs/trust-boundary.md` → `specs/nntp.md` "Transport security, and what is trusted" | phantom |
| `specs/bp-design.md:616,957` | `books/tcpcl.lisp` → the four books that exist | drift |
| `specs/substrate-transport.md:881` | annotation under the packet table: the S1/S2 book names never existed; the cluster is `books/stx-*` | phantom |
| `Makefile` | `cite_check.py --summary --strict` in `check`; `tests.test_cite_check` in `tooling-test` | — |

**`docs/trust-boundary.md` should NOT be created, and this lane did not stub
it.** Two places cite it: `tools/run_owner.py` and
`planning/evidence/auth-w10-2026-09-20.md`, both for "TLS is outside the
model". That boundary IS recorded, twice: `specs/nntp.md` § "Transport
security, and what is trusted" states it, and `specs/nntp-audit.md` §2.3's row
points at it; the native host's raw surface has its own in `specs/host.md`
§ "Trust boundary of the native host". A third document restating them is the
twin AGENTS.md tells us to delete, and AGENTS.md's "isolate and document it in
the trust boundary" is satisfied per subsystem. The code citation is repaired
to name the real section. **The evidence record is not touched** — an evidence
file records what a run's author wrote and is not edited to match a later tree
— so one citation of `docs/trust-boundary.md` remains, in the `record` class,
by design. If the project ever does want ONE index, it is a docs/ owner's
decision and it should link, not restate.

## 5. Handed to owners

**ASK → store cluster (`books/assumptions.lisp`).** The citation is repaired,
and the gap under it is not. A-DURABILITY is a real constrained function —

    (encapsulate (((fn-assume-durability-image * *) => *))
      (local (defun fn-assume-durability-image (barriered unbarriered) ...))
      (defthm fn-assume-durability-retains-barriered ...)
      (defthm fn-assume-durability-invents-nothing ... :rule-classes nil))

— but **no theorem outside that book mentions it.** `grep -rn fn-assume-
books tests host` finds `fn-assume-fairness-*` in `books/scheduler-invariants.lisp`,
`fn-assume-peer-*` and `fn-assume-policy-*` in `books/bp-release-invariants.lisp`,
`fn-assume-physical-crash` and `fn-assume-crash-tearp` in
`books/byte-store-invariants.lisp`, and **nothing for A-DURABILITY**. The five
theorems its comment names, including
`fn-snrt-acknowledged-history-retained-through-mixed-trace`
(`books/store-node-resolution.lisp:392`) and `fn-sf-crash-preserves-state`
(`books/store-files.lisp`), take no such hypothesis; durability is built into
`fn-sf-crash` instead, which is review finding D5. The book says so itself
("it does not yet discharge or apply them. That is C1-14 and C1-15 work"), so
this is not a new defect — it is a recorded one whose citation had rotted, and
the ask is only that C1-14/C1-15 be carried as the store cluster's, with the
repaired line as the map. Exact form: make
`fn-assume-durability-image` the crash image in the hypothesis of
`fn-snrt-acknowledged-history-retained-through-mixed-trace` and of
`fn-sf-stable-records-prefix-of-crash`, rather than `fn-sf-crash`'s built-in
one, and `:functional-instance` the platform profile onto them.

**ASK → BP cluster (successor of w9/dtn-2).** `tests/acl2/bp-bundle-tests.lisp`
calls itself "interoperability vectors" and has none. Either supply a captured
dtn7-rs 0.21.0 bundle — the octets, and the record of the run that captured
them, in `tests/evidence/` where `2026-09-18-bpv7-transport.md` already lives —
and assert that `fn-bpb-decode` accepts THOSE octets and reproduces them; or
walk the header's claim back to what the book proves, which is that fn's codec
round-trips fn's own values. Do not resolve it by deleting the sentence.

**NOTE → BP cluster.** `specs/bp-design.md` packets 0 and 3 name
`specs/bp-bundle.md` and `specs/bp-node.md` as deliverables. The books landed;
the two spec files have never existed. Row 1 names `books/bp-node-records`,
which has never existed either.

**NOTE → substrate cluster.** The S1/S2/S3 rows of
`specs/substrate-transport.md` name `books/statement-field.lisp` and
`books/statement-transit.lisp`. Neither has ever existed; eight `books/stx-*`
books did land. The row-to-book mapping is yours to write.

## 6. What this lane did not do

It did not create a file to satisfy a citation, delete a claim to make one go
away, touch an evidence record, prove anything, or run ACL2. It did not repair
the planning tier beyond naming it: 39 citations there are stale handoffs and
lane dumps, and a dump is a record.
