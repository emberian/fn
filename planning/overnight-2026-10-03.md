# Overnight execution plan — 2026-10-03

Prepared by Codex after source inspection and two GPT-6-Astra design reviews,
two GPT-6.1-Sol deputy investigations, and a GPT-6-Luna task-scoping pilot.
This is the dispatch plan; the repair ledger remains the only task queue.
It supersedes the old roster, timing estimates and revert-on-red instructions
in the earlier October plan. The architectural destination is unchanged.

## Starting point and what is actually unfinished

- Remote `dev`: `9af0cd1a9c5a7b6f9106c72d8312c04f0405b9fa`, verified against
  origin. The shared checkout was `31d645af9`; `origin/next` was `a35902812`.
  Both are stale starting points for new lanes. Re-anchor the train to current
  dev by an ordinary fast-forward/merge, with no reset or force push.
- Before reconciliation: 259 repair items: 108 open, 52 in-progress, 69 ready,
  13 landed, 2 refuted, 10 duplicate, 5 deferred. Most READY source is already
  on dev. All 69 were reconciled to source-landed by exact ancestor receipts
  (67 explicit SHAs, two SHAs recovered from item notes). Five newly scoped
  issues are now recorded: 264 total, 113 open, 52 in-progress, zero ready,
  82 source-landed. Source landing does not establish native/proof completion.
- Existing native run `ov1` builds source `4671ace0f` (BM10); the only later
  change at `9af0cd1a9` is the BM10 ledger receipt. Its image-root certification
  passed (32 passed, zero failed; `certify-20261003T043548Z-620519`). At this
  inspection it was still in host loading: no image/native verdict exists.
  Harvest it; do not launch a duplicate build. Cite the built source, not the
  later ledger-only SHA. Do not label known OVER failures as a green suite.
- Last handoff image set: `45e05c7fdfcd4f34539b45c241ec217acdd8d3c1` on hbox.
  This is a fallback, not qualification of current source. Deployment was
  not inspected or changed during this orientation.
- Unmerged: served-live `7b9ffe475`, post-guard-off `812082a53`, wrapper
  `4e0e11c78`, burndown-3 `2f7f5bda2`. Their worktrees were clean. The carrier
  transformation `fa32ac06f` is a broken draft, not a candidate to merge.
- Served-live fast checks: 12/13, new R1 at owner.lisp:6090. Source tracing
  reaches the existing publication worker's off-section `fnn-live-arena`
  access through the new maintenance path. Do not wrap the whole maintenance
  tick in a lock: its callees already have sections, and I/O stays outside.
  Capture a protected arena/root capability at the proper boundary and pass
  it to the worker, or defer that independent slice while retaining its code.
- Wrapper's old farm run `run-20261003T041004Z-fe23` finished with 561 passed,
  11 failed. These harvested manifests are not yet in dev's evidence index;
  archive/index before claiming filed evidence. The changed failure-scope
  book passed at matching bytes; old
  BM09/BM10 failures elsewhere prevent a whole-run green claim.
- Burndown-3 already contains CL08/09, BM08/CL20, CL10, CL12 and CL11 work.
  Read its verification, including the base failure reason, before redispatch.

## Team and decision ownership

Start implementation with six active agents including the coordinator; expand
only when reviewed packets and independent files justify it. Maximum eight.
The completed orientation used two Astra, two Sol and one Luna plus coordinator.
These investigators have finished; the implementation roster below is the
prepared dispatch setup, not a claim that overnight workers are running.

| Role | Model | Owned work and boundary |
|---|---|---|
| Coordinator | this session | Priorities, shared contracts, conflict resolution, durable plan; no second integration lane |
| Integration deputy | GPT-6.1-Sol | Sole writer to next/dev; run harvest, ledger reconciliation, validation tooling, evidence and batch images |
| Host deputy | GPT-6.1-Sol | Wrapper, lifecycle pilot, safe carrier preparation; sequences these rather than opening three overlapping edits |
| Served deputy | GPT-6.1-Sol | Served-live, POST bridge, cursor/view/reclaim integration; sole assembler of its owner/mux changes |
| Tooling worker | GPT-6-Luna | First narrow gate/test packet, then another only after review/landing |
| Test/repair worker | GPT-6-Luna | Independent executable regression or agreed small native repair |
| Optional worker | GPT-6-Luna | Added after two useful landed pilot results and no review backlog |
| Design consultant | GPT-6-Astra | Time-bounded contract/design question; retires after decision and first-slice review |

Sol deputies own engineering decisions and reviews. Astra settles the cursor
ownership contract, lifecycle/primitive schema, carrier boundary and unresolved
cross-model disagreements. Do not keep two expensive design lanes continuously
surveying the repository. Do not ask Luna to independently redesign persistence,
locks, raw dispatch, or proof statements. A small generator edit can be a later
Luna packet after Sol fixes the contract and owns ACL2 admission/proofs.

Each packet names its ledger IDs, pinned base, owned files, actual callers,
expected behavior, forbidden changes, smallest refuting check, dependencies and
reviewer. WIP limit two, counting unlanded work. No autonomous child swarms.
Shared owner.lisp/mux.lisp/extent.lisp edits require an agreed assembler; this is
coordination, not an excuse to freeze independent work.

## First wave: recover work and remove blockers

1. **Integrator:** harvest ov1 and other named runs, reconcile source/evidence
   coordinates, re-anchor next, and inspect burndown-3 before merging its small
   slices. Preserve all partial residuals. Harden repair verification before
   renewed Luna `verify ok` claims (NIGHT-VERIFY). The current verifier permits
   no test and treats a missing module or any base failure as a defect witness.
   Also make filtering explicit: `--open` includes deferred and missing fields
   currently pass filters. Do not use an imaginary suitability tag.
2. **Served deputy:** NEWNEWS metadata arm + actual command declaration;
   per-command dependency deadline; S145 feed condition variable. Repair F8's
   concrete ownership boundary. F7 cold-off-loop comes last, with its slow-disk,
   lifecycle, owner, cursor, peering, temporary-feed and checkpoint regressions.
   A deadline is containment; `sl-cold-line-quanta` remains open.
3. **Host deputy:** complete WR01 and the existing wrapper's generated interface
   and native evidence, then convert mux as one bounded enclave. Do not open
   103 conversions at once. Coordinate the mux base with the served deputy.
4. **POST bridge:** served deputy owns code and measurements for the seven raw entries;
   integration owns batch validation, evidence and landing. Install them
   after final-world writer enumeration. Keep `A-OWNER-INVARIANT-CARRIED` and
   owed writers visible. Compare raw/counterpart transcripts and cost in the
   same image, including since-open 30/200/1000 and reopened 10k/100k fixtures.
   PGO-REFUSE-ABORT stays explicit. This is assumption-backed performance
   work, not completed invariant assurance.
5. **Luna pilots:** begin with S141's duplicate-load gate residual (new duplicate
   fixture must fail with both locations), then an executable S092 TLS-condition
   regression. S107 credential-FIFO and S100 trace-ownership repairs are next
   candidates only after Sol reviews exact effect ordering and file overlap.
   S107 shares feed-service with served-live and must wait for its landing.

## Second wave: build one reusable path at a time

### Served work and macros

The chosen store-file direction is carried dispatch, not an overnight rewrite
of invalid-state semantics across store-files' refinement closure. The `mbe`
idiom is not intrinsically wrong; repeated whole-invariant checks at the host
boundary are the cost defect. Finish the carrier and preservation boundary.

GEN-CURSOR's first installed consumer is metadata-only NEWNEWS. Generate cursor
validity/preservation, residual-response equality, visit and working/output-byte
bounds, productive progress (including no matches), dependency suspension and
settlement. Capture one completed discovery/config/root view for the response.
Reuse existing OVER/NEWNEWS lemmas, but inspect the host rerun path too.

A quantum of fewer than eight rows does NOT cure a shared eight-entry cache:
other operations can evict entries and one row can span multiple entries.
Persist scanning/formatting progress or own the funded dependency until consumed.
Cache warmth cannot be a termination premise. HDR/XPAT are the next cold-data
consumer; the deadline bridge remains until that actual consumer works.

Acceptance: >8 candidates, sparse results, concurrent cache churn and readers,
partial writes, cancellation/late physical completion, and faults before/after
multiline output starts. Never append a successful terminator after omitted rows.

SCL2/S042: exact available count, actual first/last, allocation watermark separate.
Fixture preserving articles 1 and 34 answers `211 2 1 34`; empty availability
answers `211 0 watermark+1 watermark`. Establish carried summaries during rebuild;
reclaim must invalidate them even if an article-count/version key is unchanged.
GROUP/LISTGROUP/NEXT/LAST/OVER move together.

DC05/SCL4: keep the settled discovery policy. LIST-family and NEWNEWS use one
completed snapshot without changing the connection pin; Message-ID lookup tries
the pin then completed view; restricted routes retain their reference path until
refined. DATE clock freshness alone does not establish discovery publication order.

DE-R2: repair lambda application reconstruction and propagation of unresolved
callee costs before broader rollout (NIGHT-COST-LAMBDA / NIGHT-COST-UNKNOWN).
The former may become an exact Luna fixture/implementation packet; Sol owns
admission and both fixes' semantic review. Unknown costs must remain unknown.
One installed `fn-reader-chunk` cost row precedes a larger generator rollout.

### Host coordination and carrier

The wrapper is an actual reusable section envelope, not yet a general actor
interpreter. Next pilot: one publisher/export worker family's registration and
join handling. This host lifecycle pilot may ship before the carrier because it
introduces no concurrent ACL2 stobj or new raw-dispatch claim.

First fix the prototype's join contract (NIGHT-ACTOR-JOIN): a failed/timed-out
join does not prove physical termination and must not discharge registration.
Reserve worker identity before spawn or use a start latch; a child can exit
before `make-thread` returns. Acceptance schedules: early child exit, failed
spawn, held final cleanup during stop, failed join with live child, duplicate
receipt, stop then uncertain completion, and offer versus closed inbox in both
orders. Exactly one owner retains each fd/receipt.

Do not run carrier `redo.sh` as handed off: it discards all tracked modifications
and deletes its output book. NIGHT-CARRIER-REPLAY replaces it with a fail-closed
isolated transformation, correct packaged imports, source-bound signatures,
`:instance` substitution handling and explicit parse failures. Fixture work is
Luna-suitable only after Sol fixes the expected transformation. Apply the complete
move to one frozen integration candidate; never land the half-transformed tree.

A served ACL2 coordination actor waits for safe private state, catch context,
shared-owner representation/dispatch, and the primitive interpreter. Forbid
thread-unsafe hons/memoize and unsafe `:protect` exports; a condition in a step
faults that actor, never reruns torn state. Pure/shadow step books can land earlier
with their unserved status explicit. The committer remains the first full actor.

Use one action vocabulary to generate primitive dispatch, host-model labels and
checker metadata. HM02 is not near-complete merely because its WIP is 1,779 lines:
all-schedules keystones are absent and the test is initialization only. Seeded
checker JSON is not consumption of the HM table. Funded issue/settle requires its
own modeled transition or real bridge to the direct transition. Start with
issue/cancel/retire/refused-close/late-complete/settle/close schedules and fd reuse.

## Validation, integration and resource controls

Behavior-first is ember's explicit direction (recovered from the October 2
conversation): native behavior and REPL feedback lead; skipped proofs become
`category=proof-owed` items naming exact subjects/theorems. No skip-proofs,
assumption laundering, or false green. Runtime ownership/durability preconditions
are implementation requirements, not proof debt that can be waved away.

The integration deputy fixes forward on next. New findings remain visible and
block the affected claim/candidate, not unrelated lanes. No revert-for-green and
no baseline increase to absorb served-live R1. Source integration, behavioral
verification, proof, image qualification and deployment remain separate fields.
A source-landed ledger receipt never closes its unverified native/proof remainder.

Each check has one owner. Lanes run the narrow refuting test and affected book
roots; reviewers read evidence and only add a missing discriminating check. One
combined native/image run covers a frozen batch. Host/served deputies obtain
their native evidence through that candidate where possible, rather than
launching duplicate image builds. Changed image book closure can
require native testing even if no host Lisp changed. Never use lane `--closure`.
Do not repeatedly certify the entire tree to discover the next obvious error.

Use both boxes (`--box auto`/`--host auto`); published-set runs require hbox.
Start with at most two box jobs across the project, using both boxes. Existing
`ov1` already consumes the heavy slot and schedules three 24 GB native scopes;
account for those before admitting another memory-heavy task. The integrator
adjusts only from RSS/ARC and observed throughput, not a per-lane multiplication.
Every hbox build uses swarm-build; laptop ACL2 uses the slot-controlled tools.
Inspection measured the shared repository at 14 GB against the 30 GB ceiling.
Do not delete another session's worktree/cache to make room.

A Luna implementation packet uses claim/verify after NIGHT-VERIFY: same runnable
regression on base and head, named expected assertion at base, actual pass at
head, no skips/missing modules/infrastructure failure counted as red. Record
native module needs. Scope expansion or two unsuccessful approaches goes to the
Sol deputy with the minimal reproducer, not a larger patch or more subagents.
The first read-only Luna pilot correctly rejected risky tasks but selected CL08
despite its already-fixed unmerged branch being explicitly excluded. This does
not measure coding ability; it does show that queue reconciliation must stay with
Sol. Supply pre-scoped packets rather than an open-ended burn-down instruction.
After two landed packets, compare useful output and review/rework cost; add the
third Luna only if that improves throughput. Stop dispatch when review WIP is full.

## Completion targets and the retained queue

First overnight target: an integrated runnable candidate, served hang containment
and NEWNEWS fix, wrapper first enclave, measured POST bridge, reliable small-task
verification, and two genuinely completed Luna packets. Next target: installed
NEWNEWS cursor and one lifecycle pilot. These are checkpoints, not a promise to
finish the actor conversion or the entire queue in one night.

Preserve the rest as the owning lanes' next packets: arena-forget's eight named
requirements and all roots; holder/read leases; atomic init and stranded-2/3
bounded journal/barrier/control-capacity/reclaim-note work; ION X10A/X10B; peer
round bounds; web face on I/O loops; accounting/resource vectors and store pages;
recovery/retire composition; raw trap redesign; carried-view/teeth/command macros;
X17 incremental checks; historical branch mining; X13 assurance catch-up. A
DISSOLVES-IN item closes only when its scenario passes on its replacement.

The old dirty transfer-closeout worktree is preserved. Most hints already landed;
its remaining counted-queue observer hint belongs in the assurance packet, with
historical manifest `certify-20261002T202018Z-898247` retained and no green verdict
transferred to changed dependencies. Regenerate its old planning edits on the
current tree rather than copying them wholesale.

End-of-effort report: integrated SHAs, observed behavior, exact failed/pending
checks, proof owed, remaining packet ownership, image identity and deployment
status. No release claim, live-node redeploy, edge-Caddy change, branch deletion
or outward message is part of this plan. Those are separate actions with their
own user intent; the rest of the engineering queue needs no repeated permission.
