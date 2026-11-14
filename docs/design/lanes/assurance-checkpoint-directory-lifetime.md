# Commit directory lifetime — current headroom and mapped-consumer inventory

The current directory still uses positive absolute batch numbers as physical row
indices, with row0 reserved for frontiers and control. This milestone changes no
layout and activates no reuse. A larger row/default count is not the solution.

## Shared actual headroom

`fn2-commit-directory-headroom(needed, fn2-commit-root)` is a B helper in
machines-b.lisp. It returns `(mv status available)`: :ok when the nonnegative
additional batch demand fits, :no-space when it does not, :state/0 for malformed
demand, no metadata row, or invalid frontier ordering/range. For a valid current
representation, `available = (rows - 1) - proposed`, with
`published <= installed <= proposed <= rows - 1`. Zero demand can fit zero room.
Already-proposed in-flight rows consume credit. Publication lag, pending aborts,
future checkpoint completion and hypothetical reclamation create no credit.

The existing C `fn2-checkpoint-directory-roomp` delegates its explicitly named
safe physical-geometry maintenance budget to this helper. Its actual HELD caller
now supplies the declared two arguments; the stale third boot-config argument is
removed. The boot-layout guard remains separate. The pressure caller already
uses the same predicate. Capacity owner will replace its existing hint-gated trigger and
combine exact candidate/extent/pool demand with this shared API; this helper does
not reserve rows or promise future progress.

Prepared source controls cover the whole valid-frontier positive case, exact
fit, insufficient credit hidden by publication lag, the actual C room predicate,
zero demand at full occupancy, malformed demand and unordered frontiers. The
published/proposed hypothesis-removal control demonstrates the old overcount.
No ACL2 fixture, admission, guard proof or certification has been executed.

## Proposed representation, not active code

Keep absolute wire batch/event/parent identities and row0 frontiers. A resident
ring would use `1 + mod(batch - 1, rows - 1)` plus an exact stored batch tag;
return :resident/:base/:archived/:absent rather than aliasing an old identity.
The seal digest directory must use the same mapping. Row0 must own the immutable
base boundary batch/event/seal so the immediate successor can authenticate its
predecessor after that batch's resident row is gone.

A bounded one-batch rebase would target an actual covering published descriptor
cut P, not its later installation commit. Whole rebase completion is a barrier
before another C proof build. It must account for both selectable banks' exact
owned installation evidence and active continuation allocation identities, not
only a numeric cutoff. Candidate owner is designing bank evidence independent
of resident rows; restore owner is designing authenticated prior role3/4 prefix
sources. Neither dependency is established by this headroom change.

## Actual consumer inventory

| Files/functions | Present dependency | Required mapped/prefix behavior |
|---|---|---|
| machines-b.lisp: root declaration/init, digest sizing and new headroom | Row0 plus E positive absolute rows; digest region also E+1 | Tagged resident rows, boundary state and exact logical lookup; retain geometry-derived capacity |
| commit.lisp: frontier/start, prepare-root, root-grow, mark-abort | Absolute row capacity and per-batch recipe/event cells | Claim/check matching tag before write; same absolute sequence; no reuse of active proposed rows |
| commit.lisp: seal-context | Digest base+batch and base+(batch-1), seal-ready at those IDs | Mapped digest rows, exact tagged predecessor or owned base seal; no stale digest alias |
| commit.lisp: root-swap, end-abort | Row0 absolute frontiers and abort restoration | Keep absolute ordering; rollback cannot cross archived base or clear a different tagged batch |
| commit.lisp: unprepare, notification-range | Clear batch seal-ready; read published batch event span | Exact mapped tag; archived notification range must route to authenticated history, not silently become no debt |
| retirement-coordinator.lisp: actual persisted lifecycle-step | Installed frontier equality to containing batch | Absolute control identity stays; resident member/workspace/effect evidence must survive continuation |
| commit-arms.lisp | Declared state/effect footprints and actual publish/drain sequence | Widen only real new state dependencies; preserve lifecycle-before-publication/ACK and exact drain ordering |
| checkpoint-installed.lisp: installation-seal-row | Absolute installation row and digest | Current resident lookup or actual bank/candidate-owned installation seal; no ID-order forgetting |
| checkpoint-writer-ops.lisp; checkpoint-writer.lisp | Publication/checker calls installation-seal-row | Bind exact candidate/bank evidence sourced at checked publication, including after directory reuse |
| c-snapshot.lisp; checkpoint-plan.lisp | Row0 equality of proposed/installed/published and cut event | Absolute frontiers unchanged; pin immutable source boundary for the whole job |
| checkpoint-master-abort.lisp; checkpoint-master-control.lisp | Admission/pressure directory budget | Shared actual headroom; no duplicate row arithmetic or stale freed-credit hints |
| event-proof-source.lisp: proof-pack-entry | Enumerates commit=ordinal+1 through cut; reads current/prior row event spans, seal and installed-root edge | Authenticated prior checkpoint role3 entries1..P, then exact mapped resident suffix P+1..cut |
| event-read-source.lisp: event-read-open | Fabricates entry from resident directory before admitting pinned read | Admit exact authenticated prefix entry or mapped resident entry; no fabricated root/snapshot authority |
| event-read-verify.lisp: format-step | Loads predecessor/final seal at digest base+absolute commit | Factor expected-digest source from common physical/member verifier; prefix comes from checked persisted entry |
| event-build.lisp; event-producer.lisp | Full1..cut proof enumeration, empty Merkle seed, source ownership and continuation equality | Actual prior role4 accumulator at its cut-event, then resident suffix; never seed at transient rebase cursor |
| recovery-machine.lisp: geometry/link/commit-extent/finish | Absolute recovered commit rows/digest copies and final frontier range | Selected checkpoint boundary plus exact mapped suffix; no genesis-only replay assumptions after rebasing |
| txn.lisp; owed-cursor.lisp | Logical next batch/event from commit-frontier | Keep absolute identities; do not reinterpret resident row as batch |
| commit-durable-all.lisp; commit-durable-children.lisp; commit-turn-frame.lisp | Concrete index/frame/ordering proof consumers and operation closure | Named refinement/effect preservation for actual mapped subject, no weakened theorem/ratchet or rebaseline |
| sim/check-recovery.lisp | Reads extent by absolute commit | Use exact logical lookup, distinguish archived from absent |
| sim/session.lisp | Reports row0 frontiers | Keep absolute reports unchanged |
| tests/event-proof-source-unit.lisp; retirement-live-unit.lisp | Direct extent lookup by batch | Use actual mapped identity adapters when reuse lands |
| tests/commit-ceiling-unit.lisp | Current lifetime ceiling/row/frontier observations | Keep no-checkpoint physical occupancy refusal; add actual covering-checkpoint + wrap/prefix witness before changing reuse expectations |
| tests/commit-frozen-admission-unit.lisp; commit-member-unit.lisp | Row0 frontier/abort observations | Keep absolute observations unchanged |
| tests/commit-stop-unit.lisp | Deliberate missing metadata row | Preserve explicit refusal/stop control |
| tests/txn-unit.lisp; commit-executor-contracts-unit.lisp | Synthetic frontier setters | Update only scoped representation premises when ring lands; do not claim persisted evidence |
| tests/checkpoint-directory-headroom-unit.lisp | Current actual helper/predicate credit controls | Keep exact current-state contract; later add mapped-base accounting without speculative credits |

No host source currently computes these directory indices. The two concrete
index namespaces (root cells and seal digest cells) must change together. The
current event readers/proof builders make a metadata-only ring conversion unsafe.
`fn2-commit-notification-range` presently has no source caller outside its own
definition, but its declared replayable-debt semantics must not be erased to make
reuse appear complete. Type/guard-only dependencies in event-build/producer and
writer books still need their composed closure checked after representation work.

## Qualification and refusal obligations before reuse

- Preserve exact whole-result/effect correspondence between logical batches and
  mapped rows/digests; tags and physical allocation identities prevent ABA.
- Refuse overwrite while an active commit, event reader, snapshot builder,
  notification continuation or bank evidence still depends on the old cell.
  A recipient cursor is not permission to pin the resident history forever;
  archived debt requires its actual persisted range source.
- Capture both banks' real installation evidence before releasing directory pins.
  Preserve explicit predecessor/descriptor linkage; no largest-number selection.
- Authenticate prior role3 entries and role4 accumulator from the covering
  checkpoint and append exactly the resident suffix, including its base seal and
  event-continuity boundary. Never fabricate checked candidates or snapshots.
- Recovery must reconstruct the same selected boundary and mapped suffix from
  verified persisted bytes. This lane does not independently rewrite shared boot.
- Bound rebase work per call and retain target/cursor/owner/token across yields.
  Every partial rebase/crash point needs actual recovery/refusal coverage.
- Positive witnesses must include more than one resident capacity of absolute
  commits with real covering publication/prefix preservation; mutation controls
  remove tag, predecessor, pin or bank-binding hypotheses. A larger default, a
  changed test baseline or a source-only ring declaration proves none of these.

Before the representation class changes, use the shared structural rewriter with
fixtures for the many getter/setter and digest-index consumers. Current milestone
validation is source-only: structural parsing, explicit B* dependency and named
secrets/whitespace checks; qualification of the new critical resource-credit
helper, exact caller and composed prefix/rebase obligations remains pending.
