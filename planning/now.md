# Now — 2026-10-02

The next phase starts from rewritten `origin/dev` **4aa332295**. Stage 0
restored serving; the page representation and carried-invariant work remain
the main implementation direction. The September 28 version of this page is
historical (available in git), not the current roster or release verdict.

## Coordinates

- **Source.** The history rewrite landed on October 2. The tracked
  [commit map](commit-map-20261002.txt) translates old source revisions;
  old image names and archived evidence retain their original identities.
  Create fresh worktrees under `build/lanes/` from rewritten `origin/dev`.
  Do not fetch the pre-rewrite `hbox-archive` history into the working repo.
- **Proof.** The previous coordinator's final root-failure inventory names
  only `books/productive-transfer` (local record
  `build/coordinator/bl-cert-roots-1ffe1dcd5.txt`). This is a historical
  certification result, not a fresh whole-tree verdict. Current per-book
  evidence is computed by `tools/green_check.py`; the
  [current view](current.md) keeps capability certificates separate from
  implementation, image qualification and deployment.
- **Image.** The handoff reports an image set for pre-rewrite `77b7d258d`
  at `hbox:/tank/fn/images/77b7d258d62f5d3d4a7838f8fabf61bfb518eeec`.
  Its init, log, recovery, owner, crash-model, reader-client, auth, mux and
  state-checkpoint modules passed. `over_pins` failed all four cases.
  That image predates the final source changes; it is not qualification of
  current dev or completion of the release checklist.
- **Deployment.** The last recorded deployments remain the public
  `fn.fg-goose.online` node and the LAN hbox node on `a3553e6b`, format 10.
  Their records are in [current-view.json](current-view.json). They have
  not been inspected or changed during this takeover.

Evidence bytes are archived by hash on hbox; the committed
[evidence index](evidence-index.tsv) names them. Use `tools/evidence_store.py`
to retrieve a logical `planning/evidence/...` path. Evidence files do not go
back into git history. The laptop repository budget is 30 GB; never remove
another session's files or caches to meet it.

## First closeout

Codex reproduced the outbound offer theorem's failure on the rewritten
source. The implementation now returns `fn-own-feed-port-result-counted`
and sends through `fn-feed-with-queue-preserving-counts`; the productive
proof hints still opened the older constructors. Updating only those hints
certifies all three original statements (PRF-1055, PRF-1056, PRF-1062), with
no new hypotheses or executable changes. The book and its existing teeth
passed on hbox with two jobs in `certify-20261002T202018Z-898247`; its
manifest is indexed and archived as
`planning/evidence/manifests/certify-20261002T202018Z-898247.json`. This
closes the root named in the prior inventory, not a fresh whole-tree or
native qualification. The affected-books strict green gate passes. The farm
also reports 14 cached dependencies without an indexed manifest matching
their current source and closure; those citation gaps remain open. Remote acceptance and inbound durable transfer remain
separate obligations in the
[productive contract](../specs/productive-contract.md).

## Work to finish

These are implementation priorities, not a declaration of release scope.
The architectural destination remains the
[store representation design](design-store-representation-2026-10-01.md)
and D41–D47 in the [decision register](decisions.md).

1. **Reclaim and reader lifetime.** Correct GROUP's post-reclaim count and
   put OVER on its intended cursor route; close the four `over_pins` cases.
   Add arena forgetting with a handle-liveness argument so reclaimed
   payloads release resources before restart. Old pinned readers, cold-read
   workers and generation retirement must agree on when storage is free.
2. **Stage 5: owner state and dispatch.** Move the owner's two ACL2 STATE
   globals into a dedicated stobj, establish its invariant on recovery and
   preserve it through every writer, then enable a real raw-dispatched
   entry. The previous lane's tier-A conversions are unadmitted WIP, not a
   completed prerequisite. The trap alone skips no validation and must not
   impose per-call synchronization while there are zero raw entries.
3. **Complete discovery and bounded readers.** Implement the accepted LIST
   policy below; narrow the cursor-step guard, finish off-lock cold reads
   and deadline refresh before NEWNEWS resumable wiring. Complete bounded
   withdrawal-index refresh (PRF-1231), offer carry (PRF-1233), remaining
   control walks, mux allocation and status tally costs.
4. **Authority and persistence composition.** Complete the explicit
   authority field and its producer before restoring D46's consumer event
   grammar. BP transit currently reports `:ungoverned`. Finish the retire
   deadline fix, recovery refinement (PRF-1223), and stranded/init work.
5. **Simplify while completing.** Use the existing `def-loop`,
   `def-representation` and `def-carried` machinery. Develop carried-index
   declarations and witness generation against real consumers, with
   visit/work bounds where cost is claimed. Fold the paged catalog onto the
   shared representation machinery as it becomes the served default.
6. **Finish the wider representation design.** Stage 5 is not the end:
   stage 6's typed resource vector and per-operation charging, then stage
   7's bounded index growth, checkpoint reserve and composed recovery
   argument remain in the design. Reconcile their actual landed portions
   before assigning work.
7. **Harvest useful unlanded work.** The October 2 triage identifies
   residual proof, peering, LTP and diagnostic work. Apply narrow current
   slices, reconcile their consumers and certify them; branch ancestry or
   an old READY report is not a completion claim.

The detailed local handoff is
`build/coordinator/HANDOFF-2026-10-02-to-astra.md`; the lane notes and
`unlanded-triage-2026-10-02.md` beside it are historical starting points.
No previous lane roster implies a currently running agent.

## Decisions and convergence

Ember accepted LIST option A as scoped in the October 2 consultation:
LIST, LIST ACTIVE and LIST COUNTS use one coherent latest **completed durable**
discovery view, restricted to the client, without advancing its article pin,
selection or cursor. Implementation must deliberately amend NNT-042 and
specify low-water behavior and the related discovery commands' view policies.
Catalog top is not necessarily a completed durable view. The local decision
record is `build/coordinator/decisions/list-view-2026-10-02.md`.

The exact meaning of “v6.6.0-ready” was explicitly reserved for a later
conversation. That does not block engineering closeouts or supersede D39's
instruction to complete the major work before cutting. The old
`build/coordinator/COMPLETE-BEFORE-6.6.0.md` needs reconciliation against the
current design and source before serving as the final release inventory.

Follow [how we work](how-we-work.md): certify affected roots with warm
artifacts, keep book and native evidence distinct, integrate completed
changes, and qualify one immutable candidate at convergence. The
[release checklist](release-v6.6.0.md) remains a gate, not a statement that
those checks have passed.
