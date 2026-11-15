# Physical merge output: proposed connected implementation

Source basis: `53973df71`. This is an implementation proposal, not an implemented
physical-output producer or an admission result. Ordinary sealer output still
retains every generated run page in the resident cache and can reach FULL.

The preferred route is compacting checkpoint root1, using its actual held cut,
construction ledger, page worker, descriptor installation, Fence and typed live
replacement. Direct ordinary streaming is a larger alternative: the tree has a
run-replacement codec and an unregistered `fn2-runs-install` hook, but no connected
ordinary replacement admission/replay/publication producer. Those codec objects
alone confer no durability or replacement authority.

## Existing implementation seams

- `fn2-seal-merge-next` uses the actual range advance/pick/consume operations and
  `fn2-run-build-add`. Extract its common merge continuation, retaining separate
  ordinary-source and HELD checkpoint-source authority checks. Do not duplicate
  range ordering, decoding, entry copying or page construction.
- `fn2-checkpoint-source-step` enumerates actual held sources in ascending served
  precedence: schema, runs before overlays, increasing RUN/SEQ, decreasing row on
  ties. It scans one row per call, including empty/dead rows, and proves exhaustion
  by a complete scan. The current selection cost is O(N squared).
- `fn2-checkpoint-metadata-manifest-emit` currently binds one selected source to
  one emitted root and captures exactly that predecessor. Compaction must replace
  this one-to-one condition with retained actual group membership; substituting a
  nominal selected row would lose old-source retirement and coverage provenance.
- Existing metadata page production reserves real B identities, seals/verifies
  through the canonical codec, loans immutable workspace to the actual page
  worker, harvests exact writes, and waits for handback before promotion. Completion
  remains distinct from the eventual covering Fence/publication.

## Proposed bounded source and output protocol

1. Request checkpoint compaction before an ordinary sealer emits any resident
   prefix. Release its source receipt and unused leases before waiting. An active
   sealer must first finish/drain; the checkpoint never borrows ordinary authority
   or permits publication while C is HELD.
2. Under the actual HELD token, form contiguous precedence intervals within each
   schema, each with at most the declared active merge fan-in. Retain membership
   from actual source rows, including owner/generation, order and physical fullRef.
   This table is sized from admitted source-row geometry, not article count.
3. Feed each interval through the shared merge engine, canonical entry rehome,
   typed semantic/payload retention and existing run builder. Preserve the actual
   winning entry's origin until retention and encoding consume it. No complete flag
   or caller-supplied ready source substitutes for those checks.
4. Split consumed input rank from emitted dense output rank. Rebuild singleton
   intervals too: the output RUN/header identity then remains the new dense rank,
   matching current manifest/catalog interpretation without a new wire layout.
   Contiguous intervals preserve relative precedence outside the merged interval.
5. Emit one directory entry per completed interval, only after every member is
   exhausted and all output pages physically complete. Keep every old predecessor
   in the typed replacement inventory. Existing post-Fence/current-catalog,
   new-Cbase-HELD and EXCLUSIVE gates install output and retire all old inputs;
   query leases drain against the old immutable catalog. Ordinary row retirement
   never releases the persistent old Cbase promise.
6. Recover through the existing descriptor/root1 traversal and typed payload
   closure. No new journal record or alternate recovery parser is proposed.

For M sources of a schema and fan-in N, a completed generation produces
ceil(M/N) roots, including singleton tails; repeated durable generations decrease
M when M>N. This bounds active cursors, not stored entries or output pages. The
consumer must still demonstrate how initially excessive source counts progress
without skipping a source or returning an unchanged FULL retry. That connection
is an explicit acceptance obligation, not established by this arithmetic.

## Resource and file ownership proposal

At this basis, root1 has 21 windows (including its physical input pair at19/20)
and future workers have eight: 29 total. Reusing one pair and admitting N pairs
adds 2*(N-1); N=8 would give 43 leases. Derive all demand from existing declarations
and actual class aliases. Reserve the whole recipe before the cut; initialize
borrowed loader jobs only after HELD, since snapshot final poll requires sealer
jobs genuinely idle/free. Preserve stable publisher windows14/16/18. Exact range,
checker and field geometry, phase costs and protected credit feasibility require
source review before adopting this recipe.

Proposed owned books: new checkpoint-compaction state/source/merge leaves; shared
merge extraction from sealer; scoped root1 source/metadata/manifest/driver and
working geometry changes. Coordinate master request/continuation wiring, typed
catalog predecessor retirement and pool-credit changes with their owners before
editing those files. No CNS changes or second B writer are in this slice.

Required controls: tied source precedence before/after compaction; more than one
fan-in interval; a source larger than resident cache capacity streaming pages;
actual I/O harvest and page handback; all predecessor retirement and surviving
old query leases; pre-Fence crash retains old authority; post-publication restart
installs merged roots; partial recipe refusal releases the source receipt; and
CLOSING drains before HELD. Runtime/proof execution is not authorized in this lane.
