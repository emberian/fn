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

## Revised preferred protocol: rescan, one final root per schema

Produce exactly one final physical root per nonempty schema before publication.
Retain all ORIGINAL source predecessors independently of output count. Rather
than persisting temporary merge runs, repeatedly visit the full held source set
for each next output key. Keep one current best entry and a stable lower key.
For each actual source, reuse the existing single-source range seek/advance,
physical MISS loader and canonical layout comparison. Skip entries equal to the
last emitted key; compare its next head against the current best using the same
newer/tie precedence as `fn2-range-pick`. A complete held-set scan establishes the
next global winner, or schema exhaustion. Then run existing typed retention,
rehome and builder add. One call never scans the whole set or article.

This costs O(S times K source seeks/advances), for S sources and K distinct output
keys, plus physical authentication and rehome work. It trades repeated reads for
bounded memory and avoids unpublished-run allocation/disposal or a new recovery
class. It does not limit S, K or page count. No replacement is published until
all schemas are exhausted and all actual output pages complete. The output count
is one per schema, within the existing four-run allowance with overlay headroom.

The named fold schemas 5/6/7 in folds.lisp store already-materialized values and
explicitly declare :merge :latest. This protocol must use the actual layout and
range comparison; it neither combines partial event deltas nor assumes addition
or default-zero associativity. Further registered schemas must be checked against
the same actual sealer semantics before enabling them.

Candidate exact operations (internal static calls, not arbitrary callbacks):

- compaction-begin derives HELD token/candidate/owner and starts the original-source
  inventory; no caller member count or completion flag.
- source-step retains actual source identity and bounded whole-set scan progress;
  reseek-step drives the existing cursor, returning :need-read separately.
- candidate-step compares two actual authenticated entry views, then invokes the
  existing bounded rehome for a replacement best. The source page stays frozen
  until that copy completes; lower-key bytes remain immutable throughout a scan.
- selected-entry-bind constructs the common retained-entry only from the finished
  whole-set scan and current candidate identity. Existing semantic/payload closure
  runs before builder add; consume requires exact origin/serial completion.
- page bind/worker TAKE/write harvest/RETURN/consume are unchanged actual checkpoint
  operations. Directory emit occurs only at schema exhaustion and uses final dense
  output rank, independent of original inventory rank.
- existing typed live retirement must consume original inventory rather than
  manifest root count; it preserves durable old holds until actual replacement.

Proposed new leaves are checkpoint-compaction-state/source/merge. Scoped adapters
are checkpoint-metadata-source/metadata/manifest/driver, plus the original-source
inventory consumer in checkpoint-live-retire under its owner's coordination.
The master owner wires ordinary sealer request -> real drain -> checkpoint ->
resume; a disabled route or helper endpoint does not repair FULL. Do not add B
records, parsers or hashers. Existing legacy bounded resident admission may remain
for its genuine fast path, but physical/unbounded output must take this route
before a prefix is emitted.

Resource investigation is still pending. Existing candidate entry window14,
semantic window16 and physical page/read19/20 might support best/lower-key/input
roles in disjoint phases; semantic closure overwrites16, so the lower key must
be reconstructible from the protected current candidate after closure and before
the next scan. Exact octet references and reset/generation checks must demonstrate
this without authority borrowing. An eight-pair recipe would require43 windows instead of the current29 and remains
on HOLD; no
geometry edits or class/credit feasibility claim is made. If another protected
scratch is required it must join atomic pre-cut admission, not a held-cut wait.
