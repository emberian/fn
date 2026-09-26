# Checkpoints: logical value, canonical bytes, generation publication

Status: the logical core (`books/checkpoint.lisp`), canonical byte encoding
(`books/checkpoint-codec.lisp`, C1-10), generation publication/selection
machine (`books/checkpoint-publish.lisp`, C2-09), and their three test books
are certified.  The post-merge hbox run
`build/acl2/certify-20260921T020148Z-1425543` at source `186ed0b` plus
`6ad5a80` passed all six checkpoint roots; the two failures among its 276
roots were the separately-owned BP-node roots.  The exact manifest and the
earlier defect/fix history are recorded in
`planning/evidence/checkpoint-validator-2026-09-21.md`.  Counts live in the
generated ledger; this page carries each keystone's property, hypotheses and
covered scope, and what the hosts still assert.

## 1. The logical checkpoint (`books/checkpoint.lisp`)

A checkpoint is the seven-tuple `(:fn-checkpoint 1 groups capacity frontier
sequence node)`: the exact `fn-node` state after replaying `sequence`
records, the configured group list and retention capacity it binds, and the
consumed allocator frontier, which may be ahead of the node's next
transaction id because known-aborted reservations leave no record. Capture
replays the prefix once; restore takes no prefix and runs `fn-replay-loop`
only on the suffix, after checking the configuration binding, the stored
sequence, and that every suffix transaction id is at or above the consumed
frontier and below the observed final frontier.

- `fn-checkpoint-plus-suffix-equals-full-replay`: for every admissible split
  (`fn-checkpoint-admissible-splitp`: ordered journal intervals, successful
  prefix and full replays, both nodes reconcilable with their frontiers),
  capture followed by suffix restore equals full-history replay normalized to
  the same final frontier. Scope: the executable replay machine; allocator
  gaps before and after the checkpoint are permitted.
- `fn-checkpoint-restore-rejects-frontier-reuse`: for any checkpoint,
  matching configuration and valid frontier, a suffix whose first record
  reuses a transaction id below the consumed frontier is refused with
  `(:error :suffix)` before replay runs.

## 2. Canonical bytes (`books/checkpoint-codec.lisp`)

Layout, a concatenation of the records book's CBOR primitives: bytes
`"fn-c"`, uint schema 1 for new captures, uint sequence, uint frontier, uint capacity, uint
group count, one bytes item per group, then `TREE(node)`. `TREE` is a tagged
encoding of the node's value universe (`fn-cpc-treep`: nil, naturals below
2^32, octet-domain strings, the symbols `t`, `:archive`, `:forward`,
non-empty octet lists, conses). An octet list is always one bytes item and
never a cons chain, so each value has one spelling; the decoder refuses the
cons spelling (`:noncanonical`), the empty bytes item under the octet tag, a
non-minimal CBOR head, an unknown tag or symbol code, and a cons deeper than
its depth fuel (the octets it has). The item reader has no per-item
whole-stream preflight: the frame bounds the payload once (4 MiB).

The decoder also accepts schema 0 selected checkpoints written before the
acceptance stamp. A ready pre-stamp node has five-field articles and no pending
transaction; ACL2 appends `:legacy` to each article, leaves every other field
unchanged, then requires the complete current `fn-checkpointp` before restore.
Version 1 never migrates an old shape. The short-lived T2 image that wrote a
six-field node under schema 0 is accepted unchanged when it already passes
`fn-checkpointp`. The generation frame and selection marker remain protected
and are checked before migration; the saved bytes are not rewritten. Restore
still compares the private checkpoint-plus-suffix result with authoritative
full journal replay, so migration cannot replace a mismatched live state.

- `fn-cpc-decode-of-encode` (value direction): for an encodable checkpoint
  whose encoding fits the payload cap, decoding at its own groups and
  capacity and at any observed frontier and record-count bounds at or beyond
  its own yields `(:ok checkpoint)`. Hypotheses: `fn-cpc-encodablep` (a
  `fn-checkpointp` value with octet-domain group names, at most 16 groups,
  32-bit capacity and sequence, node in the universe), the two bounds.
- `fn-cpc-accepted-input-is-canonical` (byte direction): an accepted **schema
  1** input is exactly the encoding of the value returned. Hypotheses:
  acceptance and the current-version header. A schema 0 pre-stamp checkpoint
  migrates its logical article shape and therefore cannot re-encode to the
  identical bytes using the schema 1 encoder; the canonical raw-tree decoder
  still rejects alternate byte spellings before that migration.
  The decoder itself establishes the octet domain, cap, magic, version,
  bounds, configuration equality, absence of trailing octets and
  `fn-checkpointp` of the assembled value.
- `fn-cpc-decode-rejects-{mismatched-capacity, mismatched-groups,
  frontier-ahead, count-ahead}-before-node`: with the header's verdict fixed,
  the same refusal (`:configuration`, `:frontier`, `:sequence`) results for
  every octet tail in place of the node item, so the node is never parsed.
- `fn-cpc-valid-is-capture-value` (exact binding): a checkpoint that
  validates against a record prefix is `fn-checkpoint-capture-value` of that
  prefix at the checkpoint's frontier. Only hypothesis: `fn-cpc-validp`,
  which is the recognizer, matching groups and capacity, the prefix being an
  ordered journal interval below the checkpoint's frontier
  (`fn-sf-record-listp`), and the actual replay of the prefix yielding the
  checkpoint's sequence and node. Every field is fixed by the prefix.
- `fn-cpc-valid-refuses-generation-mismatch` (refusal): if any record of the
  prefix binds a generation other than its own transaction id, `fn-cpc-validp`
  is false, for every checkpoint and configuration offered with it.
  Hypotheses: membership and the mismatch; `:rule-classes nil`, since as a
  rewrite it would be a free-variable rule concluding `nil` on a recognizer.
  The journal-interval clause it rests on is load-bearing and was absent
  until 2026-09-21: `fn-replay` carries a record's generation into the node
  transitions without ever comparing it with the txid, so the replay of a
  prefix whose generation is corrupt is *equal* to the replay of the sound
  prefix, and validation accepted a prefix that `fn-checkpoint-capture`
  refuses as `:history`. Validation is the third member of the family that
  tests this condition, beside capture's `:history` and restore's `:suffix`.
- The frame: `fn-cpc-frame-{encode,decode}` carry the payload in the generic
  `fn-frame` grammar under this book's magic `FNCP` and kind table
  `(:checkpoint :selection)`; `fn-cpc-frame-decode-of-encode`,
  `fn-cpc-frame-open-of-seal` (against A-CRYPTO),
  `fn-cpc-frame-accepted-is-canonical`, `fn-cpc-selection-decode-of-encode`.

Residual: a wholly well-formed checkpoint substituted for another under the
same name decodes; the frame trailer detects damage only under A-CRYPTO's
algorithm assumptions, never freshness or durability.

## 3. Generation publication and selection (`books/checkpoint-publish.lisp`)

A generation is published as the store publishes a record: candidate bytes
data-durable under a staged name, linked under `generation-N`, directory
barrier; then, and only then, selected by the same three steps on the
marker file (`selected`), whose namespace step is an atomic replacement.
Authority is the explicit marker, chosen over a newest-valid-generation
rule because the latter turns a corrupt newest generation into a silent
roll-back to its predecessor. Each generation entry carries its bytes and,
as ghost fields, the prefix, frontier and host digest that made them.
Crash images follow `fn-sf-crash`: marker `:old`/`:new` is live from
`:marker-data-durable`, generation `:absent`/`:present` from
`:candidate-data-durable`; a present generation is the exact data-durable
candidate (the store's A-WRITE-ISOLATION premise). That choice pair is the
K12 shape of [the byte-level crash model](crash-model-v2.md) §3.3; K12 stays
open there until its P8 programs are re-transcribed from the committed
`tools/checkpoint.py`, which is a successor lane's step, not this book's.

- `fn-cpp-crash-selects-old-authority-or-complete-candidate`: from any
  reachable state (`fn-cpp-statep`) and any choice, the image's marker is the
  previous authority, or it names the candidate and the image holds the
  candidate's complete entry. The `:new` choice exists only in marker phases,
  reachable only through `:candidate-published`.
- `fn-cpp-crash-marker-is-authority-before-selection-attempted`: before
  `os.replace` on the marker may have been issued, every image's marker is
  the old authority.
- `fn-cpp-recover-selects-complete-generation`: for a well-formed image
  (`fn-cpp-imagep`) whose marker names a generation, with the host's digest
  equal to the one that sealed it and the observed frontier and record count
  at or beyond the generation's, recovery is `(:ok name checkpoint)` with the
  checkpoint the capture of that generation's prefix.
- `fn-cpp-recover-reports-corruption`: replacing the selected generation's
  bytes by any bytes the codec refuses makes recovery `(:corrupt name
  reason)`: not `:ok` for any generation, not `:none`.
  `fn-cpp-corrupting-unselected-generation-is-invisible` is the other half:
  only the marker's generation is consulted.
- `fn-cpp-selected-plus-suffix-equals-full-replay`: under the recovery
  hypotheses and an admissible split of the generation's prefix with a
  suffix, `fn-checkpoint-restore` of the recovered checkpoint equals
  `fn-checkpoint-full-replay` of prefix plus suffix (composition with §1).
- `fn-cpp-authority-retained-until-selection-durable` and
  `fn-cpp-published-generations-retained`: no step but the marker's
  directory barrier changes the authority; no step or crash removes a
  published generation.

Outcomes stay distinct: `(:none)`, `(:ok name checkpoint)`, `(:corrupt name
reason)`, `(:missing name)`.

## 4. Host adoption

### Python experiment (`tools/checkpoint.py`, `tools/run_store.py`)

`publish` asks ACL2 for the protected prefix of the capture of the durable
records at the durable frontier (`fn-store-checkpoint-protected`), seals it
with SHA-256 (A-CRYPTO), and issues the three publication steps; `select`
issues the three marker steps. The six `faults.at("checkpoint:<name>")`
sites are the cuts in `tests/campaign/cuts.py`. `Store.recover` replays the
journal as before (the journal remains the authority), then decodes the
selected generation through `fn-store-checkpoint-decode` at the observed
frontier and count, slices the suffix by the sequence ACL2 returned,
restores through `fn-store-checkpoint-restore` (the proved subject) and asks
`fn-store-checkpoint-differential` whether the restored node equals the node
full replay produced. The outcome (`none`, `ok`, `corrupt`) is printed by
`recover` and `checkpoint.py status`; `corrupt` exits 4.

Both hosts obtain `selected.fncp`, canonical `generation-N.fncp` rendering,
the inverse filename decoder, the exact 47-octet selection-frame read bound,
and the checkpoint-directory observation plan from
`books/checkpoint-publish.lisp`.  The plan sorts decoded generations and
rejects every other entry.  Hosts call the ACL2-owned observation bound
before retaining directory names: the opened profile's retained-generation
capacity, max-transactions + 1 (`fn-cpp-generation-capacity`), plus the
selection marker.  Generation allocation refuses exactly at that capacity
(`fn-cpp-next-generation-refuses-exactly-at-the-profile-capacity`; for packs,
whose numbers have gaps after retirement,
`fn-cprt-next-generation-refuses-exactly-at-the-profile-capacity`), and a
generation number runs to the uint32 width of its name and selection codec
(STO-023, PRF-171; until then a store had 4,096 publications in its
lifetime).

What the host still asserts, outside the proofs:

- SHA-256 is a fixed function of the bytes (the digest the host supplies at
  recovery is the one it supplied at publication when the bytes are
  unchanged); ACL2 only compares it.
- `os.link` publishes the whole data-durable file or nothing, `os.replace`
  leaves the old or the new marker, and `fsync` orders them: the store's
  A-DURABILITY and A-WRITE-ISOLATION premises, exercised by process-death
  tests with the OS cache retained, not by power-loss qualification.
- Production recovery remains full replay, but differential inequality is
  always a corrupt-checkpoint outcome and exit 4.  The mismatch cannot alter
  live state, and an operator flag cannot turn it into `ok`.
- Rollback of a valid older generation together with a truncated journal
  still needs an external freshness anchor (C2-12); a detected invalid
  checkpoint is a diagnostic failure, never permission to discard history.

### Native saved image

`host/native/checkpoint.lisp` exposes `checkpoint publish`, `select`, and
`status` in the saved image.  Capture, framing, selection-marker framing,
generation allocation, marker phase/action/outcome, decode, suffix restore,
and the differential verdict are ACL2 calls through
`host/checkpoint-host.lisp`.  Immutable generation publication uses the
shared U04 no-replace effect; marker replacement is a distinct driver whose
called phase step is related to the full `fn-cpp` transition by
`fn-cpp-marker-driver-step-corresponds`.

The native recovery hook runs only after the ordinary journal replay and all
of its recovery barriers.  Checkpoint restore writes checkpoint-private ACL2
globals and compares their node with the already-live `fn-store-sn`; it never
resets or replaces that state.  `none`, `ok`, and `corrupt` remain distinct,
and a corrupt selected generation exits 4 without trying an older generation.
This is diagnostic adoption only: suffix-only startup is not claimed because
the physical assumptions needed to replace full replay have not been
discharged.

The version-two auxiliary diagnostic compares the authoritative exact-history
replay with the reopened Store's historical authorship verdicts, keyring
snapshots, completed dense sequence, E2 consumer projection, topic projection,
and rebuilt consumer sequence index.  This is a recovery-time comparison only.
It reports `auxiliary=equal-v2` only when all six agree; disagreement is a corrupt selected checkpoint, not a repair that
replaces the live Store.  The node checkpoint format remains version one and
contains only the node.  A selected `fn-cc` pack remains format zero and
retains the exact original event bytes from dense sequence zero; expansion
before full Store reopen is what preserves the auxiliary history.  Reclaiming
physical prefix names must not change issued dense Store positions.

### Cold writable clone activation

A byte copy is not an activated Store.  The native `checkpoint clone SOURCE
DESTINATION` operation requires an offline, locked source and a destination
that does not exist.  The host observes a fresh 32-octet incarnation ID from
the OS CSPRNG; ACL2 validates its shape, rejects equality with the copied
history or current incarnation, and constructs the durable rollover event.
Distinct sibling clones rely on probabilistic entropy uniqueness, not a
proved global uniqueness claim.  Source and destination CLI paths must be
absolute, NUL-free and at most 512 UTF-8 octets, matching the ACL2 native
configuration path bound.  Canonicalized aliases, the staging path, fence
path and every joined copy path are checked against the same bound before
traversal.  It first builds a private sibling directory containing the
exact source bytes and a durable `clone-pending.fnce` fence.  The fence holds
the canonical version-one `fnce` rollover event proposed by ACL2, not a
second projection format.  Publication uses Linux `renameat2` with
`RENAME_NOREPLACE`; another platform refuses this operation.  Publication of
that directory may expose the destination name but
must never make it serviceable while the fence exists.  Every normal writable
or reader open at that destination refuses before Store initialization or
recovery can serve it.  The clone executor alone reopens the destination under
an exclusive lock, lets ACL2 propose `(:rollover fresh-id)` using the
recovered dense sequence and allocator coordinates, and publishes it through
the ordinary Store transaction.  ACL2 supplies the offline copy ceilings:
depth 16, at most 1,000,000 directory entries, and at most 2^40 bytes of
regular-file content; the host streams in 65,536-byte chunks and refuses
before exceeding those limits.  The history ID remains the same; the new
incarnation differs from the copied source.  A same-ID, history-ID, malformed, or
unbootstrapped proposal is refused.  The fence is removed only after a second
exact-history reopen confirms the durable rollover and new incarnation; the
fence removal and its parent-directory barrier are themselves part of the
activation operation.

A death before directory publication leaves only an unservable private
staging tree.  A death after publication but before a completed rollover
leaves the destination fenced.  An ambiguous publication or rollover completion also
leaves it fenced, requiring recovery to inspect the durable journal.  If the
rollover completed but fence removal did not, retry verifies that same event
and removes the fence without appending another rollover.  After independent
reopen confirms the durable rollover, an unlink or directory-barrier error
still reports uncertainty.  The marker may already be absent, but ordinary
opens are safe because the new incarnation is durable.  A different
incarnation or an existing nonempty destination is never overwritten.  The
copied old cursor tokens are invalid after the new incarnation; registration
state resets, while exact journal history, article and retention obligations,
authorship verdicts, and keyring snapshots remain.  This paragraph is the
activation contract.  The source contains the executor and pre-open fence;
native saved-image qualification and a nonzero served consumer cursor witness remain
open.  `checkpoint clone-resume DESTINATION` is the only operator path that
may reopen a fenced destination; it verifies the same durable event rather
than proposing a second incarnation.  Tests and operators use the production
`consumer bootstrap CONTROL` owner command.

The filename codec reuses the byte store's proved natural-decimal renderer.
`fn-cpp-generation-name-decode-of-render` is its called-codec round trip;
canonical re-rendering rejects leading-zero aliases, signs, overflow and
partial prefix/suffix values.  Native and Python hosts now marshal entry
octets and execute the returned plan; neither parses, formats or sorts the
generation namespace.

### Selected-pack reclaim crash cuts

`fnn-pack-prefix-reclaim` calls the logical
`fn-bs-pack-reclaim-plan` on the bounded, sorted physical transaction
namespace.  The plan returns only surviving names below the selected pack's
coverage boundary.  Its byte program has one `pack-reclaim-unlink` cut after
each issued unlink and one `pack-reclaim-directory` cut after the
transaction-directory barrier.  Before that barrier, each pending
`:del-entry` may apply or drop independently, so a process-death image may
retain an arbitrary subset of covered names.  After the barrier, no crash
choice restores a reclaimed name.  Neither transition permits a missing
name in the uncovered suffix.

Recovery calls `fn-store-checkpoint-compaction-observe` over the surviving
sequence/raw-octet pairs.  `fn-cc-partial-deletion-preserves-exact-history`
reconstructs the selected prefix plus exact suffix when every surviving
covered byte string agrees with the pack; a conflicting surviving covered
file returns `:conflict`.  The byte cut witnesses and source map are static
model evidence until they run against a source-matched developer image.
They do not qualify filesystem power-loss behavior.

### Superseded pack retirement

`checkpoint pack-retire ROOT` reopens the Store under its exclusive lock,
validates the selected pack and its coverage, and asks
`fn-cprt-retire-plan` for the strictly older generation names.  It unlinks
those names only, with a `pack-retire-unlink` process-death cut after each
unlink and a `pack-retire-directory` cut after the packs-directory barrier.
An empty plan returns without a barrier or retirement cut.  An ambiguous
unlink error may already have removed its attempted name and requires reopen.
The ACL2 crash-survivor model permits any issued unlink to reappear before
the barrier; the selected generation is never in the plan.  A reopened Store
can therefore retry retirement after either cut without selecting a different
authority or changing exact event history.  The separate pack allocator
accepts gaps left by retirement but always advances beyond the highest
remaining generation.  `fn-cprt-publication-initial` applies that same
gap-aware namespace to actual immutable pack publication; ordinary node
checkpoints retain their gap-free publication policy.  Retirement recovers
space occupied by superseded
packs, not by retained source events or protected article objects.  The
bounded generation number still has a finite lifetime and does not wrap.
