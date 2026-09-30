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

The decoder accepts one schema, 1. A header naming any other version (the
pre-stamp schema 0 of earlier releases included) is refused `:version`, and a
node whose articles lack the acceptance stamp is refused `:invalid` by
`fn-checkpointp`; no shape is migrated (no migrations: every node redeploys
fresh at 6.6.0).

- `fn-cpc-decode-of-encode` (value direction): for an encodable checkpoint
  whose encoding fits the payload cap, decoding at its own groups and
  capacity and at any observed frontier and record-count bounds at or beyond
  its own yields `(:ok checkpoint)`. Hypotheses: `fn-cpc-encodablep` (a
  `fn-checkpointp` value with octet-domain group names, at most 16 groups,
  32-bit capacity and sequence, node in the universe), the two bounds.
- `fn-cpc-accepted-input-is-canonical` (byte direction): an accepted input is
  exactly the encoding of the value returned. Hypothesis: acceptance (the
  current-version header hypothesis went with schema 0; the weakened theorem
  is proved).
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
with BLAKE3 (A-CRYPTO), and issues the three publication steps; `select`
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
(`fn-cpp-next-generation-refuses-exactly-at-the-profile-capacity`), and a
generation number runs to the uint32 width of its name and selection codec
(STO-023, PRF-171; until then a store had 4,096 publications in its
lifetime).

What the host still asserts, outside the proofs:

- BLAKE3 is a fixed function of the bytes (the digest the host supplies at
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

Retired on the record log (lane matrix-reds, 2026-09-27).  The saved image
exposed `checkpoint publish`, `select` and `status` over the generation
frames above, and the open ran a diagnostic restore of the selected
generation after the full replay.  Since the records flip the node
`fn-checkpoint-capture` returns holds arena handles its frame does not
resolve, so the capture of any store holding an article was refused
(`store: ACL2 refused checkpoint capture`, `(:error :arena)` in
`host/checkpoint-host.lisp` `fn-store-checkpoint-protected`).  The three
verbs now refuse by name and the open runs no generation restore; the
recover line has no `checkpoint=` field.  Format 9's checkpoint is the
state checkpoint (`fn-bs-scp-program`, the arena run then the tables; the
open reads it, `fn-sn-recover-from-checkpoint-equals-full-recover`, PRF-083,
and `fn-scka-load-of-written-file`), natively
`tests.test_native_state_checkpoint`, `tests.test_native_checkpoint_auto`
and `tests.test_native_log_compaction`.  The books of this specification
(`checkpoint`, `checkpoint-codec`, `checkpoint-publish`) remain as the
logical model and for the per-file Python fork (`tools/checkpoint.py`);
their deletion belongs with the rest of PKT-838's per-file deletion.

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

### Pack reclaim and pack retirement (retired)

The per-file layout's selected-pack reclaim and superseded-pack retirement
(`checkpoint pack-reclaim`, `checkpoint pack-retire`, their byte programs
and crash cuts) went with that layout: the native verbs in PKT-838, the
books (checkpoint-pack-retire, checkpoint-compaction-preservation,
byte-store-compaction-correspondence) and host wrappers in lane
flip-cleanup (2026-09-27). On the record log compaction and reclamation are
the log's rotation and drop (specs/storage.md STO-012, STO-017, STO-034).

### Live capture projection proof (PRF-1068; producer gate remains open)

`fn-osr-capture` takes the already carried Store pointer. Its proof-side
`fn-osr-livep` combines the phase-aware configured history relation with
independent identity, consumer and topic prefixes. Actual successful configured
startup establishes these prefixes; actual durable completion and configuration
publication preserve the live carry. A live capture therefore opens successfully
under its captured configuration history, including an in-flight transaction, without an open-success premise or a
served history scan. At readiness, recovered node, domain/capacity, configuration/event history,
frontier, identity cursor/snapshots, consumer obligations and topic
conflicts/provenance equal the captured values. Source readiness and recovery
barriers intentionally differ.

This inverse is a dependency of the live producer, not its completion claim.
The proof vocabulary `fn-osr-retainedp` additionally carries the statement
keytable/current generation resolved from retained snapshots, ordinary held
authorship verdicts and frozen row index from the completed prefix, and the
retired event-index field. Actual successful configured open establishes this
full carry; successful open also implies a proper configuration list, so that
list check is not a separate initialization hypothesis. At readiness,
`fn-osr-ready-capture-keeps-retained-fields` compares these fields after the same
actual configured recovery. Its positive witness has ordinary ARTICLE rows on
both sides of a statement-key rotation; a linked but unfinished ARTICLE shows
why readiness remains material to that equality.

Actual durable CONFIG publication also preserves this full carry without
revalidating the history: its semantic fields and completed prefix remain
unchanged while the configured node and configuration history advance.
Full producer readiness still requires preservation across the other actual
transitions, the canonical writer/load payload alpha boundary, and owner
node-secret installation. The owner secret is
separate from the Store statement keytable. Canonical row handles and paused
checkpoint summaries do not become identical to live fields by assertion.
Existing publication assumptions connect verified bytes to checkpoint tables;
this carry adds no new assumption and does not replace that boundary.

### Captured record source identity (PRF-1099; controller remains open)

The source protocol borrows the captured records-field and immutable based
handle. Snoc order restoration copies one cell per scheduling step and retains
the prepared ordered suffix for subsequent census and column passes. A fixed
thirteen-cell cursor carries scalar epoch, capture lease, pass and row ordinal;
only a completion matching that exact issued token advances the source. A
restart requires a drained pass, increases its pass serial and reuses the
prepared pointer. It refuses while a row request is outstanding or rows remain.
Delayed completions from an earlier pass cannot supply a new pass's row. This
protocol does not establish decoder contents, authenticated page mapping,
funded reversal scratch or the complete online producer.

### Bounded borrowed history decoding (planned, PRF-1102 / SCN-1014)

The captured history source is decoded incrementally using the unchanged tree
codec. `books/history-decode-stream.lisp` consumes one verified byte per active
step and retains source epoch and lease; raw string, symbol and octet payloads
remain borrowed spans in `books/history-decode-nodes.lisp`. Its non-executable
abstraction denotes the existing logical row. Numeric decoding refines the
current little-endian reader, including accepted nonminimal spellings. The
canonical encoder must classify pair-shaped octet lists incrementally and
canonicalize empty octet spans to NIL rather than copy old instruction bytes.

The full requirement remains open: captured-root directory/table/data
validation, exact row semantic inverse, padding and MKEY validation, carried
source-token binding, funded node/stack allocation, guard-verified host
composition and matching native evidence. Neither a source parser nor a
fixed page buffer alone establishes that boundary. See
[the concrete contract](../planning/history-decode-contract.md).

Borrowed decoded rows use shallow pair-node remap: ordinary held field four
changes to the target handle, or composite field two's held field four changes.
All other node references, including raw string/symbol spans, original signed
statement, frozen context and any appended binding descriptor remain borrowed.
The non-executable decoder abstraction refines those updates to the same
logical row field replacement. This structural component does not yet prove
decoder grammar carry, physical payload correspondence or full producer
recovery. No terminal string coercion or symbol interning is introduced.
## History page write continuation (PRF-1086)

`books/history-page-cursor.lisp` provides a library continuation over the current
history image commit plan. Begin retains source list references; a tick emits
one `(physical-address selector word-base)` descriptor or advances between data,
table, directory and terminal phases. Its runtime guard inspects at most ten
outer cells and three scalar counters, never a retained source suffix. The
residual theorem equates emitted prefix plus remaining descriptors with
`fn-his-plan-writes`; capture and lease identities remain unchanged. The caller
must retain the source image and resource lease until consumption completes.
SCN-1007 supplies nonempty phase and corrupted-state/mutation witnesses.

This component has no host caller yet and does not bound existing whole-history
build/flush, commit allocation/digests, or the native by-address hash. Those are
replaced by the selected census plus disk-backed bounded-buffer design in
[the preparation contract](../planning/history-page-cursor-contract.md), whose
full representation, effect and funded-publication proofs remain open.

The next private-writer component, `books/history-page-layout.lisp` (PRF-1092),
computes scalar physical layout after the census supplies data-page count N.
The existing fresh allocator reserves the directory first at address 1, then
allocates data and table pages contiguously. The executable constructor returns
N, table count T, directory span M, data base `1+M`, table base `1+M+N` and high
water `1+M+N+T`; a single-address operation computes one member. Both refine
`pgs-alloc` without constructing its list of singles. It uses the concrete
constant-work table-count function and current-format u64/u32 checks. This
removes whole-run allocation planning from the proposed private writer; it
neither allocates backing pages nor proves platform file-offset representation.

## Running and stopped snapshot producer

HST-040 remains planned: the producer must capture one committed Store
frontier, its configuration history, genesis identity, retained identity
snapshots/verdicts and keyring generation. Restore must recover retained
article/conflict/provenance, configuration, identity, consumer obligation,
topic, resource and history state at that frontier. Transient connections,
recovery barriers and process-local descriptors are not copied state.

A running capture must retain the immutable Store/image epoch and a resource
lease while later publications proceed. New resident, disk, descriptor,
worker and pinned old-artifact demands must be admitted under the supported
profile before work. Each scheduling step bounds work and fresh allocation;
a depleted quantum resumes without truncating retained data. The completion
marker is published last after all promised target data and namespace
barriers are durable. Ambiguous publication/fence failures remain uncertain
and preserve recovery evidence.

The live-carry inverse PRF-1068 and page-descriptor/layout components
PRF-1086/1092 are dependencies of that producer, not its completion. The
landed library continuations do not install a producer host call, allocate
its resources, replace whole history build/flush, or establish full retained
projection and byte-effect refinement. The unmerged producer prototype's
other proof roots are not imported by these leaf components.

`books/history-page-buffer.lisp` (PRF-1093) supplies the concrete scratch page:
a fixed 2048-u64 array, a bounded written-prefix counter, and capture/lease
references. Begin resets only the counter and identities. Put writes one word;
the accessor refuses unwritten offsets even when an old physical word remains
there. The prefix refinement equates each successful put with one logical word
append; full-page refusal leaves the state unchanged. This is one format page,
not a data-capacity limit. Buffer allocation needs its actual runtime charge,
and reuse must wait for completion/join of every I/O owner. The proof-only
prefix collector is excluded from the host path; serialization and complete
image effect composition remain open.

`books/history-image-census.lisp` and `books/history-image-header.lisp`
(PRF-1096) connect scalar census to current-format header emission. A completed
row contributes its exact resumable-codec byte count and its own pad8 bytes;
a stale ordinal or u64 field overflow leaves census totals unchanged. The
four scalar regions each occupy `8*count` used bytes. Two scalar capacity
cursors suffice for those columns and the payload region; a tick doubles once,
with no recursive capacity calculation. Their results produce the canonical
five starts and page count. `fn-hch-tick` writes one word of the existing
FNADTSN2 header into the fixed scratch and returns done only after that page is
full. The named effect theorem connects the concrete prefix to `fn-hp-hdr2`;
no header-sized list or zero vector is constructed by execution.

These are component boundaries: the exact codec count is supplied by a
separate resumable encoder, and capture/lease identities remain in its parent
cursor and the scratch. Captured based histories require the new bounded
current-format decoder, including borrowed string/symbol/octet spans; resident
suffix rows remain borrowed references. Neither an eager `fn-sf-records`
conversion nor terminal span materialization is permitted. Canonical body,
table/directory emission, offset-domain checks, resource admission and complete
publication refinement remain open. This source increment carries no served
keystone or certification claim.

`books/history-page-metadata.lisp` (PRF-1104) emits the existing six-word
address/transaction/digest entry into the same scratch. `fn-hpm-tick` carries
ordinal, component and remaining run words; each stored word advances once.
Page-full, done and address/ordinal refusal preserve cursor and scratch. The
ordinal/component survives scratch consumption/reset, since a directory entry
may straddle physical pages. Named entry, run-position and concrete effect
refinements use `pgs-entry-words` and `pgs-encode-run`; a table is the single-page
case, with its341entries and two final zeros. Digest source attribution remains
an explicit premise: the spool reader must return the exact captured/staged
digest at that ordinal. The emitter retains only one256-bit digest and scalar
state. It preserves concrete scratch representation and epoch/lease identity.
Complete spool admission, authenticated reads, final root binding and served
composition remain open; no host caller or certification claim is added.

The scalar layout component also exposes `fn-hpi-region/page` in
`books/history-page-io.lisp`: positional whole-file requests use the unchanged
FNSI base plus the physical page offset. Accepted ranges fit the image region
and admitted runtime/profile extent, and different pages do not overlap. The
extent is an admission input, not a hard-coded storage ceiling. This is the
ACL2 addressing seam for eliminating the native by-address hash. Registered
reader extents already include the FNSI base; their relative requests must not
add it again. The physical/controller layer still owns matching request tokens,
short/ambiguous I/O verdicts and cancellation/pin lifetime.

The MKEY column uses the existing salted32-bit FNV over Message-ID characters.
`books/history-key-cursor.lisp` (PRF-1096) supplies a bounded one-byte core and a
resident string client. Initial, residual and terminal refinements connect it
to `fn-hist-hash` and `fn-hp-mkey`; scalar hash domain and progress are preserved.
Cold string spans supply one authenticated source byte to the same core,
without whole-string construction. Capture/root/source-position authority
belongs to the surrounding source cursor. Absent Message-IDs keep the existing
zero key; a present string returns one plus its FNV result. No format changes.
