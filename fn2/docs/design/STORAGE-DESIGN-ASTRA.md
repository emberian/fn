## Attack the recommendation

I would keep the ordered journal, separated immutable payloads, parent-held integrity checks, and materialized folds. I would change the metadata layout, the checkpoint protocol, and several of the claims made for them. The recommendation is a promising architecture; it is not yet a storage protocol a builder can implement without inventing consequential semantics.

References below use these names:

- **Execution**: [build/coordinator/fn2/EXECUTION-MODEL.md](build/coordinator/fn2/EXECUTION-MODEL.md).
- **Study**: [build/coordinator/fn2/STORAGE-DESIGN-ANGLES.md](build/coordinator/fn2/STORAGE-DESIGN-ANGLES.md).
- **Clients**: [build/coordinator/fn2/CLIENTS-AND-DATA-MODELS.md](build/coordinator/fn2/CLIENTS-AND-DATA-MODELS.md).
- **Envelope**: [build/coordinator/fn2/ENVELOPE-AND-HOST.md](build/coordinator/fn2/ENVELOPE-AND-HOST.md).

**1. “The log is the only authority” needs a definition that survives reclamation.**

Study §13 combines an authoritative journal containing small sources, cursor changes, obligations and evidence with expiry that drops old journal extents. These statements are compatible only after specifying what replaces the deleted facts.

A checkpointed index is disposable while the facts needed to rebuild it survive. Once those facts are deleted, the checkpoint contains indispensable information. Calling it a “derived view” does not make it reconstructible.

The correct invariant is:

\[
State = Fold(Summary_k,\ Events_{k+1..n})
\]

with a separate obligation:

\[
Observe(Fold(Events_{1..n}))
=
Observe(Fold(Summary_k,\ Events_{k+1..n}))
\]

for every observation the retained contract permits—including duplicate checks, outstanding obligations, supported historical selections and retry outcomes.

This is D13, not ordinary checkpointing. A storage checkpoint, an application’s signed checkpoint claim, and permission to discard history are three different things. A successful storage checkpoint does not release an archive obligation. Signing a Merkle root does not establish the summary equation.

Kafka’s compacted log makes the distinction concrete: it preserves current keyed state while deliberately allowing intermediate events and eventually tombstones to disappear. fn cannot copy that policy for identities that may be reoffered indefinitely. See `~/paperbin/kafka2026-docs-design.md`, “Log Compaction”; Clients §§2.2.6–8 and 3.1; `~/dev/fn/planning/decisions.md`, D13.

**2. The recovery tables silently narrow the fault model.**

Study §§B.2 and K allow a newer COW root with missing children to be treated as an unfinished commit and replaced by an older root. Under an honest-fence, crash-only model, that can be correct. Under the declared model, it can erase an acknowledged commit.

These two histories can leave identical bytes:

1. A new root lands, a dependency does not, and the process dies before its fence succeeds.
2. The fence succeeds, the client receives acceptance, and the dependency is subsequently lost or corrupted.

A checksum detects the missing dependency. It does not distinguish those histories.

Likewise, “bad final batch, nothing valid afterward” is insufficient evidence for `torn tail`. With acknowledged-write loss permitted, the answer may be `unknown`. A surviving successor, checkpoint or independent receipt can strengthen the evidence to `damaged`.

Four superblocks do not solve this. TigerBeetle’s copies help its root-discovery protocol under its fault assumptions; its replicated recovery machinery supplies additional evidence. Copying the number four does not import that machinery. See `~/paperbin/tigerbeetle2026-internals-data-file.md`; Execution rule 8.

The three assumptions have distinct jobs:

- **A-PERSISTENCE-FENCE** establishes the durability promised by a successful barrier.
- **A-INTEGRITY-EVIDENCE** establishes what matching and mismatching integrity evidence lets us conclude.
- **A-INDEPENDENT-FRONTIER** makes rollback detectable to the extent that an independent witness actually covers the lost frontier.

A checkpoint witness at position 100 says nothing conclusive about an acknowledged position 101 that nobody independently retained.

**3. A Merkle log does not eliminate the need to specify predecessor relationships.**

A stored root commits to some sequence. Recovery still needs to establish:

- which sequence the batch extends;
- which physical predecessor must have existed;
- whether the batch belongs to this history and incarnation;
- where to search after a damaged header;
- which allocation generation its references name.

One can derive prefix extension by replaying the records from an authenticated previous frontier and recomputing the Merkle tree. But that is an algorithm, not a consequence of placing `(size, root)` in a header.

I would retain an explicit previous-batch digest. It serves physical recovery. The Merkle log serves inclusion and consistency proofs over semantic events. Their subjects differ, so neither is a redundant twin.

A signed root also does not prevent a node from showing two clients different extensions of a common prefix. It makes conflicting observations checkable when they meet.

**4. The recommendation’s `install` transition violates the bounded-step model as written.**

Study §13.2 puts column appends, index updates and fold application into `install`. Those operations can involve many records, groups, pages and cache misses.

Execution rule 8 requires one bounded transition to install the complete committed root/frontier. Therefore the new read view must already exist before that transition. Installation swaps a handle; it does not execute the batch’s mutations.

The second prepared batch must be constructed against the first batch’s proposed successor state. Otherwise:

```text
R0: account = 0
A: account := 1
B: unrelated cursor := 9

incorrect: RA = update(R0, A), RB = update(R0, B)
install RA; install RB   => account becomes 0 again
```

The same bug loses article-number allocations, Message-ID reservations and allocator changes. This needs an explicit successor-root construction protocol, not “apply deltas at install.”

**5. The first-slice resident Message-ID index is already ruled out.**

Study §§B, L and 13 repeatedly cite Execution §6 as permitting rebuild-at-open first. The settled document says the opposite: the first served design has a persistent pageable identity index and bounded replay state.

Further, `(tag, sequence)` is not an exact identity index unless the original Message-ID octets remain available. After payload reclamation, probing the old article record is no longer an implementation of exact equality.

Retain the exact Message-ID in permanent identity metadata. A hash or Bloom filter may reject candidates cheaply; neither may decide equality. Store the content identity, original acceptance binding and relevant conflict state alongside it. This is particularly important because Clients §3.3 explicitly preserves collision quarantine rather than treating digest equality as unconditional byte equality.

Bitcask’s resident keydir and hint-file rebuild are useful contrasts, not a first-slice escape hatch. See `~/paperbin/sheehy2010-bitcask-log-structured-hash-table.txt`.

**6. The proposed “small” index metadata still grows with the store.**

Resident fences, filters, manifests, free-set bitmaps, retention-class tails and Merkle frontiers all need their own treatment under rule 9.

Two KiB of fences at one million entries is small. It is still linear growth. A persistent manifest cannot require every run descriptor to be resident. An arbitrary number of groups cannot imply one resident tail buffer per group. A fixed number of LSM levels is another stored-data ceiling.

Use pageable directories and filters, an aggregate active-tail budget, and resumable traversal. The number of simultaneously active merge inputs may be fixed by execution capacity; the number of levels or retained runs may not.

Similarly, `u64` is an excellent common representation, but “585,000 years, therefore no ceiling” is not the ruling Ember gave. Persistent counters need an extensible encoding or explicit extension scheme. Machine-word fast paths must not define the semantic maximum.

**7. “Pins cost zero” hides both a semantic change and retained metadata.**

Study §C correctly notices the distinction between a visibility version and a byte lease. Its conclusion is too broad.

A numeric version still requires the information needed to answer at that version: birth and withdrawal positions, membership history, historical selection metadata, and the relevant view definition. If that information is compacted away, either the pin retains replacement evidence or the query must rebase.

Moreover, permitting later reclamation to turn a previously readable article into `unavailable` changes the connection-isolation claim in Clients §3.4. Replies are then a function of the pinned logical version **and current availability observations**, not solely the connection’s octets and its pinned version. I support that change, but it must be made explicitly.

Three retention mechanisms must stay distinct:

- durable obligations such as `:archive` and `:forward`;
- a logical version used for selection;
- physical storage and memory leases used by an active operation.

For BODY, acquire a storage lease for the selected object before emitting the success status. Lease the small memory window separately. Otherwise reclamation can remove the next block halfway through an already-started response.

A leased 2 KiB article can also strand an entire mixed extent if reclamation operates only at extent granularity. “Space held ≤ article size” requires relocation or subextent allocation; it does not follow from the lease abstraction alone.

**8. The strongest alternatives were compared under weaker designs.**

The COW scorecard charges a BODY reader for retaining the whole database root for 68 minutes, even though Study §C itself describes selecting under a short root pin and streaming under object leases. The uniform LSM row is similarly charged for physical table snapshots.

A logical historical query can instead read the current physical layout, using version-stamped entries and a stable resume key. Compaction must preserve those logical answers, but need not preserve every old table.

The recommendation should receive credit for that separation. So should its alternatives.

Likewise, uniform LSM storage does not require bodies to pass through a WAL and then be rewritten into tables. Study §A.1 already identifies direct blob dependencies as an alternative. TigerBeetle’s LSM documentation also describes moving nonoverlapping tables between levels by changing metadata, without rewriting values. See `~/paperbin/tigerbeetle2026-internals-lsm.md`, “Compaction Move Table.”

Postgres contributes more than a deliberately expensive strawman: WAL separates commit latency from home-page writeback; HOT coalesces some hot-row costs; visibility maps enable index-only reads; TOAST separates large values. I would not build its complete recovery and MVCC machinery here, but those costs are not universal properties of pages. See the `postgresql2026-docs-{storage-hot,storage-vm,storage-toast,wal-intro}.txt` files in `~/paperbin`.

**9. Several numbers need correction or a narrower scope.**

| Claim in the study | Correction |
|---|---|
| ~40 B per ack, ~8 MB/day | That is logical delta volume. At 210,000 isolated durable acks/day, one 4 KiB journal unit per ack is **860 MB/day**, before checkpoint and filesystem amplification. Shared flushes help only when operations actually overlap or deliberately wait. |
| ~30 ms recovery from a 64 MiB tail | This is approximately the sequential transfer time at 2 GB/s. It excludes decoding, hashing, index reconstruction and dependency reads. A small log record can reference a 16 MiB object; bounding journal bytes does not bound dependency-verification bytes. |
| ~1.3 merge passes per entry at fanout eight | Fanout and final population do not determine this. Initial run size, compaction policy, partially populated levels and overlap are missing. |
| 4,096 sixteen-byte entries per 64 KiB block | That is the headerless quotient. Headers, integrity metadata and restart/fence information reduce capacity. Exact keys require additional retained bytes. |
| Five reads for 1,000 overview rows | Approximately five **64 KiB data reads** at 300 B/row, before directories and run overlap. It is not five 4 KiB reads. |
| Overview reclustering adds ~0.12× | This assumes one 300 B representation per article. At 1.5 memberships, duplicating a complete overview per membership contributes about 450 B/article, approximately **0.18×** against a 2.4 KiB record, before merge overhead. |
| COW’s ~18× means it “fails” | The arithmetic follows the chosen page-update scenario. Whether it fails depends on actual dirty paths, batch sharing, page size and the performance requirement. At the first client’s rate, flush latency may dominate either design. |
| LFS cleaning cost is `2/(1-u)` | Sprite’s figure counts **reads plus writes**. Survivor bytes written per newly freed byte are `u/(1-u)`; total writes including new data are `1/(1-u)`. Keep these denominators separate. |
| SQLite WAL does not handle large transactions well | The quoted warning is obsolete, struck-through text on the source page. SQLite documents the change since 3.11.0. |

Sources: Study §§A–G; Envelope §1; `~/paperbin/rosenblum1992-design-implementation-log-structured-file-system.txt`, §3.4; `~/paperbin/sqlite2026-docs-wal.txt` and the [SQLite WAL documentation](https://www.sqlite.org/wal.html).

The ~1.9×/~1.3× recommendation totals also omit enough machinery that I would not use them to choose a winner: exact identity storage, persistent directories, checkpoint roots, allocator metadata, proof material and cold-tail maintenance all need accounting.

**10. BLAKE3 range verification is feasible, but the format description is incomplete.**

An internal BLAKE3 chaining value is not an ordinary BLAKE3 digest of the block. Chunk counters, tree shape, final length and `ROOT` processing matter. A flat list of subtree values needs a specified reconstruction algorithm; partial final blocks and objects smaller than one block need explicit cases. The [BLAKE3 reference implementation](https://github.com/BLAKE3-team/BLAKE3/blob/master/reference_impl/reference_impl.rs) distinguishes chaining values from root output.

More importantly, the authored source’s content identity should not include a node’s allocation address or generation. Physical page integrity should bind those fields. Consequently, one hash tree cannot automatically replace both contracts.

I would use BLAKE3 range-proof material for portable source verification and a separate physical hash for storage pages. The additional hashing is a real cost. Tahoe is instructive precisely because it distinguishes different integrity subjects and commits to encoding parameters and length; see `~/paperbin/wilcoxohearn2008-tahoe-least-authority-filesystem.txt`, §4.3, and `tahoelafs2026-docs-file-encoding.rst`.

**11. “Only an honest flush is required” is too strong.**

The design also needs exclusive writer ownership, a declared write-damage radius for its crash-only argument, correct completion/borrow handling, valid addressing, and a way to establish file growth and namespace durability when those occur.

SQLite’s powersafe-overwrite documentation explicitly distinguishes collateral damage from atomic writes and states that SQLite normally does **not** assume atomic database-page writes. Study §J’s characterization of SQLite should be corrected. See `~/paperbin/sqlite2026-docs-psow.txt`.

None of this justifies rejecting ZFS, Btrfs, buffered I/O or a raw device. It specifies what claims each backend can support. An I/O error after persistence has become ambiguous enters `uncertain`; it is not converted into “refused, nothing stored.”

## The five decisions with your rulings

These answer Study §14.2.

**1. Unit of state: one semantic event history, represented by a retained prefix summary plus suffix.**

Mutable keyed objects are supported as folds. Their updates are typed operations in the same commit stream as articles and obligations. There is no independently committed mutable store.

For a keyed operation, persist its principal and operation identity, expected prior version where relevant, resulting mutation, and stable outcome. Admission and sealing check against the ordered proposed state, including earlier operations in the batch and its unresolved predecessor. A repeated operation returns its recorded outcome; it does not execute again.

Coalescing is permitted only when it preserves every promised result. Two successful cursor advances may share one final cursor value, but their retry identities cannot disappear merely because the value was coalesced.

An ordinary checkpoint changes representation. Discarding semantic history requires an identified sufficient-summary rule. Initially, retain exact identity and obligation evidence; compact latest-only internal state only where its contract permits that.

**2. Pinned versions: stable selection and identity; payload availability guaranteed after selection acquires a lease.**

I choose Study §C’s option (a), with three qualifications:

- Historical metadata needed by supported pins remains available.
- A reply acquires its object lease before promising to stream the object.
- The reference semantics explicitly includes availability and view-change/rebase outcomes.

A connection does not retain every body it might someday request. A selected BODY retains its object’s backing storage, while only a bounded window occupies the byte pool. Durable retention obligations remain stronger than this read lease and survive process death.

For long XOVER selections, retain the logical version and last emitted key. Re-seek in the current physical index after yielding. Do not hold an old LSM manifest or COW root across network stalls.

**3. Retention placement: classes are placement hints, with one default class.**

Place payloads with similar expected lifetimes together. Support operator-defined classes without requiring one resident buffer per class. Crossposts initially use the longest applicable retention expectation.

The authoritative release predicate remains:

```text
all applicable retention requirements discharged
and every independent durable obligation released
and no active storage lease requires the allocation
and recovery no longer requires the old allocation
```

Class membership is not release evidence. A live policy change can make an old extent contain survivors; the cleaner moves those survivors through the commit protocol.

Keep event/control metadata independently retainable from payloads. If small sources initially share journal sectors with metadata, reclamation must copy the retained metadata before those sectors can be reused.

**4. Integrity commitment: a Merkle event log from the first format, plus physical predecessor links and parent-held page hashes.**

Sign a typed checkpoint claim containing at least:

```text
history identity
history incarnation
semantic event count and Merkle root
fold/schema identity
summary commitment
exact-identity commitment
checkpoint descriptor commitment
signing-key identity
```

A bare `(size, root)` is insufficient for the checkpoint-substitution contract in Clients §1.2.

Keep the physical batch chain separate. A maintenance-only batch advances physical commit order without inventing an application event.

A checkpoint signature attests to the named claim. It does not prove correct folding, current availability, worldwide non-equivocation or freshness beyond the witness’s coverage.

**5. Sealed streams: yes, as opaque client-encrypted content with an explicit public envelope.**

The storage layer stores, authenticates and transports ciphertext. It does not own decryption keys or silently index decrypted content.

The envelope may expose Message-ID, signer, stream, size and whatever public threading or subject fields the application deliberately supplies. Thus encryption does not inherently eliminate every overview field or thread relationship; it eliminates server access to fields placed inside the ciphertext.

This is compatible with fn’s “encrypt before signing” position. It does not create a new cryptographic group-management protocol. Tahoe’s verify/read distinction is useful here, but Tahoe’s time-expiring leases must not replace fn’s evidence-gated obligations. See `~/paperbin/tahoelafs2026-docs-architecture.rst`, “Leases, Refreshing, Garbage Collection.”

## The concrete storage format and root-selection algorithm with recovery invariants

I propose an **ordered event journal with separated payloads and one pageable ordered-run engine for metadata**. The engine serves identity, article metadata, overview, mutable folds, obligations and location mappings. Different schemas have different merge rules; they share page encoding, directories, caches, merge machinery and installation.

This removes the recommendation’s separate commit-order overview layout and later reclustering subsystem. Overview enters the ordered engine under `(group, article-number)` from the beginning.

The following is the proposed format and protocol, rather than a claim that these mechanisms already exist.

**A. Identities, order and basic encoding**

Keep these quantities distinct:

| Name | Meaning |
|---|---|
| `history_id` | Logical history identity |
| `history_incarnation` | An explicitly created lineage incarnation; not changed merely by restarting |
| `writer_epoch` | Durably established epoch before a process issues ordinary storage writes |
| `commit_no` | Physical batch order, including maintenance |
| `event_no` | Semantic event order |
| `article_id` | Article identity within the node |
| `group_number` | Nonreused number within one group |
| `checkpoint_no` | Checkpoint installation order |
| `allocation_id` | `(writer_epoch, allocation_counter)` for one physical allocation |

A clean restart preserves history identity and incarnation. An explicit restore or fork must establish its lineage and cursor semantics; a new incarnation is not a device for concealing lost acknowledged history.

Encoding:

- Octets are octets; strings are length-prefixed octet sequences.
- Tags and format versions have specified byte values.
- Persistent counts, identifiers and lengths use canonical unsigned base-128 integers: shortest encoding, no redundant terminal zero group.
- Numeric ordering is numeric ordering, not lexicographic ordering of that encoding.
- Large fields and records may span fragments. Decoding, comparison and arithmetic are resumable.
- Common values use word-sized fast paths. Overflow continues through the extensible representation.
- All padding is zero and covered by integrity checks.
- Unknown required types or malformed encodings produce a named format failure; they are never skipped as if absent.

Page size `P`, append/damage-isolation unit `S`, extent geometry and filter parameters are format parameters. The initial choices can be `P = 64 KiB` and `S = 4 KiB`; neither fixes the number of stored objects or tree levels.

The bootstrap has a fixed magic/version prefix and an authenticated geometry descriptor locating four anchor slots and the initial storage domain. Fixed bootstrap framing is format geometry, not a namespace ceiling. Reads and writes of it obey the backend’s alignment requirements.

**B. Physical references and pages**

A physical reference is:

```text
Ref = (
  storage-domain,
  physical-unit,
  allocation-id,
  page-kind,
  encoded-length,
  expected-hash
)
```

The expected hash is held by the parent. An allocation’s identity changes whenever its space is reused.

A structured page is encoded as:

```text
magic, format-version, page-kind
history-id, history-incarnation
physical-unit, allocation-id
header-length, payload-length
schema-specific header
payload
zero padding
```

Its physical hash is:

```text
BLAKE3("fn2/physical-page/v1" || exact encoded page bytes)
```

A read must match both the expected hash and the expected identity fields. A valid page from another location or allocation generation is not accepted.

Raw source blocks may devote the entire block to source bytes. For these, the parent supplies the identity fields, actual length and logical source offset, and the physical hash covers that context plus the padded block bytes. This preserves full-size streaming blocks without pretending that their content digest authenticates allocation metadata.

Page kinds include:

- ordered-run data;
- ordered-run index;
- partitioned filter;
- manifest/directory;
- allocation map;
- source manifest and range-proof material;
- checkpoint descriptor;
- Merkle-log nodes.

Directories are themselves pageable trees. There is no resident entry per page, run, group or free block.

A run-data page contains a schema identifier, ordered entries and an offset directory. An entry contains a typed key, logical version where needed, value kind, and inline value or checked reference. Internal index pages contain separator keys and child references. Large entries use checked continuation objects.

Filters are negative-probe accelerators. They are published only with the exact run they summarize. A filter cannot substitute for exact comparison or establish that an incompletely searched index is absent.

**C. Semantic records and metadata schemas**

A semantic record has this framing:

```text
record-kind, schema-version
event-no
principal / operation identity, where applicable
typed fields
```

An article-acceptance record includes:

```text
article-id
exact Message-ID octets
algorithm-tagged authored-source identity and source length
authored-source descriptor
node-local projection descriptor
membership assignments: (group-id, group-number)
acceptance/configuration references
durable charges and created obligations
operation outcome
```

Long membership lists and projections are external immutable records, processed incrementally. Their size is governed by the operator profile.

Other record kinds include cursor advancement, registration changes, configuration changes, withdrawals, obligation creation/release, and explicitly supported keyed mutations.

Physical maintenance records include allocation, relocation, run replacement, retirement and checkpoint installation. They advance `commit_no`; they need not advance `event_no`.

The first metadata schemas are:

| Key | Retained value |
|---|---|
| exact Message-ID | Article binding, content identity, acceptance and conflict state |
| article-id | Source/projection descriptors, birth position, withdrawal history, membership descriptor |
| `(group-id, group-number)` | Article-id, visibility metadata and overview |
| `(table-id, object-id)` | Latest-only mutable fold value and version |
| `(principal-id, operation-id)` | Recorded outcome for its declared retry lifetime |
| obligation-id / range | Independent obligations and release evidence |
| logical object identity | Current physical placement |
| physical allocation | Ownership, generation and allocation state |

Compaction preserves logical historical reads where those are supported. It may discard obsolete versions of latest-only mutable state. It may not discard an identity binding because its body expired.

The permanent Message-ID entry contains the exact bytes. A compact fingerprint may precede it in a page or cache; it is not the key’s meaning.

**D. Source blocks and portable integrity**

Store the authored source independently of injected headers and physical placement.

For a large source:

1. Stream source bytes into bounded pool windows.
2. Compute its ordinary content identity incrementally.
3. Write immutable source blocks.
4. Build a paged source manifest containing ordered offsets, lengths, physical references and BLAKE3 range-proof material.
5. Commit the article record only after all required writes have completed and the batch’s durability protocol succeeds.

The range-proof construction follows BLAKE3’s actual chunk tree:

- chunks use their absolute source chunk counters;
- internal nodes use the specified parent operation;
- final-root verification uses `ROOT` processing;
- final length and partial last chunks are checked;
- a source no larger than the requested block is verified as the whole source.

The manifest must support constructing the sibling evidence needed to verify a requested range against the ordinary source digest. A peer supplying an arbitrary manifest cannot establish that binding merely by putting the desired digest in its header.

Physical page hashes remain separate. Relocating bytes changes physical references and hashes without changing authored-source identity.

Small sources can remain inline in journal frames. Before reclaiming such frames, copy any still-required source or metadata into new allocations and commit the new placement. No committed record is edited in place.

**E. Journal frames, batches and the two roots**

Journal space is allocated in extents, but written in fresh `S`-sized frames. An acknowledged frame is never partially filled by a later batch.

Each frame carries:

```text
magic, frame-kind
history-id, history-incarnation
writer-epoch, commit-no
journal-extent allocation-id
frame ordinal and fragment offset
payload length
payload
padding
frame hash
```

The frame hash covers the complete frame with its hash field zeroed. Physical location and allocation identity are part of the covered context.

A sealed batch contains:

```text
commit-no
previous commit-no and previous seal hash
input root identity
semantic event interval
record stream and record-stream commitment
new dependency manifest
allocation / retirement deltas
metadata-manifest edits
output root recipe
event Merkle frontier after the batch
final seal hash
```

The final seal commits to all framing, lengths, records, dependencies and root-recipe fields. Its own hash field is zero while hashing. The output recipe does not include its own seal hash, avoiding a circular definition; the completed seal hash becomes the batch/root identity.

A root recipe identifies:

- the materialized checkpoint base;
- the ordered committed suffix to apply;
- physical manifest and allocation changes;
- the event frontier and relevant configuration generations.

It need not contain freshly written index pages for every ordinary commit. The bounded committed suffix is indexed in memory and is reconstructible from the journal.

The event Merkle tree has domain-separated leaves and internal nodes, commits to canonical semantic records, and uses an explicitly specified append-only binary-tree shape. Its frontier and proof nodes are paged when necessary. Physical relocation does not change an event’s leaf.

For two batches:

```text
RA = Apply(R0, A)
RB = Apply(RA, B)
```

`B` may prepare while `A` is in flight. It sees `A`’s proposed identity reservations, numbers, charges, configuration and allocations. It cannot independently decide against `R0`.

Before sealing, build the complete read-visible successor overlay, including every lookup needed to observe the new state. Reserve its memory and installation resources before accepting the batch into this phase.

The baseline imposes this order:

1. `A` prepares, seals and writes dependencies.
2. `A` writes its journal frames.
3. All those writes complete.
4. A covering fence completes successfully.
5. One bounded transition installs `RA`.
6. `B` may submit its journal frames only after `A`’s fence succeeded.
7. `B` eventually installs `RB`.

`B` may stream independent dependencies earlier, into disjoint reservations. It cannot publish past an uncertain `A`.

This restriction also gives a valid successor seal evidentiary value: its predecessor had passed a successful fence before that seal could be submitted.

Installation is a root-handle/frontier swap. Applying thousands of deltas is preparation or subsequent materialization work, never the atomic installation step. Readers consult the complete installed overlay until materialization absorbs it.

Reply and notification obligations transfer to reserved outcome/notification state. They do not keep either commit slot occupied until every client reads its reply.

**F. Checkpoint installation and anchor updates**

A checkpoint is an ordinary ordered maintenance batch.

For the first implementation, take its cut at the predecessor’s installed root. Freeze that root’s materialization generation and construct:

- immutable runs for the bounded committed tail;
- a complete pageable metadata manifest;
- the allocation-state root;
- retained event/proof directories;
- the event frontier;
- the next journal recovery arena.

Later batches may collect while this work proceeds, but do not commit across the checkpoint batch. Reads, uploads and other bounded machines continue running. This is a deliberate first implementation tradeoff: checkpointing can add commit latency. Do not claim the ordinary one-flush latency bound during it.

Reserve the checkpoint’s metadata allocations before constructing its allocation map, including space for the map itself. Unused reservation space is released later. This avoids a free-map self-allocation cycle.

Commit the checkpoint through:

```text
dependencies → journal-write → fence → durable → install
```

**Only after that fence succeeds** may the anchor writer submit a locator for the checkpoint.

Use four fixed anchor slots as two banks of two. Each anchor contains:

```text
slot identity
history-id and incarnation
checkpoint-no
checkpoint batch identity
checkpoint descriptor Ref
previous checkpoint identity
geometry identity
anchor hash
```

To advance:

1. Preserve the current bank.
2. Write both slots of the other bank with the new checkpoint locator.
3. Wait for both writes and a covering fence.
4. Mark the new bank promoted in execution state.
5. Permit later retirement transactions to release storage needed only by the old checkpoint.
6. Alternate banks at the next checkpoint.

The extra anchor fence is amortized checkpoint work, not a per-article fence.

A valid new anchor is evidence that its checkpoint batch was already fenced **before the anchor write was issued**. Therefore a valid anchor whose required checkpoint data is missing is evidence of damage under the declared contracts, not an ordinary half-written checkpoint.

A lone newer anchor is investigated. It is not ignored just because an older generation has two copies.

**G. Finding the journal tail without trusting a broken next pointer**

Each checkpoint contains a checked directory of the extents authorized for journal use after that checkpoint: the **recovery arena**. Entries include physical locations and allocation identities.

Journal writes must stay inside that arena until a committed checkpoint supplies its successor arena. Arena capacity is an execution/recovery-backlog setting. Filling it backpressures commits; it does not cap retained history.

Recovery scans every frame position in the relevant arena. It does not stop at the first malformed frame, trust an unchecked length to skip ahead, or search only through a next pointer stored in the damaged batch.

A valid checkpoint encountered during replay introduces its successor arena. If anchor promotion has not completed, the predecessor checkpoint and all journal material needed to reach that transition remain protected.

This gives bounded normal tail discovery without requiring a scan of the entire data file. Scanning all storage remains a repair procedure.

**H. Allocation, retirement and writer epochs**

The allocator is a pageable map with explicit states:

```text
FREE
RESERVED
ALLOCATED(owner, allocation-id)
RETIRE_PENDING(retirement-commit)
```

Reservations cover both prepared batches, streaming uploads and maintenance. The allocator never supplies a block protected by any current root, required recovery base, proposed successor or outstanding borrow.

An ordinary release follows this sequence:

1. Commit the logical release or replacement location.
2. Mark old allocations `RETIRE_PENDING`.
3. Install and promote a checkpoint that no longer needs the old allocations for recovery.
4. Wait for all storage and external I/O leases to end.
5. Commit `RELEASE_ALLOCATION`, making the allocations free.
6. Reuse them only afterward, with new allocation identities.

This costs more than “the free bitmap says zero.” It provides a recoverable reason for reuse.

On recovery:

- Start with the selected checkpoint’s allocation map.
- Replay exact allocation, relocation, retirement and release deltas.
- Keep checkpoint and journal infrastructure protected.
- Treat allocations of unresolved candidates as quarantined.
- Return orphan speculative allocations to free space only after candidate selection is settled and old I/O can no longer reach them.

Do not overwrite surviving speculative blocks merely because a replay would allocate the same addresses. TigerBeetle’s deterministic replay depends on its complete allocation protocol; determinism alone does not justify that overwrite.

Before ordinary writes after startup, commit a `BEGIN_WRITER_EPOCH` maintenance batch. No object writes for that epoch are issued before its fence succeeds. If recovery finds a complete such batch, it adopts it and chooses a later epoch. If the epoch record tore before durability, the protocol ensures that no ordinary writes from that epoch had escaped.

Within an epoch, allocation counters never repeat, including after cancellation. A rollback of the entire epoch evidence has the same independent-frontier limitation as rollback of the history itself.

Process death ends process-local leases only after the backend establishes that old submitted writes can no longer complete into reused storage. An in-process timeout is not that evidence.

**I. Root-selection algorithm**

Recovery performs the following steps as resumable core work.

1. **Read bootstrap and all anchor slots.** Validate framing, slot identity, geometry, history/incarnation and hashes. Retain evidence of invalid or contradictory slots.

2. **Enumerate checkpoint candidates.** Include every structurally valid anchor target, including a newer singleton. Compare checkpoint identities and predecessor relationships, not wall clocks.

3. **Validate candidate descriptors.** Check their expected hashes, batch bindings, history identities, event frontiers and recovery-arena directories. A damaged newer candidate is not erased from consideration by finding an older valid one.

4. **Discover the tail.** Scan the permitted arenas independently of damaged batch lengths. Group verified frames by allocation identity, writer epoch and commit number. Reconstruct complete seals and partial candidates.

5. **Construct the ordered chain.** Require exact predecessor hashes and successive commit numbers. Reject unexplained branches, gaps, duplicate physical identities and incompatible before/after root recipes.

6. **Replay into a private recovery view.** Apply complete batches in order. Verify canonical event encoding, Merkle extension, operation identities, exact identity decisions, allocation transitions and maintenance preconditions. Do not publish partial replay.

7. **Resolve the terminal candidates.** A complete, valid final batch may be adopted even if its original reply was never sent. A final batch with missing dependencies is not automatically discarded. Classify it using the fault profile and surviving frontier evidence.

8. **Check independent evidence.** A trusted receipt or checkpoint naming a later or incompatible committed frontier prevents selecting a shorter history as normal recovery. A witness is a lower bound unless its protocol supplies stronger information.

9. **Establish durability before resuming mutation.** Recovery must not turn bytes merely observed through a failed-write cache into a durable acceptance claim. Use a backend recovery contract that establishes stable reads, or reissue the validated tentative data and journal representation to fresh protected allocations and fence them. Simply retrying the failed `fsync` is insufficient.

10. **Install once.** Install the selected complete root/frontier, establish the writer epoch, and release notifications incrementally. Damaged or unresolved histories remain fenced where their uncertainty affects decisions.

The algorithm chooses the newest **established compatible history**, not the newest checksum-valid sector and not the oldest conveniently readable checkpoint.

An older checkpoint may be used as a replay base to reconstruct the same newest history. That is different from rolling the history back.

**J. Recovery invariants and the four classifications**

These invariants are checked at the boundaries where their evidence is consumed:

| Invariant | Required evidence |
|---|---|
| **Framing** | Canonical encodings, bounded fragment processing, valid lengths and ordinals, complete seal, checked padding |
| **Lineage** | Matching history/incarnation; writer epochs introduced by the protocol; no unexplained fork |
| **Order** | Exact predecessor seal, successive physical commits, correct semantic event interval and Merkle extension |
| **Reference integrity** | Every accessed child matches the expected type, address, allocation identity, length and hash |
| **State transition** | The batch applies to its named predecessor; identity, numbering, cursor and obligation rules hold |
| **Allocation** | No conflicting live ownership; allocation and release transitions legal; no free/reachable overlap in the represented state |
| **Checkpoint cut** | Materialized state represents exactly the named cut; replay begins at the next batch |
| **Retirement** | Every removed required edge has a committed replacement or authorized release; recovery protection precedes reuse |
| **Frontier evidence** | No surviving trusted evidence contradicts the selected history |

The classifications are:

| Class | Evidence and required behavior |
|---|---|
| **`intact`** | A unique compatible selected chain passes the applicable checks, and no surviving evidence contradicts it. Report its frontier and the integrity scope checked. Under the declared persistence assumptions it is the recoverable committed state. |
| **`torn tail`** | The established prefix is intact; the defective suffix is confined to permitted terminal writes; there is no valid successor proving a later fence; and the fault profile or authoritative evidence establishes that the defective suffix need not contain acknowledged history. Only that suffix may be discarded. |
| **`damaged`** | Evidence establishes that required data is missing or inconsistent: for example, a valid successor requires a missing predecessor, a valid post-fence anchor names a bad checkpoint, an independent receipt requires a lost batch, or a selected committed page fails its parent’s hash. Preserve the frontier claim and seek repair; do not relabel the shorter readable prefix as the recovered history. |
| **`unknown`** | The evidence cannot distinguish incomplete work from lost acknowledged work, cannot order competing candidates, cannot authenticate the required lineage, or cannot establish the needed reads. Preserve candidates and fence dependent mutation. |

A damaged page and an unknown frontier can coexist. Record the affected range and evidence, not merely one global adjective.

There are two necessary scope qualifications:

- **No constant-time open proves the entire device intact.** Normal open checks root/control state and the replay it performs. Payload and cold-index integrity is checked on access and by incremental scrub. A full-store `intact` claim requires a full relevant scan.
- **No local format detects complete rollback without surviving independent evidence.** If every local byte is restored to an older coherent image, checksums and signatures stored in that image still verify. The recovery report must expose witness coverage; the theorem must retain `A-INDEPENDENT-FRONTIER`.

For the broad fault profile, an unexplained bad final batch is therefore `unknown`, not automatically `torn tail`. This is the central correction to Study §B.

ARIES supplies a useful discipline here: correlate persisted page state with logged progress and make repeated recovery itself recoverable. Its analysis/redo/undo machinery is unnecessary when uncommitted updates never overwrite required pages. See `~/paperbin/mohan1992-aries-recovery-method.txt`, opening description and restart-recovery discussion. FoundationDB likewise separates durable log order from storage materialization, but its recovery frontier depends on coordinated replica evidence that a single fn node does not possess: `~/paperbin/zhou2021-foundationdb-unbundled-transactional-kv-store.txt`, §§2.4.3–2.4.4.

## The counter-design and what you would build

The strongest counter-design is a **checksummed COW metadata tree, separated immutable payloads, and the same semantic event journal**.

It uses exactly the same:

- history and operation identities;
- source-block format;
- batch seals and durability protocol;
- logical visibility versions;
- object and memory leases;
- recovery classifications;
- retention and allocator rules.

The difference is physical materialization. Each batch writes fresh metadata paths and installs their root, rather than accumulating bounded deltas and flushing sorted runs.

This is considerably stronger than Study’s LMDB-shaped row:

- BODY readers retain object leases, not database-wide root snapshots.
- Large sources need not occupy contiguous overflow runs.
- Events remain available for consumers and peers.
- Parent-held hashes detect stale and misdirected pages.
- Path copies are shared within a batch.
- Range deletion can detach subtrees where semantic retention permits it.
- Page size is chosen for this workload.
- Root selection does not silently fall back after evidence of acknowledged damage.

Its advantages are substantial: one navigable index structure, fewer read candidates, no run-merging policy, and less replay at ordinary open. The old fn page-store theorems are relevant experience, though they do not establish correctness under the new fault model or composed execution protocol.

Its main cost is writing changed metadata paths for every commit. The relevant measurement is distinct dirty pages per batch, including the allocator—not “three pages per key” multiplied indiscriminately. At the initial fleet’s rate, it may be perfectly adequate. I would keep it as the comparison implementation.

**I would build the ordered journal plus shared ordered-run metadata engine described above.**

The reasons are concrete:

1. The first workload has many more cursor acknowledgements than articles. A logical delta journal permits immediate durable acknowledgement while coalescing repeated metadata changes before writing their materialization.

2. Message-ID and operation-identity histories grow independently of resident memory. Sorted immutable runs provide a direct persistent representation without copying random metadata paths for each insert.

3. Group-number and overview keys are naturally ordered. Cluster them from their first materialization. There is no need for a separate “global overview now, per-group overview later” format.

4. The same machinery can serve current folds, exact identities and versioned article metadata. This is fewer physical mechanisms than the proposed combination of columns, number chains, a special overview reclusterer, sorted-ID runs and mutable-table checkpoints.

5. Payloads are written directly to their final immutable storage, with journal references. They do not pass through LSM compaction.

The price is explicit: run overlap, compaction reservations, transient input/output space, filter/index reads, and checkpoint work. The system must apply backpressure before maintenance debt exhausts its reserved capacity. A maintenance calendar share is not itself proof that the allocated bandwidth can sustain admission.

The relevant precedent is not “TigerBeetle, therefore correct.” It is the combination of incremental reserved compaction from `~/paperbin/tigerbeetle2026-internals-lsm.md`, WAL/materialization separation from the FoundationDB paper, value separation, and RocksDB’s explicit tradeoff between write, read and space amplification in `~/paperbin/dong2021-rocksdb-evolution-development-priorities.txt`. RocksDB’s reported SST write amplification excludes WAL writes; fn’s comparison must include them.

I would retain Study’s seven measurements, with these changes:

- **M1:** Compare the proposed shared-run engine against the corrected COW design using identical payload placement, integrity and retention semantics. Count journal padding, metadata, allocator, anchors and cleaning separately.
- **M2:** Include cold, sparse groups whose recent entries have already exceeded cache capacity. Charge directory and overlapping-run reads.
- **M3:** Test exact Message-ID lookup after original bodies and journal placements have been reclaimed. A resident hash is a cache control, not an eligible first-slice architecture.
- **M4:** Report disk space stranded, object storage leased, pool memory borrowed and historical metadata retained as separate quantities.
- **M5:** Test both correlated thirty-consumer bursts and isolated durable acks. The difference between forty logical bytes and one physical append unit matters.
- **M6:** Include two prepared batches, an interrupted checkpoint, a newer singleton anchor, corrupted final-batch dependencies, an independent later receipt, stale reused blocks and a crash during recovery. Measure dependency verification separately from journal scanning.
- **M7:** Keep the filesystem experiments, but publish the observed barrier/alignment behavior and costs without platform refusal logic.

The decisive first-slice demonstration is this: a checkpoint or relocation occurs while two successive batches are prepared, a cold BODY is leased, a cursor ack commits, and expiry attempts to reuse space. Kill the process at every write/fence/install boundary. Recovery must preserve every established promise, identify genuine ambiguity, and never reuse storage still required by the selected history or an outstanding borrow.

That is the storage design I would build: one semantic history, one ordered commit protocol, one shared metadata engine, explicit physical generations, and recovery that distinguishes what the bytes prove from what we merely hoped happened.