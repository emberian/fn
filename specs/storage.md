# Persistent storage

Status: specialized storage direction agreed. The actual immutable-file Store,
record/replay codecs and live file/node composition are implemented with scoped
proof and fault evidence; see the [refinement contract](store-refinement.md).
Final segment/checkpoint layouts, complete byte/host correspondence and platform
qualification remain open under D06–D09/D14. The separate isolated-slot
`books/journal.lisp` experiment is not the running adapter model.

## Authority and layout

The proposed backend uses append-only object segments, a transaction journal,
and versioned checkpoints. Segment locations and index layouts are local.
Portable objects do not reference filesystem paths or physical offsets.

STO-001: committed journal/checkpoint state is authoritative. Lookup indexes are
derived from it. Rebuilding an index preserves the same committed mappings.
If an index answers a range query, validate completeness as well as correctness of
returned entries; validating individual object hashes does not prove no entries
were omitted. An externally implemented index is part of the trust boundary until
a suitable correspondence/checking argument exists.

Proposed on-disk roles, not a frozen directory ABI:

```text
objects/       active and sealed object segments
journal/       transaction generations
checkpoints/   committed model snapshots and their journal frontiers
staging/       bounded incomplete transfers and transaction input
indexes/       rebuildable lookup/search structures
```

Store profile. The metadata frame `config.json` (FNSM, books/byte-store-frame.lisp)
bounds the work of opening a store before any configuration record is replayed:
the transaction-namespace observation (`fn-profile-txn-observation`), the
aggregate replay input (`fn-profile-replay-within-boundp`) and the per-record
publication ceiling. Since D27 its values are the operator's (format
`fn-store-8`: transactions, history octets, record octets, article octets,
groups per article, group-name octets, open suffix and five namespace counts,
docs/operator.md), set at `init` by flags and validated by the relations of
`fn-bs-profile-validp`; ACL2 fixes no value except the codec ceilings above
them. A format-7 store runs under its translation until it is upgraded. It is
written by `init` and changed only offline, by the profile upgrade (`operator
CONFIG store upgrade-profile [PRESET] [--FIELD N ...]`,
books/store-profile-upgrade.lisp): ACL2 admits only an upgrade
(`fn-profile-upgradep`: a valid profile, no field smaller; the format 7 to 8
step is the case of equal fields, `fn-profile-upgrade-format-7-to-8`), and
each gate above is monotone under one, so a store valid under the old profile is
valid under the new one and replays to the same state (replay takes no profile).
The write is the byte program `fn-bs-profile-program`
(books/byte-store-profile-program.lisp), whose crash images name the old frame or
the new one at every cut. This is a local-policy choice of fn; no RFC governs it.

STO-015: a namespace the store holds is bounded by the operator's profile,
never by a constant (D27). Configuration generations and AUTHINFO
credentials are bounded by the profile's `max-config-generations` and
`max-credentials` (format 8 fields 11 and 12, read through
books/store-profile-namespace.lisp). The writer refuses exactly past the
bound, by name (`:max-config-generations`, `:too-many-credentials`), and
the reader admits every namespace within it: the configuration listing
(`fn-nco-observe`) and the credential loader (`fn-native-auth-load`). An
upgrade never lowers a count (`fn-profile-upgrade-keeps-namespace-counts`),
so a namespace written under the old profile is admitted under the new one.
The credential file's octet and line bounds follow its count: 512 octets and
8 lines per credential, plus one unit for the header, a work bound per
credential. fn.toml's size bounds stay constants. They bound the work of
reading a fixed-schema file that names the store, and the file holds no
collection. Consumers, BP rows and policy members are not yet read from the
profile (planning/evidence/bounds-profile-2026-09-25.md).

STO-013: a record's sequence, transaction ID, generation, charge and stamp
are u64 (design 2026-09-25-bounds §2.3, packet P6). A record that needs a
field above 2^32 - 1 carries schema octet 2 and eight-octet CBOR uint heads
(RFC 8949 §3.1); every other record keeps its schema-0 or schema-1 octet and
its bytes, and a store written under schemas 0 and 1 opens to the same
records (`fn-record-v1-bytes-decode-identically`,
`fn-record-v1-bytes-are-their-translation`). A profile's record bound R is
checked against the record ceiling at the widths the runtime produces (u32
heads, 1 083 octets of fixed overhead), so a format-8 profile saved before
P6 is admitted unchanged (`fn-bs-profile-v1-valid-stays-valid`); a schema-2
record is at most 28 octets past that ceiling and the publish gate refuses
it. The frontier and the profile's T field still cap transaction IDs at
2^32 - 1. The widths are a stronger fn guarantee; no RFC requires them.

STO-002: acceptance publishes one transaction containing the source references,
duplicate-history effects, all local group allocations, and any obligations or
reservations accepted in that operation. No partially committed cross-post or
promised-but-unaccounted retention can become visible.

## Commit protocol

The semantic phases are:

1. Validate against committed state; reserve resources and stage an identified
   transaction. The proposal is not yet visible to readers.
2. Make all referenced object bytes and their required namespace reachability
   durable according to the platform contract.
3. Make the transaction's complete commit record durable.
4. Publish the committed state and generate the protocol/application success.

STO-003: successful acceptance is emitted only after the corresponding durable
commit result. Host completion events name the transaction and generation; stale,
duplicate, or unrelated completions cannot publish another transaction.

Only one shared-state commit is in flight initially. Network input may continue
within quotas. A disconnected requester does not cancel an already durable
transaction. If it retries, history prevents repeated allocation/effects.

STO-004: a known abort and an indeterminate I/O result are distinct. After an
indeterminate result, fence shared-state mutations and recover before continuing.
Do not assume an error means nothing reached disk. It is valid for an unacknowledged
transaction to appear after recovery; it is not valid for a modeled acknowledged
commit to vanish. Transport/application retries must accommodate that uncertainty.

## Recovery

STO-005: under the [crash model](failures.md), recovery produces an invariant-
preserving committed history containing every acknowledged transaction, with no
partial transaction. Unacknowledged complete commits may also survive. Recovery
checks framing, integrity, dependencies, journal order, and checkpoint linkage.

The exact rule for choosing a journal/checkpoint generation is still open. Do
not implement “pick the newest timestamp.” Incomplete uncommitted tails and
detected damage to committed data have different handling. Quarantine/report
detected corruption; do not silently reinterpret it as successful rollback.
Detecting rollback of an entire otherwise valid store requires an independent
trusted anchor and is outside the crash-only claim until D14 supplies one.

The current journal experiment distinguishes contiguous journal sequence from
acceptance transaction IDs, which are consumed even on a known abort. Its
durable acknowledgement anchor is an explicit assumed input, not a mechanism
implemented by the book. A staged marker makes an abort uncertain because the
marker could survive; recovery must resolve it. That isolated-slot journal is not
connected to the composed node or physical adapter. The actual immutable-file/store-node path is connected and tested; its
remaining physical correspondence is tracked in [store refinement](store-refinement.md).

Object bytes may survive without a committing reference. Such orphans are not
visible articles and are reclaimable only after transaction/recovery roots are
accounted for. Conversely, committed references must never resolve to missing
objects under the stated crash assumptions.

## Checkpointing and compaction

The current compaction tranche publishes an immutable selected transaction
prefix pack containing the exact canonical bytes of every covered Store event.
Recovery validates each surviving covered transaction byte-for-byte against
that pack, permits covered files to be absent after an interrupted reclaim,
and requires a complete contiguous suffix from the coverage boundary.  An
unknown gap or conflicting surviving record is corruption.  Reclaim resumes
by unlinking only the ACL2-issued surviving covered names under the writer
lease and fencing until the transaction-directory barrier succeeds.  The pack
does not summarize or discard semantic history: generic replay still consumes
the reconstructed full event stream, including retention and identity events.
The current native `pack-reclaim` command opens the Store for writing and holds
its exclusive lock through the last unlink and directory barrier. A live owner
or read-only opener holds an incompatible Store lock while a reader uses its
pinned archive, so this command refuses before deletion when such a reader is
active. This is an offline exclusion rule for this command; it is not a general
proof of concurrent physical reclamation under a different storage layout.
The native `pack-retire` command uses the same lock and retires only pack
generations older than the validated selected generation.  Each unlink and
the closing directory barrier are separate crash cuts.  This recovers space
from redundant pack copies; the exact event stream and indefinite retention
of protected sources are unchanged.  The gap-aware pack allocator advances
past the selected high-water generation and never reuses a retired name.
One selected pack is limited to 4096 events and 4 MiB of encoded bytes.  Since
this tranche stores the complete canonical prefix rather than a semantic
summary, it cannot compact an arbitrarily large history; rolling packs or a
proved state summary remain future work.

Preservation (PRF-073, `books/checkpoint-compaction-preservation`): deleting
any subset of the reclaim plan leaves the next open's namespace observation
valid, and the framed pack reconstructs the identical record list, so replay
and every served fact are unchanged. The plan reads the open path's own
namespace gate, `fn-profile-txn-observation`.

STO-006: replacing history with a checkpoint preserves the full logical state
needed for future behavior, including allocation watermarks, duplicate history,
outstanding obligations, relevant policy context, and receipt/release evidence.
Never checkpoint just the currently visible article list. Evidence is a typed
provenance (RET-007, `books/provenance.lisp`), carried through the checkpoint
as the bounded printable string the record grammar already holds; a
provenance written before the typed value existed is the `:legacy` kind and
keeps its bytes and its meaning.

STO-007: compaction preserves every retained object's exact bytes and identity,
and every required record. The replacement becomes durable and reachable before
old storage is reclaimed. A crash at each phase must recover a complete valid
generation. Temporary space is reserved; no-space during compaction cannot force
deletion of protected content. In-flight readers pin their storage dependencies.

STO-008: stored bytes are checked when used according to the integrity policy.
Detectable corruption triggers explicit degraded/quarantined state. Scrubbing,
redundant copies, repair, and erasure coding are later mechanisms with separate
assumptions; a digest alone does not repair content or guarantee all faults are
detectable. Recovery must not emit a fresh success for missing or corrupt data.

Composed recovery requires both article/retention replay and identity-evidence
replay to succeed. A structurally valid atomic signed article with a missing
historical enrollment is a recovery fault even when its embedded article alone
replays successfully. `fn-sn-recover` leaves the observed history intact and
sets the file phase to `:fault`; recovery barriers cannot turn that state into
`:ready`. `fn-sn-open-observed` reports its existing `:replay` error instead of
opening the seed's empty node. The negative composed trace in
`tests/acl2/store-identity-traces-tests.lisp` exercises this separation;
fresh certification and native corrupt-history startup evidence remain open.


### Checkpointing: the Store checkpoint that open reads (P3, 2026-09-25)

STO-011: Open reads the newest verified exact-state checkpoint and replays at
most K records after it, else replays in full and says so.

The Store checkpoint is the exact state of the open after a committed prefix
of S records: the record list itself and the accumulator of each fold the
open runs (`fn-sco-capture`, books/store-checkpoint-open.lisp: the
configuration and node fold paused at the prefix end, identity, consumer
projection, topic prefix, event index). It removes no record, so it is
packing plus a cache and D13 is not a precondition. It is derived: replay
stays authoritative, and the file may be deleted at any time.

- **Bytes.** One file, `store-checkpoint.fnsc` in the store root: FNSC
  segment frames (header 37 octets: magic, schema 2, index, count, length,
  sequence S as u64; the chunk; a trailer `fn-frame-trailer` over the
  previous trailer, the header and the chunk). Each segment is at most the
  profile's max-record-octets R plus 69 octets, so each is one bounded read.
  The payload is a postfix program for a stack machine
  (books/store-checkpoint-codec.lisp); the decoder is a loop with an
  explicit stack and never calls the Lisp reader.
- **Publish.** `fn-bs-scp-program`: stage, write, fsync, rename over the
  name, root fsync, with cuts `state-checkpoint-created`, `-written`,
  `-staged-durable`, `-replaced`, `-durable`. At every cut the name is the
  old file, absent, or the new octets (`fn-bs-scp-program-crash-is-old-or-new`).
  The verb is `operator store checkpoint` (store lock held); it extends the
  checkpoint the open used over the suffix (`fn-sco-extend-of-capture`).
- **Open.** The host reads the file segment by segment (range reads, under
  A-HOST-EXCLUSIVE-READ), decodes it, and `fn-sco-select` serves it only
  when the chain verified, S is at most the committed count, and the suffix
  is at most K (max-open-suffix). It then reads only the transaction files
  with sequence at least S and calls `fn-sco-open`, which equals the full
  open of the whole history (`fn-sn-recover-from-checkpoint-equals-full-recover`).
  Otherwise it replays in full. Status prints `open=checkpoint:S suffix=k`
  or `open=full-replay reason=R` (absent, corrupt, ahead-of-history,
  suffix-exceeds-k).
- **Not yet.** K0 coverage of the publish program's root rename is open.
  (The owner opens from the checkpoint and publishes at K/2 since
  owner-checkpoint-open, PRF-083.)

STO-016: The checkpoint open costs less than the full replay it replaces,
and a publication does not hold served commands.

- **The file carries the count.** The event index maps every sequence below
  S to its record, so the file writes S in the record slot when the index
  yields exactly the record list (`fn-sco-freeze`), and the decoder reads
  the list back out of the index (`fn-sco-thaw`; `fn-sco-thaw-of-freeze`,
  every checkpoint value). Past the index's u32 keys the list stays in the
  file: nothing is capped. The header's sequence field is S either way. The
  Store state itself still holds the record list (`fn-sf-records`).
- **One open.** Both host opens extend a checkpoint once (the decoded file
  over the suffix, or the empty capture over the whole history) and read the
  configuration and the opened Store off the extension (`fn-sco-store-open`,
  `fn-sco-store-open-of-extended-capture`); the owner installs from that
  value (`fn-ock-install-of-store-open-by-definition`), so the suffix is
  replayed once per process start.
- **Linear list checks.** The whole-node recognizer a decoded checkpoint's
  node is checked by uses linear checks for its Message-ID, binding and
  obligation-identity lists (a hash set in a local stobj, `fn-ks-distinctp`,
  `fn-ks-subsetp`), each equal to its quadratic `:logic` definition.
- **Publication off the mutex.** The owner captures the base, the
  configuration history and the record list under its mutex, then extends,
  encodes and writes on its own thread, and installs the result under the
  mutex again. What it writes is the capture of the history at the capture
  point (`fn-ock-publication-is-the-capture-at-the-capture-point`).

## History classes and lifetimes

STO-010: every class of durable state the store holds has a stated lifetime,
the future decision that needs it, and the capabilities that may remove it,
each under a named proof obligation; no other operation removes it.

Status: contract for M5 (review of 2026-09-24,
[direction review](../planning/review-2026-09-24-gpt6-direction.md) §M5). The
committed-history marker (STO-009) is implemented. History compaction and
content reclamation are not; their rows below are the obligations an
implementation must discharge. Where a lifetime depends on policy that is
not decided, the row says **open**.

Three capabilities may ever remove durable state. They are different
promises and each has its own proof obligation:

- **Packing** (P) moves bytes into fewer filesystem objects. It keeps the
  history and its semantic contents. Obligation: the open after the removal,
  at every cut, hands replay the identical record list (PRF-073). Today's
  `pack`, `pack-reclaim`, `pack-retire` and `operator CONFIG store compact`
  are this capability and nothing else.
- **History compaction** (H) replaces a prefix of records by a versioned
  summary. Obligation: for every future permitted input, every decision
  computed from summary plus suffix equals the one computed from the full
  history. That covers acceptance, duplicate and conflict verdicts, number
  allocation, charges, release admissibility, statement lookup and
  equivocation, and consumer decisions. Showing that current reads look the
  same is not enough. Not implemented. It needs D13 and a summary format
  with its own version.
- **Content reclamation** (C) removes object bytes. Obligation: no retention
  obligation holds them (D03: only an explicit authorized release ends one),
  and no active reference pins them: a reader's pinned archive, a consumer
  cursor or an unresolved BP handoff. The record that the bytes existed, and
  their identity, stay (see anti-resurrection). Not implemented for article
  content.

Only these three remove state. A capability not named in a class's row
never removes that class. "Forever" means under D03: until an authorized
policy that this contract does not yet have says otherwise.

| Class (where it lives; codec) | Future decision that needs it | Lifetime | May remove it |
| --- | --- | --- | --- |
| Article record (Store transaction, `fn-r` schema 0/1, `books/records*`) | Message-ID duplicate and conflict verdict (D25); serving by number and Message-ID; content identity; group numbering; the obligation undertaken at acceptance (STO-002); provenance (RET-007) | Record: forever. Payload bytes: until their obligation is released and no reference pins them | P: the record, byte-exact. H: only into a summary that keeps the Message-ID and content-identity binding, the group allocations (anti-resurrection, frontiers) and any open obligation. C: the payload only, after release |
| Retention undertaking (`fn-e` `:undertake`, `books/store-events`) | Capacity charge; the hold on content; admissibility of a later release; the operator's `store retention` | Until the matching authorized release | P. H: an open undertaking must stay in the summary with its charge, subject and evidence. C: never removes it |
| Retention release (`fn-e` `:release`) | That the hold ended and on whose authority; reclamation's permission; refusing a second release | Until superseded by a summary that keeps the released identity and its evidence (**open**: D13) | P. H: into the anti-resurrection summary only |
| Identity and key policy evidence (`:statement-verdict` `fn-stxe`, `:keyring-snapshot` `fn-stxk`, `:accepted-statement` `fn-stxa`) | Verifying historical signed articles at recovery (STO-008: a missing enrollment is a fault); equivocation (`fn-sn-equivocatorp`); statement lookup; key and epoch evolution | Forever (**open**: a keyring-epoch summary that answers every historical verification identically) | P. H: only with a summary proved to answer `fn-sn-statement-lookup` and `fn-sn-equivocatorp` the same for every future query |
| Consumer cursor pins (`:consumer` `fnce`: bootstrap, register, ack, rebase, unregister, rollover; `books/consumer-*`) | What each consumer acknowledged; which history an unacknowledged consumer still pins; the next registration epoch | Each entry until superseded by the next ack, rebase or unregister for that consumer. The epoch scalar: forever | P. H: into the latest entry per consumer plus `next-epoch` (the state `books/consumer-position` already carries). Its pins bound C |
| Topic admission (`:topic-admin-install`, `:topic-anchor`, `:topic-admit`) | Admitting later topic events (parents, authorship, admin) | Forever (**open**: experimental) | P only |
| Submission outcomes | Local POST: the accepted article record, which answers a retry with the same Message-ID as a duplicate. Refused and uncertain outcomes are not persisted beyond the burned reservation. BP submissions: the workflow and handoff records | As the article record / as the BP rows below | As those rows |
| Unresolved BP handoffs and obligations (FNBS directory: dispatch, delivery, deletion, conflict, family, forward rows; `books/bp-fnbs-*`) | Custody, retry, delivery and deletion reports, conflict evidence | Until resolved; then an outcome summary for duplicate and replay refusal (**open**) | Separate namespace. None of P, H or C touches it today (**open**) |
| Allocation frontier (`allocation-frontier.json`, FNSM kind 2) | Next transaction ID; an ID once reserved is never reused, including burned ones | Forever; one monotone value | None |
| Committed-history marker (`committed-history.json`, FNSM kind 3, STO-009) | Detecting a lost committed suffix at open | Forever; one monotone value | None. H must write a summary whose record count the marker still bounds (the summary counts as the records it replaces) |
| Local number frontiers and watermarks (per-group next number) | Allocating a number never used before in that group | Forever. Today derived by replay from article records | H must carry every group's high-water in the summary (numbers are never reused, even for removed articles) |
| Anti-resurrection summary | Refusing, or deciding by policy, a re-offer of a removed Message-ID or content identity; never reusing its numbers | Forever, once it exists | None. It does not exist yet: D13 is its precondition, and H and C are not admissible without it |
| Store profile (`config.json`, FNSM kind 1) | Every open-time bound; the budget | Forever; changed only by the offline upgrade | None |
| Configuration history (`config/`, generations) | Current served groups and domain; the generation that local-post provenance cites | Current generation: forever. Older generations: while a record's provenance cites them (**open**) | Not in the Store transaction namespace. No capability today |
| Pack generations and selection marker (`packs/`) | The selected pack reconstructs the covered prefix | The selected generation: while it is selected. Older generations: redundant | P (`pack-retire`: older generations only) |
| Whole-state checkpoints and auxiliary images | A differential comparison at open. Derived, never authoritative | While selected | May be discarded; replay remains authoritative |
| Staging names (`staging/`) | None: never authority (`books/store-sweep`) | Until the recovery sweep | The sweep |

**What today's compaction relieves.** It relieves the transaction-file count
and per-file overhead: inodes, directory entries and the open's one read per
file. It relieves no other limit. The transaction budget counts committed
records, and packing leaves them unchanged. The replay input is the same
record list. Because the pack is one 4 MiB unit, the history must fit in
that unit. The operator headroom line (`operator CONFIG status`, `headroom
transactions-used=N transactions-budget=B`) should say this beside it:
`compaction relieves files, not transactions`. Only H under D13 raises
admission headroom. Only C frees content bytes. That line is part of this
contract and is not printed yet (**open**).

**Bounded operation.** M5 promises bounded execution and metadata behaviour
under a stated workload and retention/release policy, with explicit refusal
when a promise cannot be funded. It does not promise unbounded distinct
content on finite storage. Under D03's indefinite retention with no release,
every class above grows monotonically until admission refuses by name
(`fn-sbud-prepare`, `:unaffordable`).

### The committed-history boundary

STO-009: a committed-history boundary is written after each commit and before
its acknowledgement, and every open refuses, by name, a record history
shorter than it; a burned allocation never trips it.

The namespace gate admits a history and every proper prefix of it
(`fn-cverb-open-history-gate-admits-a-lost-suffix`). The allocation frontier
cannot tell a lost newest record from a burned reservation, because the
frontier is reserved before the record. `committed-history.json` is the
witness written after the commit:

- What it holds: `fn-hm-after-commit SEQUENCE` is the FNSM kind-3 frame of
  the count `SEQUENCE + 1` (`books/store-history-marker.lisp`).
- When it is written: `fnn-mark-committed` (`host/native/io.lisp`) runs after
  `fnn-publish` returned `:durable` (the record passed its
  transaction-directory barrier) and before `fnn-finish`. It is called at
  the three publish sites: `store post`, the capacity probe, and the owner's
  `fnn-owner-publish-prepared`. The one other writer is the recovery
  catch-up below. No reservation, abort or refusal writes it.
- The byte program (`*fn-hm-marker-program*`): create a `.stage-` name in
  `staging/`, write it, fsync the file, rename it onto
  `committed-history.json`, fsync the root directory. Each step has a cut:
  `marker-created`, `-written`, `-staged-durable`, `-replaced`, `-durable`.
  They are selectable on a developer image as `FN_NATIVE_POST_FAULT=CUT:kill|eio`
  from ACL2's table `fn-hm-marker-cut-names`. Any OS error is uncertain:
  the store is fenced, the transaction is not acknowledged, and recovery
  decides. So every acknowledged record is below a durable marker.
- The open's check: `fn-hm-open-verdict`, evaluated once in `fnn-recover`
  against the length of the reconstructed record list (pack events plus
  suffix files, so a reclaim does not shorten it). A count below the marker
  is a fault that names `history-short-of-marker`. A frame that is not
  kind 3 names `marker-damaged`. Under the profile's `history-marker =
  unmarked` an absent marker is admitted as `:unmarked`: that is every store
  written before the marker, and its first writable open writes the marker.
  The host calls `fn-hmr-open-verdict` (`books/store-history-required.lisp`),
  which is `fn-hm-open-verdict` except as below.
- Proved (PRF-076), over a model whose crash table is rename atomicity for
  this one program: no history the host can produce is refused. Such a
  history is any interleaving of burned reservations, uncertain
  publications, and commits crashed at any marker cut
  (`fn-hm-run-keeps-every-open-admitted`). A lost suffix that contains an
  acknowledged record is refused as `history-short-of-marker`, whatever
  history follows it (`fn-hm-open-refuses-a-lost-acknowledged-record`).
- The crash table is no longer an assumption: the program is
  `fn-bs-marker-program` of the byte crash model
  (`books/byte-store-marker-program.lisp`), between the record program and
  the finish program in every commit's coordinate
  (`tests/campaign/native_cuts.py` `POST_PROGRAMS`). In every crash image of
  every cut the marker is the old one before the rename, old or new at it,
  and new after the root barrier, never torn
  (`fn-bs-marker-program-crash-is-old-or-new`), which is exactly the history
  step above (`fn-bs-marker-crash-is-the-history-table`), so the open after
  recovery stays admitted (`fn-bs-marker-crash-open-stays-admitted`). K0 at
  the five cuts is `fn-bs-k0-marker-cuts-relation`
  (`books/byte-store-k0-marker.lisp`); at `marker-replaced` it is stated on
  the two resolutions of the pending rename.
- Cost: one more staged write, two fsyncs and a rename per committed
  record, in every profile. Measured with the in-process commit probe (120
  commits of 32 KiB, hbox, three runs each): on tmpfs, 110 ms per commit
  before and 108 ms after, which is within noise. On ZFS (`/tank`), 326 ms
  before and 388 ms after: 62 ms more per commit (+19%). The ZFS runs vary
  (before: 279 to 360 ms per commit). See
  [the record](../planning/evidence/m5-history-lifetimes-2026-09-24.md).
- **The guarantee (D31)**, with A the committed prefix covered by success
  answers a client may rely on, M the durable marker's count and D the
  durable reconstructable length: A <= M <= D. The syscall sequence is not
  frozen; a cheaper publication program is legitimate when its
  acknowledgments and crash behaviour refine the same invariant, and moving
  the count into the allocation barrier is not (allocation precedes the
  record's durability).
- **The requirement (D31 case 1).** The format-8 profile's thirteenth field,
  `history-marker`, is `unmarked` (0: every format-7 store, and a format-8
  store not migrated) or `required` (1). Under `required` an absent marker
  is damage: `fn-hmr-open-verdict` answers `:marker-missing` and the open
  faults (exit 4). `init` never writes `required`
  (`history-marker-required-before-a-marker`); `store upgrade-profile
  --history-marker required` does, and `fn-hmr-upgrade-verdict` grants it
  only when the marker is present and counts exactly the reconstructed
  history (`history-marker-not-covering` otherwise). The command opens the
  store first, and that open writes the covering marker, so a migration is
  the two-step: the marker program, then the profile program
  (`fn-hmr-legacy-store-migrates-by-the-two-step`,
  `fn-hmr-requirement-follows-a-covering-marker`). The upgrade relation
  lets the field rise and never fall (`not-an-upgrade history-marker`), so a
  required store never admits an absent marker, whatever follows
  (`fn-hmr-required-store-never-admits-an-absent-marker`).
- **The recovery catch-up (D31 case 2).** A record can be durable while its
  marker is not: the process died between the record's barrier and the
  marker's. The next open finds the record, and a retry of that submission
  is then answered as already stored (NNTP 441 with the duplicate text, the
  developer `duplicate`, BP `:duplicate`) with no later commit to advance
  the marker. The catch-up point is recovery: after `fnn-recover`'s fifth
  barrier (so the reconstructed records are durable) and its staging sweep,
  and before the open returns, a writable open writes `fn-hmr-catch-up`'s
  frame, the reconstructed count, through `fnn-mark-committed`: the same
  program and cuts (selectable on `recover` as
  `FN_NATIVE_RECOVERY_FAULT=CUT:kill|eio`, and on `store upgrade-profile` as
  `FN_NATIVE_PROFILE_FAULT`). An error there is uncertain (exit 3) and the
  next open catches up again. A reader under the shared lock writes nothing
  and answers no submission. Proved over the history model of commits,
  opens, resolutions and migrations: `fn-hmr-step-preserves-the-invariant`
  (the open admits, A <= M, and a live process's marker equals D) and
  `fn-hmr-open-refuses-below-every-answered-record` (an open that finds
  fewer records than the newest one answered as stored, by a 240 or by a
  resolution, is refused naming the marker).
- Not detected: losing the marker together with the files it covers in an
  `unmarked` store (reads as `:unmarked`); an unacknowledged record that
  survived above the marker and was never answered (`fnn-publish`
  uncertain, or a crash before the marker's rename, with no open since);
  replacing the whole store with an older valid copy, which needs a
  freshness anchor (D14); the configuration history and the BP stores. A
  shared-lock reader may serve a record above the marker until the next
  writable open.

### Content reclamation under D13 (STO-014)

STO-014: Content reclamation under D13: an operator retention rule, a per-article decision over every holder, and a tombstone that keeps every decision the history needs.

Status: decision, tombstone and served projection proved (PRF-088); the
host asks the tombstone-aware D25 verdict at every site; OVER, XOVER and
NEWNEWS drop a reclaimed article; `status` prints the rule and the
reclaimable, held and reclaimed counts. The durable `store reclaim` verb is
not implemented: the K0 byte model has no step that replaces a committed
transaction's content (planning/evidence/reclaim-host-2026-09-25.md).

**The rule** is the operator's, set through the ordinary reconfiguration
record: `admin retention set keep-forever | released-by-all-holders |
release-after DAYS` stages two `:set-limit` rows, `retention` (0, 1, 2)
and `retention-days` (`books/reclaim-rule`). No row reads keep-forever,
D03's default, so a store written before this section behaves as before.
An unrecognised row is refused by name and reclaims nothing. The rule is
the authorized release of the article's own archive pin; it releases no
other obligation.

**The decision** (`fn-rcl-verdict`, `books/store-reclaim`) answers one
article with `:reclaimable` or the first reason it stays:
`already-reclaimed`, `rule-keeps`, `rule-refused`, `too-recent`
(release-after: stamp plus DAYS × 86,400 s after now; a legacy stamp never
qualifies), `verdict-needs-payload` (a verdict other than `:absent`: the
statement index is re-derived from the payloads at open and an
`:unverified` article may verify under a later keyring, STO-008; an
`:absent` article, which has no authorship field, contributes nothing under
any keyring and neither does its tombstone, so it is not held),
`held-reader-pin`, `held-consumer-cursor` (a
consumer that acknowledged number A in the group holds every number above
A), `held-feed` (a live peer not yet delivered it; a retired peer holds
nothing) and `held-bp-obligation`. The keystone says the executable test is
exactly "no obligation in the flattened list names the article" together
with the rule.

**The tombstone** replaces the payload octets of the article record and
nothing else: NUL `FN-RCL1`, a source flag, the payload's SHA-256, the
SHA-256 of its D25 source under its own agent, the payload length and that
agent (`books/reclaim-tombstone`). The record keeps its Message-ID,
sequence, txid, generation, groups, memberships, obligation identity,
content subject, release evidence, charge and stamp, so the history entry,
the numbers, the group bindings and the content identity stay.
Acceptance never reads a stored payload, so replaying the record with the
tombstone reaches the reclaimed state, and every other record's step
commutes with reclamation (`fn-rcl-prepare-commutes-with-reclaim`).
A tombstone is never admitted as an article: its first octet is NUL, which
no article's first header line can open with, and `fn-pa-carrier-form`,
which every served ingress calls before the Store prepare, refuses it as
`:article` (`fn-rcl-tombstone-refused-at-carrier-form`,
`books/reclaim-admission`). The developer image's `store post` has no
article check and is not a served ingress.

**What stays the same** (the decisions this table lists): the duplicate
history (`fn-acceptedp` for every Message-ID; a reclaimed ID is refused
again, never resurrected), group numbering (per-group next numbers), each
article's bindings, and the D25 duplicate-versus-conflict verdict the host
calls (`fn-rcl-existing-action`) up to a SHA-256 collision on the compared
pair. Verdict lookup reads the Store's verdict slot, which reclamation does
not touch, and an article with a verdict is not reclaimed.

**Served**: ARTICLE, HEAD, BODY and STAT of a reclaimed article answer
`423 article reclaimed` by number and `430 article reclaimed` by
Message-ID. OVER answers 503 for it and NEWNEWS still lists it (open).

### Chained packs (not implemented)

The 4 MiB compaction unit is permanent per store today, because each
compaction repacks the whole history. Chaining lifts that limit without
raising the open's largest single allocation. It needs:

1. A pack that covers events `[lower, boundary)` and names its predecessor:
   the predecessor's generation, boundary and frame digest. The first pack
   has `lower = 0` and no predecessor.
2. Contiguity: each pack's `lower` is its predecessor's `boundary`. The
   selection marker names the newest pack. The open walks the chain from
   the newest, reads one pack at a time, and checks each link's digest.
3. A chain-length bound in the profile, so the open's work stays bounded
   before any pack is read. The aggregate replay bound (field 3) must also
   count pack events; today it counts suffix files only (finding 3 of the
   compact-verb record).
4. Retire keeps every generation the selected chain names, and removes only
   generations outside it.
5. The preservation theorem generalized: the chain's concatenated
   reconstruction plus the suffix is the identical record list (PRF-073 over
   a chain). Each crash cut of publishing a new link leaves the previous
   chain selected.
6. A compaction then packs only the uncovered suffix, at most 4 MiB, into a
   new link. It never repacks what earlier links cover.

Chaining is still packing. It does not relieve the transaction budget or the
replay input. That is H's job.

## First executable scope

Model logical transactions before selecting sector alignment, frame lengths,
segment sizes, checkpoint layout, or a disk index. Then refine to bytes and the
chosen platform contract. These choices are M2 exit criteria, not details to
invent independently inside a file-writing adapter.
