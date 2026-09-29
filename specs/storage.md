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

STO-027: The catalog is the served store's executable: the Message-ID binding, the local numbers, a row's visibility to a version and the retained octets are columns of `fn-cat` read in constant time, never rediscovered by a walk of the history (wave 5, D33; lane catalog-slice: the columns exist and are proved, the served path moves to them in the continuation).

`HDR :fn-verified` (PRF-367, lane scale-reads) reads the catalog for its numbers and articles and the RECORDED verdict list for each line's verdict (SUB-006: the acceptance evidence, which a keyring change never rewrites), resolving a whole reply's verdicts in one pass over that list: O(R + V) for R lines and V recorded verdicts, where the reference was O(R x (N + V)). A catalog row's context verdict is NOT that evidence (it is decided under the keyring in force at its intern and a `:redecide` replaces it), so the verdict is not yet a constant-time column; that needs the row-to-evidence equation carried, or a recorded-verdict column.

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
`fn-store-10`, the one format; a `fn-store-9` profile is refused at the open
by name with the way out, STO-028: the format word, then transactions,
history octets, record octets, article octets, groups per article,
group-name octets, open suffix, five namespace counts and the three header
limits of header-limits-profile, fifteen u64 fields numbered 1 to 15,
`*fn-bs-profile-field-names*`; format 9's frontier word and committed-history
marker, carried and never read, are gone;
docs/operator.md), set at `init` by flags and validated by the relations of
`fn-bs-profile-validp`; ACL2 fixes no value except the codec ceilings above
them. It is written once, by `init` (or `store import`, STO-028), and never
rewritten in place (D34, fresh deploys): a different profile is a reinstall
and an import with the raised field; a store of another format is refused at
open by name. This is a local-policy choice of fn; no RFC governs it.

STO-015: a namespace the store holds is bounded by the operator's profile,
never by a constant (D27). Configuration generations and AUTHINFO
credentials are bounded by the profile's `max-config-generations` and
`max-credentials` (profile fields 10 and 11, read through
books/store-profile-namespace.lisp). The writer refuses exactly past the
bound, by name (`:max-config-generations`, `:too-many-credentials`), and
the reader admits every namespace within it: the configuration listing
(`fn-nco-observe`) and the credential loader (`fn-native-auth-load`). An
open reads the profile the store was born under (D34), so a namespace the
node wrote is admitted by every later open.
The credential file's octet and line bounds follow its count: 512 octets and
8 lines per credential, plus one unit for the header, a work bound per
credential. fn.toml's size bounds stay constants. They bound the work of
reading a fixed-schema file that names the store, and the file holds no
collection. Consumers are read since STO-021; policy members are not
(planning/evidence/bounds-profile-2026-09-25.md).

STO-021: no hidden constant caps a community count (D27). Every constant
that bounds stored data is one of three things: governed by a profile field,
a work bound of one fixed-shape record, or a codec width that admits every
valid profile (`fn-bs-profile-validp-codecs-accept`); the classification is
planning/evidence/community-bounds-2026-09-26.md. The consumer count is the
profile's `max-consumers` (field 8): the owner's registration
(`fn-cp-register-within`, books/consumer-position.lisp) refuses
`:max-consumers` exactly when the table already holds that many, and a raised
field takes effect at the next open with no migration; replay re-runs the
registration's validity, not the admission bound, because the profile only
rises. Open: the group-name bound (field 6) is not yet read on the served
path and the name width is 256, below the NNTP wire's 460 (PKT-451); a
peer's configuration rows are now data (STO-023).

STO-030: the header limits of one article are profile fields, and admission refuses exactly past them by name.
Fields 13 `max-header-fields`, 14 `max-header-lines` and 15
`max-header-octets` (defaults 64, 256 and 16,384, the parser's constants
before D27) bound one article's header; `init` and `store import` take
them as `--max-header-fields N` and so on. The relation is 1 <= fields <=
lines <= octets <= the article codec's ceiling, each failure refused by
name. The served POST refuses a header past them with a 441 naming the
field (books/injection.lisp `fn-inj-decide`, PRF-230); readers parse
under the ceiling, so raising a limit never changes an admitted article.

STO-023: stored data is bounded by the operator's profile or by the records that built it, never by a lifetime constant.
Two constants that capped data are gone (D27;
planning/evidence/caps-to-profile-2026-09-26.md). A peer's row group grows
by requests: `peer carries` and `peer budget` publish only the rows they
change, `(:add-peer-rows NAME ROWS)` and `(:remove-peer-rows NAME ROWS)`
(configuration delta codes 18 and 19, books/config.lisp), and
`*fn-cfg-max-rows*` (1,024) bounds the work of one delta, not the rows one
peer holds (`fn-cfg-add-peer-rows-refuses-exactly-past-the-work-bound`,
`fn-cfg-apply-delta-adds-at-most-the-work-bound`); the published deltas
apply as the whole-group extension did
(`fn-pcb-extend-deltas-apply-as-the-extend-delta`), and the record count is
the profile's `max-config-generations`. A checkpoint generation
number is a uint32, the width of its name and selection codec, and the
generations a store retains are the profile's capacity, `max-transactions`
plus one: the allocator refuses exactly at that capacity
(`fn-cpp-next-generation-refuses-exactly-at-the-profile-capacity`; the pack
allocator's twin went with the pack layer), so
a reinstall with a larger T (`store import --max-transactions N`) raises it and a store no longer meets a lifetime
figure of 4,096 publications. No store format changed: an older image
refuses a configuration log holding codes 18 or 19 and a checkpoint
directory holding more than 4,096 names or a name at or above 4096, the
rollback consequence of these two steps. Field 6, `max-group-name-octets`,
now governs group names at both intakes: `init` refuses
`:max-group-name-octets` by name (`fn-nop-init-plain-groups-are-within-the-profile`)
and every configuration record, offline or through the live owner, is
authorized against it (`fn-cvec-native-admin-authorize-refuses-exactly-past-the-group-name-bound`);
the field was always validated against the codec width, so no format
changed. Open: the name width rising to the wire's 460 (RFC 3977 section
3.1), PKT-510.

STO-025: opening a store costs each configuration record its own work.
Every fold that replays configuration records (`fn-cpr-loop` at open,
`fn-sco-cpr-prefix` over a checkpoint's prefix, `fn-cnode-replay-loop` and
`fn-cnode-apply-config` at each publication's authorization) carries the
configuration invariant in its guard and checks each record with
`fn-cnode-carried-acceptablep`, which is the node's acceptance check under
that invariant (`fn-cnode-record-acceptablep-is-the-carried-check`); before
it, each record re-ran the whole-configuration recognizer two or three
times, so a replay's cost grew with the configuration's size per record
(PKT-501; planning/evidence/caps-to-profile-2026-09-26.md, Continuation).
The replay still reads every configuration record at open; a configuration
checkpoint the open resumes from is PKT-510. An offline request authorizes
its one record from the fold its open computed (PRF-209): the
configuration-only and physical folds over the history ending in that record
are one step from the folds without it (`fn-cfgc-config-replay-of-one-more`,
`fn-cfgc-cpr-replay-of-one-more`, the record filed after every event because
its txid is at or past the frontier), and the host-called authorization
`fn-cfgc-cvec-native-admin-authorize` equals the replaying one whenever the
carried fold is the open's replay of the same histories
(`fn-cfgc-cvec-native-admin-authorize-is-the-replayed-authorization`). The
candidate open over the whole history, and the open itself, remain one pass
each per request (PKT-601).

A BP node's held rows and held octets are the operator's too, in the node's
own profile rather than the Store's: the FNBS journal is not a Store
namespace, and `bp-service`, `bp-contact` and `bp send` run with no Store.
The file `bp-node-profile` in the journal root (books/bp-node-profile.lisp,
PRF-131) is one frame of `fn-bp-profile-1`, `max-held-rows` and
`max-held-octets`, or (PRF-134) one frame of `fn-bp-profile-2`, which adds
`max-adu-octets` (the largest application data unit the node admits: a
whole bundle's payload, or the total ADU length a fragment names) and
`max-bundle-octets` (the largest bundle the node decodes from a peer); its
absence is 64 rows, 16 MiB, 65,538 and 1 MiB, the machine every earlier
journal ran under. A format-1 file opens with the last two at those
defaults (`fn-bpnpf-profile-read-of-format-1`). Each field is a machine limit (1 to 2^24, the
machine state's representation ceiling), the frame carries every value that
relation admits (`fn-bpnpf-read-of-octets`: a saved profile opens), and
every valid profile opens a machine with exactly those limits
(`fn-bpnpf-valid-profile-opens`; profile 2:
`fn-bpnpf-profile-read-of-octets`). `bp-node profile JOURNAL NODE ROWS
OCTETS [ADU BUNDLE [ROTATE]]` only raises it (`fn-bpnpf-write-never-lowers`,
`fn-bpnpf-profile-write-never-lowers`). Profile 3 (lane bp-rotation) is one
frame of `fn-bp-profile-3`, which adds `rotate-records`, the rotation
threshold a node verb's open consults (specs/bp-node-machine.md 3.6,
"Natural rotation"); formats 1 and 2, or no file, read with 4,096
(`fn-bpnpf-node-profile-read-of-older`), a saved profile 3 opens
(`fn-bpnpf-node-profile-read-of-octets`), and a write never lowers a held or
codec field while the threshold may move either way
(`fn-bpnpf-node-profile-write-never-lowers`). A journal whose rows or held octets
exceed the profile it opens under is refused at replay with the named
verdict `:held-beyond-profile`, never truncated
(`fn-bpnpf-replay-past-the-profile-is-refused`,
`fn-bpnpf-replay-past-the-octets-is-refused`). The receive boundary refuses
a wire past `max-bundle-octets` before decoding it and a bundle whose ADU is
past `max-adu-octets` before custody, by name
(`fn-bpnpf-admission-refuses-beyond-the-profile`). The codec widths the
three former ceilings became (ADU, bundle decoder input, held image) are
2^24, every field's ceiling, so no profile names a value a codec refuses
(`fn-bpnpf-profile-within-codec-widths`; specs/bp-node-machine.md 7.1). The
Store profile's `max-bp-rows` field is still not read (PKT-294).

STO-013: a record's sequence, transaction ID, generation, charge and stamp
are u64 (design 2026-09-25-bounds §2.3, packet P6). A record that needs a
field above 2^32 - 1 carries schema octet 2 and eight-octet CBOR uint heads
(RFC 8949 §3.1); every other record keeps its schema-1 octet and its
bytes. No older image's store is read (D34, no migrations: fresh deploys at
6.6.0); the pre-P6 decoder and its two identity theorems were retired with
it. A profile's record bound R is
checked against the record ceiling at the widths the runtime produces (u32
heads, 1 083 octets of fixed overhead); a schema-2
record is at most 28 octets past that ceiling and the publish gate refuses
it. The frontier and the profile's T field still cap transaction IDs at
2^32 - 1. The widths are a stronger fn guarantee; no RFC requires them.

The node's producers stay inside the u32 widths, so every record it stages
is schema 1 and within R (`fn-sn-prepare-stages-a-narrow-article-record`,
`fn-post-admitted-article-record-is-within-r`, PRF-123): the allocator
stages only the reserved transaction ID (frontier - 1, the frontier u32),
with generation equal to it and sequence the committed count; the stamp is
seconds below 2^32 or the article is refused `:clock-unusable`; the POST
boundary refuses a charge above 2^32 - 1 (`:charge-bound`) and a BP policy
cannot name one. The prepare itself does not refuse a wide charge, so the
bound is the boundary's. u64 is therefore the width the codec and the
translation carry, not one the node produces: a transaction ID past
2^32 - 1 needs a wider frontier file (frontier-3), a stamp past 2106 and a
charge past 2^32 - 1 need their producers widened first.

STO-018: a record whose charge fits u32 is within the profile's R at any
sequence, transaction ID, generation and stamp width, and the allocation
frontier frame carries u64 (frontier format 3) with every format-2 frontier
frame read to the same transaction ID. The record ceiling a profile's R is
checked against counts five-octet heads for the schema octet, the group
count, the Message-ID, the three metadata strings and every group name, which
encode at least 17 octets shorter; four eight-octet heads need 16
(`fn-record-encode-producer-length-bound`, PRF-126). So widening the
allocator or the clock past 2^32 - 1 moves no profile field, and no saved
profile needs translation. The frontier frame's payload is the format-2
deterministic uint below 2^32 and the eight-octet head (canonical only above
2^32 - 1, RFC 8949 §4.2.1) from 2^32 to 2^64 - 1; the format-2 reader is kept
by name and the format-3 reader agrees with it on everything it accepts
(`fn-bs-frontier-decode-extends-format-2`), so no frontier file is rewritten.
An image before format 3 refuses a wide frontier frame by its payload bound,
never misreads it. The width guarantees are fn's; no RFC requires them.

The producers, and where each stops today:

- sequence, transaction ID, generation: the durable allocator
  (`fn-sf-prepare-record`, the frontier). Its successor
  (`fn-bs-frontier-next`) still stops at 2^32 - 1: the file machine
  (`fn-sf-statep`), the observed open (`fn-sn-open-observed`), the checkpoint
  (`fn-checkpointp`, `fn-checkpoint-restore`) and its TREE naturals
  (`fn-cpc-treep`) and the consumer candidate bound read the frontier as u32
  (PKT-244).
- stamp: `fn-record-stamp-of-observation`, seconds below 2^32 or
  `:clock-unusable`; the checkpoint's TREE naturals carry an article's stamp,
  so widening it waits on the same codec (PKT-244).
- charge: the POST boundary (`fn-sbud-post-boundary`, `:charge-bound` above
  2^32 - 1) and the BP policy (`fn-bpi-policy-p`); the charge is the one
  field the ceiling cannot absorb.
- the article producers (`fn-sn-article-record` from the served POST, the
  developer `store post` and BP ingress): charged `fn-sbud-article-figure`
  of their own counts before a transaction ID is reserved; the Python BP and
  owner clients ask the same verdict (`fn-store-sn-article-verdict`). The
  signed composite (kind 4) and peer-carried events are checked against R on
  their actual bytes and are not yet charged the article figure before
  reservation (PKT-244).

The history bound H is kept by admission, not only checked at open: an
article is charged the record ceiling of its own payload length and group
count at the produced widths (`fn-sbud-article-figure`), both by the
developer `store post` verdict before reservation and by the served prepare's
budget, so an admitted article never takes the committed history past H
(`fn-sbud-article-verdict-keeps-history`,
`fn-sbud-prepare-under-article-budget-keeps-history`) and the next open's
replay bound holds.  The figure does not read the profile.
Before this gate an article was charged a fixed 65 538 octets, and an article
past it could be accepted and leave the store unopenable (packet 1,
tests/acl2/profile-monotonicity-tests).

STO-002: acceptance publishes one transaction containing the source references,
duplicate-history effects, all local group allocations, and any obligations or
reservations accepted in that operation. No partially committed cross-post or
promised-but-unaccounted retention can become visible.

### The store's filesystem (STO-031)

STO-031: A Store opens only on the filesystem its record names: `init` records the identity of the filesystem the store root is on, every open observes it again and is refused by name when the record is absent, invalid or names another filesystem, and `store rebind-filesystem` records a deliberate move; the owner's start is refused by name when the store requires durable storage and its mount observably disables it.

A node's Store belongs on a provisioned volume (PKT-579). When the volume is
not mounted, the store path resolves into the directory underneath, on the
filesystem holding the mount point, and an open there would serve, or begin,
a different history. This is a local fn guarantee; no RFC speaks to it.

- **The record.** `filesystem-identity.fnmi` in the store root: an FN frame
  (magic `FNMI`, version 1, kind 1, ACL2's trailer) whose payload is five
  u16-length fields: the kernel's filesystem id (statfs `f_fsid`), the
  filesystem type, the mount point containing the store root, the mount's
  source, and the durability policy (0 or 1). `init` (operator and
  developer), `store import` and the developer probe write it once, by stage,
  fsync, rename and a root fsync (books/store-mount-identity.lisp
  `fn-smid-record-plan`; host/native/io.lisp `fnn-record-filesystem-at-init`).
- **The observation.** Linux: `f_fsid` from statfs, and the line of
  `/proc/self/mountinfo` whose mount point is the longest component prefix of
  the root's resolved path (a later line wins a tie), parsed and selected in
  ACL2 (`fn-smid-mountinfo-step`; a line past 65,536 octets makes the
  observation unobserved, never guessed). OpenBSD and macOS: statfs's
  `f_fsid`, `f_fstypename`, `f_mntonname`, `f_mntfromname`.
- **Same filesystem** (`fn-smid-same-filesystemp`): type and mount point
  agree and, where both fsids are reported (nonzero), the fsids agree; where
  either is not (OpenBSD reports zeros to an unprivileged process) the
  sources agree. A remount of the same volume on another loop device is the
  same filesystem; another volume at the same mount point is not.
- **The open** (`fn-smid-open-decision`, called by `fnn-acquire` before any
  other read, so by every open; it is `fn-smid-open-verdict` wherever a
  record is present): `:open`, or refused by name as `store filesystem
  unobserved`, `store filesystem unrecorded` (a root with neither record nor
  `config.json`: the empty directory where the volume should be), `store
  filesystem record invalid`, or `store filesystem changed: expected ...,
  found ...; mount the node volume or run `store rebind-filesystem` after
  moving the store deliberately`. Nothing is created or written at a refused
  open. A complete store with no record (made before the record, or whose
  `init` died before writing it) opens offline with a warning naming the
  remedy, and its owner's start is refused (`fn-smid-start-verdict`).
- **Rebind** (`store rebind-filesystem [--storage-require-durable on|off]`,
  operator; `store ROOT rebind-filesystem [on|off]`, developer): under the
  writer lock, with the profile and frontier loaded but the identity not
  checked, records the current observation, keeping the store's policy or
  setting it (`fn-smid-rebind-plan`).
- **The durability policy** (PKT-648, `fn-smid-start-verdict`): the owner's
  start of a store with policy 1 is refused by name when its mount carries
  `nobarrier` or `barrier=0` or is tmpfs or ramfs; with policy 0 it starts.
  The owner's start, `status` and `health` print the warning for such a
  mount (`fn-smid-durability-warning`); an ordinary open does not. `init` and `store import` record policy 1
  under a mission's configuration (the release and public node) and 0
  otherwise (`fn-smid-init-policy`). ZFS `sync=disabled` and a drive's
  volatile cache are not observable here and remain the operator's
  obligation (docs/operator.md, Storage requirements).

### Compressed payloads: DEFLATE over a shipped dictionary (STO-037)

STO-037: A stored payload may be held compressed: a raw DEFLATE stream over a shipped preset dictionary named by its BLAKE3 digest, decoded by the verified inflater, never transcoded at rest

A stored article record may hold its payload compressed
(`books/payload-lz-record.lisp`, the frame `fn-z`: DICT-ID, the payload span,
the record without it, and C). C is a raw DEFLATE stream (RFC 1951) made
over a preset dictionary (RFC 1950 section 2.2), and DICT-ID names that
dictionary: the first four octets of its BLAKE3 digest, 0 for none
(docs/extensions/nntp-compress-dict.md).

- **One format, one decoder.** C decodes through the verified inflater's
  payload decoder (`books/payload-deflate.lisp` `fn-pzd-decode`, over
  `books/deflate-inflate.lisp`). The COMPRESS wire uses the same inflater.
  An :ok answer is exactly N octets, and the stream ended at its final
  block or at a sync flush at the end of its input.
- **The encoder is untrusted.** zlib (`host/native/fn-deflate.c`
  `fn_deflate_payload`, level 9, over the current dictionary) proposes C.
  The append takes the frame only when the decoder gives the span back
  (`fn-lzr-append-decide`). A wrong candidate is a named store fault; a
  candidate that does not shrink the record keeps it as it is.
- **Dictionaries are shipped, append-only and kept forever**
  (`books/payload-lz-dicts.lisp`). New payloads use the current one. A
  payload is never transcoded at rest, and a frame whose DICT-ID the table
  lacks is refused by name (:lz-dictionary), never guessed.
- **The served read** decodes C over pooled host buffers
  (`fn-pzd-decode-bufs`). KEYSTONE `fn-lzr-decode-bufs-is-the-lz-value`
  says the octets are the value A-DURABLE-LZ names. Because every buffer is
  rebuilt per payload (`fn-zin-payload-bufs-is-payload-with`), nothing
  carries from one read to the next.
- **The digests stay over the original octets** (D25): content identity,
  Message-ID, signature and Cancel-Lock are computed before the append.

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

STO-033: The commit batch and the close rule. One batch of prepared commits is
in flight at a time (the storage-log design of 2026-09-27, section 3.3: the
batch of PreparedCommit tokens over the record log), and its members are
ordered by their prepare. A member is acknowledged only after the batch's
barrier, and in order. The batch closes when the log thread returns from the
previous barrier or at the operator's live bounds `log-batch-records` and
`log-batch-octets` (`:set-limit` slots of the running configuration: a work
bound per scheduling step, never a profile field), and never on a timer: at one
poster the batch is one entry and its latency one barrier. A failed barrier
makes every member in flight or waiting uncertain and fences the store; recovery
holds the committed records followed by a prefix of the batch, so an
acknowledged member is never lost and an unacknowledged one may appear
(STO-004, STO-005). The batch layer is `books/owner-batch.lisp`; no host line
calls it until the store node's article commit moves onto the token and the log
kernel.

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

The record log's open applies that distinction (lane log-corruption,
2026-09-27, PRF-316, `books/store-log-damage.lisp`). A crash leaves at most
the ONE pending write torn at the frontier over the segment's preallocated
zeros, so after the scan stops ACL2 probes every write unit of the rest of
the segment. An entry there that validates under the predecessor it claims
is damage to committed data followed by valid history: the open refuses
`reason=log-damaged at=SEGMENT:OFFSET first-valid=Q valid-after=N records=M`,
exit 1, writes nothing, and the owner does not start (`status` and `recover`
alike; `log-chain-broken` keeps its meaning). No valid entry after the stop
is the torn tail: recovered to the last complete entry with a
`log torn-tail at=SEGMENT:OFFSET debris-units=D` line. Damage confined to
the LAST entry cannot be told from a torn tail and is recovered with that
line. The operator's choice is explicit: `store ROOT recover --repair
truncate SEGMENT:OFFSET` names exactly the refused damage of the active
segment; the segment's octets are kept as `quarantine/SEGMENT.damaged-at-OFFSET`
first, then the log recovers to the stop and replays the prefix (`log
repaired ... dropped-valid-entries=N dropped-records=M`). A repair naming
anything else is the same refusal. Restoring the damaged entry from a
snapshot or a peer is not offered yet (open). The history read again for a
checkpoint or an export refuses by name when the closed segments no longer
chain to the active segment's genesis.

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

**Scope, 2026-09-27.** The pack tranche below (and PRF-073) describes the
per-file layout `fn-store-8`, which no image opens any more (STO-028). On
the one format, `fn-store-9`, compaction is a state checkpoint that rotates
the record log and drops the segments it covers (STO-034), and content
reclamation is `store reclaim` over the log (STO-028); the pack verbs
refuse there by name (`reason=record-log`). Measured on hbox at 40,000
articles of 2 KiB (planning/evidence/log-recovery-2026-09-27.md section 4,
a loaded box): `store compact` 98 to 139 s at 4.7 to 7.5 GB peak RSS, the
open from the checkpoint afterwards 14 to 19 s, against 2,963 s at 16.4 GB
for the format-8 compaction it replaced; the log's 268 MB became a 129 MB
checkpoint and a 1 MiB segment. The memory of a compaction is not yet
bounded by the step (PKT-842). The text below stays as the record of the
per-file route until its code and rows are retired (PKT-838).

The per-file compaction tranche published an immutable selected transaction
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

STO-034: Segments, rotation and drop (format `fn-store-9`; design
2026-09-27 storage-log section 6; books/store-log-segments.lisp). The record
log is the segments `journal/NNNNNN.log` (six digits, from 000001); the
highest present is the active one. A state checkpoint's capture ROTATES the
log in three programs (lane operations; books/store-log-segments.lisp
`fn-lgs-spare-program`, `fn-lgs-rotate-program`,
`fn-lgs-rotate-durable-program`): the next segment is created in `staging/`
as `.stage-segment-NNNNNN`, preallocated and fenced (cuts `rotate-created`,
`rotate-fenced`) off the owner mutex; the switch, under the mutex with no
batch in flight, renames it into `journal/` (cut `rotate-renamed`), its only
I/O; `journal/` is fenced (cut `rotate-durable`) off the mutex by the new
segment's first fence, before any member written there is acknowledged, and
by the publication before the checkpoint's F row names the segment with the
closed segment's last trailer as its genesis
(books/store-log-rotate-spare.lisp: `fn-lgrs-journal-fence-names-the-acknowledged-batch`,
and without that fence an acknowledged batch can be left under the staging
name only); after the checkpoint is installed (rename and root fence) the
segments below it are unlinked and `journal/` fenced (cuts `drop-unlinked`,
`drop-durable`): the replacement is durable and reachable before old storage
is reclaimed (STO-007). The open reads the checkpoint first, scans the
segments from the one its F row names with the chain carried across them,
and refuses by name, exit 1: a segment missing between that one and the
active one (`history-short-of-checkpoint`), segment 1 gone with no checkpoint
the open can use (`checkpoint-damaged`), and an entry that validates under
another predecessor (`log-chain-broken`, never read as a torn tail). A death
at any rotation or drop cut reopens to the same history: a spare staged but
not renamed is a staging orphan the writable open sweeps (segment K stays the
active one); after the rename and before `rotate-durable` the new segment is
an interrupted rotation the open completes, holding nothing acknowledged; and a covered segment left by a drop is dropped again
(`fn-lgs-open-plan-scan-ignores-covered`). The history the open replays after
the drop is the full chain's (T8, `fn-lgw-segment-drop-preserves-the-open`, over the streamed open).
`store compact` on a `fn-store-9` store is a checkpoint with rotation
followed by the drop; the owner's automatic checkpoint does the same. On a
running owner `store compact` and `store checkpoint` are a request to that
publication (HST-034, books/owner-compact-request.lisp
`fn-ock-requested-next`: due at any suffix, never a second in flight, never
past a deferral), answered by name over the control socket; compaction
needs no stop.
The open reads each segment one entry at a time (books/store-log-stream.lisp,
`fn-lgw-step`, called by `fnn-log-stream-segment`; PRF-297, lane
log-open-stream 2026-09-27): the header, the entry's length, that entry's
octets, the step's decision; no string of the segment exists and the walk
keeps no record. Measured on the 10,000 x 32 KiB fixture (full replay,
hbox): live heap at the replay 6,217.8 to 640.3 MB, peak RSS 14.1 to
1.25 GB, wall 4:38.5 to 0:55.2 (planning/evidence/log-open-stream-2026-09-27.md
section 3); of the 640 MB, about 310 MB is the image's own world.

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
  is at most K (max-open-suffix). It then reads only the suffix (on
  `fn-store-9`, the record-log segments from the one the checkpoint's F row
  names, STO-034, streamed one entry at a time since lane log-open-stream,
  2026-09-27; on the retired per-file layout, the transaction files with
  sequence at least S) and calls `fn-sco-open`, which equals the full
  open of the whole history (`fn-sn-recover-from-checkpoint-equals-full-recover`).
  Otherwise it replays in full. Status prints `open=checkpoint:S suffix=k`
  or `open=full-replay reason=R` (absent, corrupt, ahead-of-history,
  suffix-exceeds-k). **K is the fast path's threshold, not a guaranteed
  maximum suffix** (decided 2026-09-26, gpt-6's review section 2; ember may
  choose the guarantee later): a suffix within K is served from the
  checkpoint, a longer one is the full replay, the honest fallback to the
  same state (`fn-ock-fast-path-within-k-by-definition`,
  books/owner-checkpoint-open.lisp). The suffix a publication leaves is
  about the commits made while it ran, which no due rule can bound; when it
  exceeds K the remedies are a cheaper publication, reserved service or
  admission limiting, never a second capture meanwhile.
- **Not yet.** K0 coverage of the publish program's root rename is open.
  (The owner opens from the checkpoint and publishes at K/2 since
  owner-checkpoint-open, PRF-083. The recovery-lag policy since
  checkpoint-pipeline-5, `fn-ock-publication-next`: ONE publication in
  flight, a due observation meanwhile ONE coalesced request (recorded, and
  nothing else: no second capture, no second estimate, no cancellation of
  the publication running), and when it finishes the owner decides again at
  the newest committed frontier by the same rule, at once rather than at
  the next accept; the durable S a finish records is the count the capture
  was handed, never the count when the write returned
  (`fn-ock-one-publication-in-flight`, `fn-ock-finish-binds-the-captured-prefix`).)

STO-016: The checkpoint open costs less than the full replay it replaces,
and a publication does not hold served commands.

- **The file carries the count.** The F row carries S and the frontier
  (`fn-sct-tables-of-capture`, STO-026); every committed event below S is
  one E row and one P row (its payload, once), and the load rebuilds the
  event index from E (`fn-sct-capture-of-tables-of-capture`): the record
  list is stored once, never twice. Nothing is capped: one row per event,
  whatever S. Every run's header carries S in its sequence field. The
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
  configuration history and the record list (by pointer) under its mutex,
  then builds the tables, decides, and encodes and writes them step by step
  on its own thread (`fnn-checkpoint-write-steps`, STO-026), and installs
  the result under the mutex again. What it writes is the file of the
  tables of the capture at the capture point (`fn-ockp-run-writes-the-file`
  over `fn-sct-tables-of-capture`, PRF-199).

STO-024: The owner's automatic publication is decided by name before it is
encoded and encodes through the octet buffer, never as octet lists.

- **The estimate and the budget.** Before any encode ACL2 computes the
  file's length from the tables' metadata, allocating nothing and touching
  no payload octet (`fn-ockp-estimate`, books/owner-checkpoint-writer.lisp;
  equal to the table codec's file length,
  `fn-ockp-estimate-is-len-file-octets`), and compares it with the
  profile's checkpoint budget, the file bound an open refuses a checkpoint
  past (`fn-ock-capture-budget` = `fn-sccr-file-read-bound`: three times
  `max-history-octets` plus one segment's framing), and with the free
  space the host observed less the maintenance reserve (STO-026). Past
  either bound the publication is deferred by name (`CHECKPOINT deferred
  reason=exceeds-budget|exceeds-space estimate=E budget=B`, and `status`
  carries ` deferred=... estimate=E budget=B` on its `checkpoint-file`
  line), nothing is written, serving continues, and the attempt is not
  repeated while the bound it named is below E
  (`fn-ockp-decide-defers-by-the-estimate`, PRF-200, over
  `fn-ock-publication-blockedp`). The budget bounds one publication's work
  by the operator's declared history (D27), not the data a store holds.
- **The stream.** The publication thread encodes the tables step by step
  into its own octet buffer (the abstract stobj fn-octets-pub of
  books/owner-checkpoint-writer.lisp, a second stobj congruent to the
  served attempt's `fn-octets`, so nothing is shared off the mutex), the
  buffer holding one step's rows and one segment's residue, never the file,
  and writes each step's frames straight from that buffer through the
  unchanged byte program (`fn-bs-scp-program`, the same five cuts). What it
  writes is byte for byte the table codec's file of the tables of the
  capture (`fn-ockp-run-writes-the-file`, PRF-199), and every frame is
  admitted by the reader's rule before the host writes it
  (`fn-ockp-admit-frames` over `fn-sccr-admit-segment`): a file the open
  would refuse is never completed.

STO-026: The state checkpoint is four tables (schema 3), each a run of
FNSC segments, holding every payload once, written by one resumable
pipeline in bounded batches through the publication buffer and read back
as the capture; a file of another schema is refused by name and the
journal replays.

- **The tables** (lane checkpoint-pipeline, 2026-09-26; D33, D34;
  books/store-checkpoint-tables.lisp). F: one row `(3 S FRONTIER
  REVISION)`. P: one row per committed event, its payload bytes (an
  article's payload, a composite's article-record bytes) or NIL. E: one row
  per committed event, the event with every octets leaf equal to its P row
  written as a reference `ref s` (one op added to the tree codec); the
  record's other fields are its own until the catalog slice. R: the four
  fold roots (the configuration fold paused at S, the identity context, the
  consumer cursor, the topic prefix state) with each stored article's
  payload written as a reference to its P row, found through the event
  index's Message-ID trie. No event index is stored: the load rebuilds it
  from E as `fn-sco-capture` does. The dedupe is by equality with P[s]
  (`fn-sct-refp`); a signed composite's carried record is a distinct
  object with distinct bytes, so its payload in R stays literal (PKT-583).
- **The frame.** Each run is `fn-scc-chunks` of its rows' programs in
  segments of at most the profile's record bound, framed and chained from
  the genesis by the unchanged FNSC frame (schema byte 3, sequence S);
  `fn-scc-decode-segments`'s refusals and the per-segment admission
  (`fn-sccr-admit-segment`) are reused, and the admission refuses another
  schema by name: `open=full-replay reason=checkpoint-schema`
  (`fn-sco-select-named`). One store format (D34): no schema-2 reader.
- **The pipeline** (books/owner-checkpoint-writer.lisp: the definitions and the step-level twins; books/owner-checkpoint-pipeline.lisp: the loop keystone and the invariants). Capture (O(1)
  under the mutex: the base, the configuration history, the record list by
  pointer, the frontier, the free space, the source revision); the estimate
  from the tables' metadata without encoding or touching a payload octet,
  equal to the file's length (`fn-ockp-estimate-is-len-file-octets`); the
  decision by name before any allocation (`fn-ockp-decide`, PRF-200:
  `exceeds-budget` against `fn-ock-capture-budget`, `exceeds-space` against
  the free octets the host observed by statvfs less `fn-smr-reserve-octets`;
  the retry blocked while the bound it named is below the estimate); then
  `fn-ockp-step` per batch of 1,024 rows (a work bound per step, D27),
  the full segments framed and admitted by the reader's rule before they
  are handed to the host, the residue under one segment kept for the next
  step. The owner's thread and the verb run the same steps
  (host/native/io.lisp `fnn-checkpoint-write-steps`), each step's frames
  written through `fn-bs-scp-program`'s staged file between its `created`
  and `written` cuts: no new program, no new cut (SCN-129: a kill between
  two steps reopens with the old checkpoint and the stage is swept).
- **What is proved.** `fn-sct-decode-file-of-file-is-the-capture` (PRF-199):
  the reader's decode of the file written for the tables of a capture is
  those tables, and their value is the capture, for any segment size;
  `fn-sct-load-is-decode-file` (PRF-135): the host's buffer load is that
  reader on the frames' octets; so `fn-sn-recover-from-checkpoint-equals-
  full-recover` transfers unchanged. `fn-ockp-run-writes-the-file` (PRF-199,
  the loop): the octets of the host's steps, at any batch size and any
  segment size and from any initial buffer contents, are that file
  whenever the loop completes; its step facts are PRF-133's and the
  witness at batch sizes 1, 3 and 1000 is in
  tests/acl2/store-checkpoint-tables-tests.lisp.

### The snapshot page store (STO-035)

STO-035: The snapshot page store. The owner's snapshot is to become a copy-on-write page store (lane
arena-store, 2026-09-27; `books/pagestore*.lisp`; record
`planning/evidence/arena-store-2026-09-27.md`). One page file of 16 KiB pages
(2048 little-endian u64 words). A commit record (two slots per root, in page 0
for the owner's root: one barrier per commit; page 0 is the model's reserved
page, which `pgs-disk-keeps` keeps and the reclamation cycle's start marks,
so no allocation or sweep ever hands it out) names a directory run whose
entries (address, writing txid, BLAKE3-256 digest) name table pages of 341 entries,
whose entries name the data pages. A snapshot writes only its dirty data
pages, the table pages holding them, the directory run and the record, all to
fresh space, then one fdatasync. The open verifies the record's check, the
directory, and (lazy) the pages its own commit wrote or (eager) every page;
the rest is verified at first touch and a mismatch is refused by name.
Limitation (L-PGS-LAZY-SHAPE): the model's lazy open checks the shape of every
table page; the host's lazy open checks only the table pages the record's own
commit wrote and checks the others (digest and shape) at first touch, so a
malformed older table page is refused at its first touch, not at the open. Every
decision is ACL2's; the host has two byte primitives. Proved (PRF-344):
commit-then-open denotes the committed state; a crash anywhere opens on the
committed or the previous state, the previous one unless the record landed;
other roots and forks are isolated; allocation always answers fresh
addresses; reclamation never frees a page a valid record of any root keeps.
Named: A-PGS-HOST-IO. Scenario: SCN-186. Not yet the owner's path: the owner's state (fn-hist
first) moves onto these pages in a later step.

The page image format FNADTSN2 (lane arena-store-3; `books/proto/adt-bytes.lisp`;
coordinator decision 2026-09-28: free region placement, the index as a value).
Every owner state on these pages is an image of 16 KiB pages (2048
little-endian u64 words), image page K the page store's logical page K. Page 0
is the header: magic "FNADTSN2" (the octets, word 0), format version 2, the
schema digest (words 2-5; a digest of the schema's own octets: another schema
is refused by name, never rebuilt), N (the record count), R (the region count:
one per column, then the pool), per region its first page and its length in
octets, then NPAGES (the image's page count), zeros to the end of the page. A
region takes the power-of-two number of pages its length needs
(`adt-cap`), zero-padded; a column holds N little-endian cells, the pool the
records' variable-length octets. Placement is free: the decoder
(`adt-decode`) and the history's open check (`fn-hp-w-header`) accept any
placement where every region lies after page 0, inside NPAGES, and apart from
every other (`adt-placement-ok`), and refuse any other by name (:placement);
pages no region holds are not read. The canonical image (`adt-ser`, a function
of the value alone) places the regions in order after the header. For the
history (`books/history-pages-placed*.lisp`), the open's header check, the row
read and the writer are proved over ANY such placement (PRF-342: an image
whose pool sits on a page past a free one reads and appends as the canonical
one does; the writer marks dirty only the header and, per region at its
start, the pages its new octets overlap). A region that outgrows its pages
is to move to new pages allocated at the image's end, nothing else moving:
the writer answers the named verdict (:grow R) and the growth step (the move
and the append into the moved region's new pages) is not yet landed
(L-HP2-GROWTH). The pages a moved region leaves stay in the image, unread,
until the page store can drop a logical page (L-HP2-VACATED: they are not yet
handed to the page store's reclamation). A keyed ADT's image carries its Message-ID
index as a VALUE: one more region after the pool, an open-addressed table of
2^k u64 slots (0 empty, else the row's index + 1) under the salted FNV-1a of
the key, at most half full, read as stored and never rebuilt at the open; the
history's image does not carry one (no served path looks a history row up by
Message-ID; the MKEY column holds each row's bucket), so the first keyed image
on these pages brings it. FNADTSN1 (contiguous placement, no NPAGES word) is
refused :magic: format 10 stores are fresh (D34). The page digests are the
page store's table entries (the image has no second digest table) and are
the store's digest, BLAKE3 (the value of fn-digest's attachment): the word
digest the host calls is proved to be `fn-blake3` of the page's
little-endian octets (`pgs-x-words-digest-is-blake3`,
`books/pagestore-words-blake3.lisp`; SHA-256 until 2026-09-28, no format
change: FNADTSN2 pages are format-10 structures).

The history's image (PRF-342, lane arena-store-2; `books/history-pages.lisp`).
The first owner state on these pages is the history (fn-hist). Its snapshot
is the FNADTSN2 byte form (`books/proto/adt-bytes.lisp`) of one row per
event: MKEY (1 + the salted FNV-1a bucket of the event's key Message-ID, 0
when none), the length of the event's tree octets (the checkpoint's proved
tree codec, `fn-scc-encode`), and those octets zero-padded to a multiple of 8
(so every append writes whole words). Image page K is the page store's
logical page K, and the page store's per-page digest is the image's
page-digest leaf (BLAKE3 of the page's octets): there is no second digest
table. Proved: the decoder
inverts the image; an append changes only the header page and, per region,
the pages its new octets overlap, at most 11 + (32 K + the new trees'
octets) / 16384 pages for K events while no region doubles. Limitation
(L-HP-DOUBLING): until the growth path lands, a region that doubles is the
writer's named verdict (:grow R); FNADTSN2's free placement lets it move alone
(the growth path, open). The Message-ID bucket heads are not in the image
(see the index as a value above). The open reads the
image's page 0 only: the header check (magic, version, the schema digest,
the region count, placement, column sizes, the page count) answers N and the
regions, and another schema's image is refused by name (:schema), never
rebuilt. Reads return need-verdicts: a page not yet verified answers
(:need-table T PHYS) / (:need-page P PHYS) and the host fills it with its two
byte primitives, verifies it against its table entry and asks again; the
first read of a row pays at most its four cells' pages and its pool entry's
pages. Proved: over any page store state whose verified pages hold the
image's words, the header check and the row read answer the history.
The writer (lane arena-store-3; `books/history-pages-write*.lisp`) appends
an event into the page store's words from the header answer the host
carries (N, the lengths, the starts): six blocks (the header's words 6-17,
one cell per column, the padded tree in the pool), written only when every
page they touch is verified (else the need-verdict, nothing written) and
only while no region changes its cap (else the named verdict (:grow R),
nothing written). Proved: the appended history's image words are the old
ones with those blocks in place; over any state whose verified pages hold
the image, an :ok leaves them holding the appended history's image,
answers its header, and marks dirty only pages of the proved dirty list
above, each verified, so the commit writes exactly the new image's pages.
Not yet the owner's path: the region growth (FNADTSN2), the host wiring and
the snapshot commit are the next milestones.

The owner's records as an abstract stobj (PRF-372, lane arena-store-6;
`books/history-records.lisp`; coordinator decision 2026-09-28: the owner's
records become the logical value of an abstract stobj whose executable is
the history image, not a twin per consumer). `fn-hrecs` holds a history H
whose executable is H's first N events as the FNADTSN2 image on a nested page
store, then an in-memory suffix array of the events appended since the
image's last append; H itself is a ghost (the logic carries it, the
executable never builds it). The meaning is `fn-hrecs-faithful`: H is the
image's events then the suffix's, and every verified page holds H's placed
image; every export keeps it. The exports are pure and a read of a row
whose page is not verified answers (:need-page P PHYS). The one retry loop
(`fn-hrecs-read`) serves each need by one fill (the host's byte primitive
`fn-pgs-fill-realize` at the address the table names for P, then the page
store's digest check) and asks again. Proved: an :ok answer is record SEQ of
H (or (:refused :seq) past its end); the loop keeps H, its faithfulness and
the page file's relation (`fn-hrecs-disk-faithful`: the page file holds the
image's page for every page not yet verified) and never stops for fuel (each
fill verifies an open page); the flush (oldest suffix event into the image,
relocating a region that outgrows its pages) keeps H whatever it answers.
A-PGS-HOST-IO enters at the fill and nowhere else. Not yet: the Message-ID
lookup and the store's readers moved onto it (the owner's store still holds
the record list), the open's adopt of a committed image, the flush's retry
over pages not yet verified, the commit.

The store's records over the committed image (PRF-373, lane arena-store-7;
`books/history-records-disk.lisp`, `books/store-records-field.lisp`;
coordinator decision 2026-09-28). The kernel state's records field
(`fn-sf-records-field`) is a snoc-list of the whole history or a BASED field
(:hrs-based HANDLE . SUFFIX): HANDLE names a committed history image (the page
file, the page store's root record, the image's MKEY salt and header) and
SUFFIX holds the records appended since. `fn-sf-records` of a based field is
`fn-hrs-disk-history` HANDLE followed by the suffix's list; the image's
history is DEFINED, not assumed: the decode opens the page store from the
root record (the directory run and every table page from the file through
`fn-pgs-fill-realize`, each checked by the page store's open), adopts the
header and reads rows 0..N-1 by the retry loop (each page it needs filled
from the file and digest-checked). It answers exactly N rows; a decode that
is not clean (the open or a page refused) is a fault by name
(history-image-fault: a recovery event), never a silent value. Proved: when
the page file holds H's image at the addresses the committed tables name
(`fn-hrs-disk-holds`) and the decode is clean, the history is H
(`fn-hrs-disk-history-is-image`); a based field's list is then H followed by
the suffix; the commit's append goes onto the suffix in O(1) and the count
(image N plus the suffix's), the last record (the suffix's when it is not
empty) and a record past the image read in O(1) / O(distance from the newest)
without decoding. The transitions that keep the history keep the FIELD in
the logic too (`fn-sf-remake`, the commit, the success), so a based state
stays based. An unmigrated reader of the whole list pays one decode (the
lazy decode); the served readers move to `fn-hrecs-read` one at a time. No
path builds a based field yet: the served open's adopt of a committed image
is next.

## History classes and lifetimes

STO-010: every class of durable state the store holds has a stated lifetime,
the future decision that needs it, and the capabilities that may remove it,
each under a named proof obligation; no other operation removes it.

Status: contract for M5 (review of 2026-09-24,
[direction review](../planning/review-2026-09-24-gpt6-direction.md) §M5). The
committed-history marker (STO-009) was implemented on the per-file layout.
Content reclamation over the record log is `store reclaim` (STO-028, lane
log-recovery 2026-09-27, PRF-271); history compaction is not implemented;
the rows below are the obligations an implementation must discharge. Where a lifetime depends on policy that is
not decided, the row says **open**.

Three capabilities may ever remove durable state. They are different
promises and each has its own proof obligation:

- **Packing** (P) moves bytes into fewer filesystem objects. It keeps the
  history and its semantic contents. Obligation: the open after the removal,
  at every cut, hands replay the identical record list (PRF-073). On
  format 9, `operator CONFIG store compact` (the checkpoint's rotation and
  the drop of the covered segments, STO-034: the checkpoint keeps every
  record, which export writes) is this capability and nothing else; the
  per-file `pack`, `pack-reclaim` and `pack-retire` were, and refuse on
  format 9.
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
  and no active reference pins them: a reader's pinned archive or an
  unresolved BP handoff. An E2 consumer position is not such a reference: it
  is a committed Store-event prefix and creates no retention pin (the selected
  no-implicit-pin profile, [consumer progress](consumer-progress.md)); a
  consumer whose content was reclaimed sees an explicit unavailable gap. The record that the bytes existed, and
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
| Consumer positions (`:consumer` `fnce`: bootstrap, register, ack, rebase, unregister, rollover; `books/consumer-*`) | What each consumer declared through which committed Store-event prefix; the next registration epoch | Each entry until superseded by the next ack, rebase or unregister for that consumer. The epoch scalar: forever | P. H: into the latest entry per consumer plus `next-epoch` (the state `books/consumer-position` already carries), with a mapping that keeps every live position's prefix. They pin nothing, so they do not bound C (a retaining consumer mode would be a separately charged durable hold: PKT-165) |
| Topic admission (`:topic-admin-install`, `:topic-anchor`, `:topic-admit`) | Admitting later topic events (parents, authorship, admin) | Forever (**open**: experimental) | P only |
| Submission outcomes | Local POST: the accepted article record, which answers a retry with the same Message-ID as a duplicate. Refused and uncertain outcomes are not persisted beyond the burned reservation. BP submissions: the workflow and handoff records | As the article record / as the BP rows below | As those rows |
| Unresolved BP handoffs and obligations (FNBS directory: dispatch, delivery, deletion, conflict, family, forward rows; `books/bp-fnbs-*`) | Custody, retry, delivery and deletion reports, conflict evidence | Until resolved; then an outcome summary for duplicate and replay refusal (**open**) | Separate namespace. None of P, H or C touches it today (**open**) |
| Allocation frontier (`allocation-frontier.json`, FNSM kind 2) | Next transaction ID; an ID once reserved is never reused, including burned ones | Forever; one monotone value | None |
| Committed-history marker (`committed-history.json`, FNSM kind 3, STO-009) | Detecting a lost committed suffix at open | Forever; one monotone value | None. H must write a summary whose record count the marker still bounds (the summary counts as the records it replaces) |
| Local number frontiers and watermarks (per-group next number) | Allocating a number never used before in that group | Forever. Today derived by replay from article records | H must carry every group's high-water in the summary (numbers are never reused, even for removed articles) |
| Anti-resurrection summary | Refusing, or deciding by policy, a re-offer of a removed Message-ID or content identity; never reusing its numbers | Forever, once it exists | None. It does not exist yet: D13 is its precondition, and H and C are not admissible without it |
| Store profile (`config.json`, FNSM kind 1) | Every open-time bound; the budget | Forever; written once at init or import (D34) | None |
| Configuration history (`config/`, generations) | Current served groups and domain; the generation that local-post provenance cites | Current generation: forever. Older generations: while a record's provenance cites them (**open**) | Not in the Store transaction namespace. No capability today |
| Pack generations and selection marker (`packs/`) | The selected pack reconstructs the covered prefix | The selected generation: while it is selected. Older generations: redundant | P (`pack-retire`: older generations only) |
| Whole-state checkpoints and auxiliary images | A differential comparison at open. Derived, never authoritative | While selected | May be discarded; replay remains authoritative |
| Staging names (`staging/`) | None: never authority (`books/store-sweep`) | Until the recovery sweep | The sweep |

**What per-file compaction relieved** (format 8; on format 9 the rotation
and drop remove whole segments, STO-034). It relieves the transaction-file count
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

(The marker below is a file of the per-file layout `fn-store-8`; on
`fn-store-9` the record log's chain and its named open refusals, STO-034,
detect a lost or spliced suffix.)

STO-009: a committed-history boundary is written after each commit and before
its acknowledgement, and every open refuses, by name, a record history
shorter than it; a burned allocation never trips it.

STO-022: The durable reply's barrier cost is the publication program's and
nothing less.

On the record log (format 9, the only format an image opens: format 8 is
refused by name at the profile's open) the boundary is the log itself: M := D
(design 2026-09-27 storage-log section 3.4). A record is acknowledged only
after its batch's barrier (P-BATCH, `fnn-log-fence`: the segment's fdatasync
and the log kernel's fence), so the last complete entry of the log is the
committed history, and an open that scans the segments
(`fnn-recover-log`, P-LOG-RECOVER, `books/store-log-segments.lisp`) finds
every acknowledged record or refuses by name (`log-chain-broken`,
`history-short-of-checkpoint`, `checkpoint-damaged`). There is no separate
marker object, no marker program and no catch-up: the per-file layout's
`committed-history.json`, its host writer and its open check, the marker books (`store-history-marker`, `store-history-required`,
`byte-store-marker-program`, `byte-store-marker-candidates`, `byte-store-k0-marker`)
and PRF-076 and PRF-169 were deleted with the per-file layout (lane
log-recovery-2, PKT-838). A burned reservation leaves no entry, so it never
shortens the scanned history. The barrier cost of a served commit is the
batch's: one fdatasync of the segment per batch, shared by its members.

Not detected: replacing the whole store with an older valid copy, which needs
a freshness anchor (D14); the configuration history and the BP stores.

### Content reclamation under D13 (STO-014)

STO-014: Content reclamation under D13: an operator retention rule, a per-article decision over every holder, and a tombstone that keeps every decision the history needs.

RET-008: A per-group expiry policy is an authorized release: the operator's keep/default/purge days and octets window, honouring a posted Expires: within the bounds, released through the one reclaim path with every holder still in force.

Status: decision, tombstone and served projection proved (PRF-088); the
host asks the tombstone-aware D25 verdict at every site; OVER, XOVER and
NEWNEWS drop a reclaimed article; `status` prints the rule and the
reclaimable, held, reclaimed, signed and kept counts (every article in one
class, PKT-844). The durable `store reclaim` verb is
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
holder that acknowledged number A in the group holds every number above
A: a per-group article-number holder. No caller constructs it from an E2
consumer position, which is a Store-event prefix in another coordinate and
pins nothing; the slot is reserved for an explicitly selected retaining
consumer mode, PKT-165), `held-feed` (a live peer not yet delivered it; a retired peer holds
nothing) and `held-bp-obligation`. The keystone says the executable test is
exactly "no obligation in the flattened list names the article" together
with the rule.

**The tombstone** replaces the payload octets of the article record and
nothing else: NUL `FN-RCL1`, a source flag, the payload's BLAKE3 digest, the
BLAKE3 digest of its D25 source under its own agent, the payload length and that
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
calls (`fn-store-existing-action`, `fn-rcl-action-over` over the stored
bytes) up to a BLAKE3 collision (about 2^-128 per chosen pair) on the compared
pair. Verdict lookup reads the Store's verdict slot, which reclamation does
not touch, and an article with a verdict is not reclaimed.

**The classes** (PKT-844; `fn-rcl-class-in`, books/store-reclaim-holders).
`status` prints each article in exactly one class: `reclaimable`, `held`
(a holder), `reclaimed` (a tombstone), `signed` and `kept`, and the five
sum to the report's `articles=N`
(`fn-rcl-store-classes-partition-the-articles`). `signed` is an article
an accepted authorship verdict other than `:absent` names: every kind-4
composite (a signed article, a served key statement among them). Its
payload is retained with the identity state that verdict belongs to and
article retention never releases it, under every rule, clock and holder
set (`fn-rcl-signed-article-is-never-reclaimable`); it is `signed` even
where the rule would keep it anyway, because the verdict, not the rule, is
its reason to stay. `kept` is the rest the rule keeps (keep-forever, too
recent, a rule the store cannot apply). Before PKT-844 a signed or
rule-kept article was counted in `articles` and in no class.

**Served**: ARTICLE, HEAD, BODY and STAT of a reclaimed article answer
`423 article reclaimed` by number and `430 article reclaimed` by
Message-ID. OVER answers 503 for it and NEWNEWS still lists it (open).

### Content reclamation's durable step: `store reclaim` (STO-017)

STO-017: History compaction and content reclamation are distinct; `store reclaim` removes released payload octets by checkpointing the rewritten history on the record log and dropping the covered segments, returning them to the file system.

On the record log (format 9, the one store format; STO-034) `store reclaim`
rewrites the history, replays the rewritten history, publishes its state
checkpoint with the log rotated and drops the segments it covers: the
released payload octets leave the disk with those segments
(host/native/checkpoint.lisp `fnn-log-reclaim-steps`). A death before the
checkpoint's install reopens the history as it was and a rerun reclaims
again; from the install on the open reads the rewritten history and a rerun
reclaims nothing more (`fn-rclp-events-idempotent`,
`fn-rclp-a-reclaimed-event-stays-reclaimed`).

The two operations (the Fable mandate, section 8):

- **History compaction** (replacing history by a summary sufficient for
  every future decision) is not implemented. Nothing here claims it.
  `store compact` (STO-012) keeps the exact event history: the checkpoint
  covers it and the drop removes only what the checkpoint covers.
- **Content reclamation** (`store reclaim`, books/store-reclaim-pack.lisp's
  rewrite, books/store-log-reclaim.lisp's decision) changes only the payload
  octets of released article records. Every event keeps its sequence,
  transaction ID, generation, Message-ID, groups, obligation ID, content
  subject, release evidence and stamp, and its charge falls to the one
  permanent history unit (below); every event that is not a legacy article
  record (an accepted-statement composite, a keyring snapshot, a statement
  verdict, a retention, consumer or topic event) keeps its bytes
  (`fn-rclp-events-keep-every-other-kind`).

The verb, offline under the exclusive lock after the ordinary open:

    fn operator CONFIG store reclaim [--dry-run | --recorded]
    fn operator CONFIG retention set {keep-forever | released-by-all-holders | release-after DAYS}

The instant is recorded (PKT-857, books/reclaim-instant.lisp, PRF-327).
Under `release-after DAYS` the context reads the clock; before a reclaim
rewrites anything it publishes one configuration record whose only delta is
the limit row `retention-reclaim-at` (the stamp plus one, 0 when the clock had
no wall reading), through the administrative authorization, publication and
read-back, and the report names it (`instant-record=NAME generation=G`). The
configuration that record yields names the rule and the instant the decision
used (KEYSTONE `fn-rci-recorded-context-is-the-decided-context`), and the
decision over it is the decision taken (KEYSTONE
`fn-rci-recorded-decision-is-the-decision`): the rewritten history is a
function of the pre-reclaim history and the record, so a copy of the
pre-reclaim store given that record reproduces the reclaim with
`store reclaim --recorded`, which reclaims at the recorded instant, records
nothing, and is refused by name (`no-recorded-instant`) where no reclaim was
ever recorded. A process death after the record and before the checkpoint's
install leaves the instant recorded and the history unrewritten: `--recorded`
completes it; a plain rerun records a later instant. This is not a store
format change: a `:set-limit` row of a slot no reader names is admitted by
every image and read by none (a new record-log event kind would be one: the
open refuses any record it cannot decode). Each reclaim takes one
configuration generation of the profile's `max-config-generations`; a
refused publication refuses the reclaim before any rewrite.

The host streams the history one record at a time into ACL2's fold
(`fn-rcls-step` under the store's context `fn-rclp-ctx`, which carries its
articles indexed by Message-ID so a record's step is one hashed lookup and
never a walk of the article list: PRF-934, row A8) and keeps each
record's rewrite (`fn-rclp-event`); `fn-lgr-decide-stream` then answers over
the fold (KEYSTONE `fn-lgr-decide-stream-is-lgr-decide`: the whole-history
decision, whose rewritten history is those rewrites): nothing
(`reclaimed=0`, exit 0, nothing written), `--dry-run` (the Message-IDs and
the octets a run would free, nothing written), a named refusal (`profile`),
or the reclaim, whose checkpoint holds exactly the rewrite of the committed
history (KEYSTONE `fn-lgr-decide-checkpoints-the-rewrite`). Which records
change: only a legacy article record whose article no holder names, whose
verdict does not need its payload, under a releasing rule
(`fn-rclp-events-never-touch-a-held-article`); what a changed record is: the
same record with the tombstone of its payload
(`fn-rclp-event-decodes-to-the-tombstoned-record`).

On a running owner the verb is a request the owner answers by name over its
control socket (Q16, `books/owner-reclaim.lisp`, PRF-927). The owner's
history is its rows (held rows whose payloads are arena handles); the pass
rewrites and folds them in chunks off the owner mutex (`fn-orc-chunk`), and
the rows' octets after the rewrite are exactly the offline rewrite of the
history's octets (KEYSTONE `fn-orc-rewrite-rows-is-the-offline-rewrite`;
the fold is the offline fold, `fn-orc-fold-is-the-offline-fold`), so the
decision names exactly the rewritten articles
(`fn-orc-decision-names-the-rewritten-articles`). Today the owner answers
`--dry-run` (its report in the owner's log, posts and reads continuing) and
refuses `store reclaim` and `--recorded` by name (`offline-only`) until the
installing pass (the rewritten capture's checkpoint, the live swap, the
drop) lands.

What becomes available again, precisely: the payload octets of each
reclaimed record, on disk when the covered segments are dropped, and in the
committed-record octets the admission gate sums (`bytes-used` of
`status`'s headroom line; `fn-rclp-freed-is-the-admission-count`), and the
retention charge of the reclaimed article's archive pin less one permanent
history unit (`charge-reserved`; `fn-rclp-rewritten-charge-is-the-history-unit`):
the pin itself stays, as `fn-retain-release` keeps one unit for a released
obligation, and no other obligation's charge changes. The release is the
operator's authorized retention rule. The transaction count is not released
(sequence numbers are history).

Retired with the pack layer (lane flip-cleanup, 2026-09-27): the reclaiming
pack (the decision that dropped the derived checkpoint, published, selected and
retired a pack generation, with its reclaim-* cuts), whose native steps
PKT-838 deleted.

### The maintenance reservation (STO-019)

STO-019: Admission leaves room for the release record and checks maintenance's temporary space against the disk, so a full store can always finish or safely abandon its own maintenance.

The decision (PKT-169, 2026-09-26) and its two halves:

- **The disk.** `store compact` and `store reclaim` write one state
  checkpoint beside the files present. The host reports the free octets of
  the store's filesystem (statvfs: `f_bavail` blocks of `f_frsize` octets)
  and ACL2 decides whether the checkpoint's estimate fits them
  (books/owner-checkpoint-writer.lisp `fn-ockp-decide`, through
  `fn-scka-publication-setup`). The history bound `max_history_octets`
  bounds the open's replay input; so H is not maintenance's budget, and a
  store at its history bound compacts and reclaims. (The pack's disk
  keystones went with the pack layer; the checkpoint's check has no
  keystone in PRF-129 yet.)
- **The release record.** A release is a Store record (the `:release`
  retention event). The served gates (`fn-smr-verdict-at` for every record
  kind, `fn-smr-article-budget-for` for the served POST and BP transit,
  `fn-smr-article-verdict-at` for the developer `store post`) admit a
  record other than a release only if, after it, the profile's own gate
  still admits one release record: one transaction of the profile's budget
  and the release record's codec ceiling (4,096 octets) within H
  (`fn-smr-admission-keeps-the-reserve`, `fn-smr-prepare-keeps-the-reserve`,
  `fn-smr-article-verdict-keeps-the-reserve`). A release consumes the
  reservation (`fn-smr-reserve-admits-the-release`). The reservation holds
  at init under every admitted profile and is kept by a profile upgrade.
  It is the profile's gate at kind `:release`, not a constant of its own;
  `status` prints it: `maintenance-reserve octets=4096 transactions=1
  held|short` (`short` only on a store filled before this rule).

The release's configuration record (`retention set`) is in the
configuration namespace, bounded by `max_config_generations` and the
configuration record bound, never by H: no Store admission takes its room.
The BP namespace keeps its own reservation, the FNBS received-namespace
debt cover (books/bp-node-debt.lisp); a bundle delivered into the Store
passes the Store gates above.

### The capacity vector (STO-020)

STO-020: The Store's capacity is a resource vector: admission never consumes the last resource an accepted promise needs, so a full store can complete its outstanding work, release, maintain itself, recover and reuse the space.

gpt-6's review of wave 2 (section 3) asks for "committed use + in-flight
reservations + completion/maintenance debt <= admitted capacity" with the
components apart. They are (books/store-capacity-vector.lisp, PRF-138):

| Component | Bound | Where admission keeps it |
| --- | --- | --- |
| Transactions (the `%020d.txn` namespace, the history's sequence numbers) | the profile's T, for the life of the store (compaction and reclaim keep the count) | the gate reserves one transaction per open debt and one for the maintenance release |
| History octets (unframed record octets, the sum the open counts) | H | the same, 4,096 octets (the release ceiling) per release |
| Completion debt: the open forward undertakings, each owing one `:release` record | counted from the history (`fn-cvec-record-debt`), carried by the owner as (K . DEBT) | an `:undertake` is admitted only if its own release still fits |
| The maintenance release | one `:release` record (STO-019) | as STO-019 |
| Retained payload charge | the retention ledger's capacity | pre-paid: a pin's charge includes its release unit, and a release never raises the reserved charge |
| Configuration generations (`retention set` is a configuration record) | `max_config_generations` | every other configuration record is refused the last generation (`max-config-generations`); the retention rule may use it |
| Workspace (disk) | the free octets the host observes | compaction and reclaim are refused `temporary-space` when the pack does not fit (STO-019); the pack is bounded by the compaction unit |

The gate (`fn-cvec-verdict-at`, `fn-cvec-article-budget-for`,
`fn-cvec-article-verdict-at`) admits a record other than a release only if,
after it, the profile's gate still admits DEBT' + 1 release records in turn,
DEBT' the open undertakings after it. With no open undertaking it is
STO-019's gate, except that an `:undertake` must keep its own release. Where
the vector holds, every open undertaking's release and the maintenance
release are admissible in any order (`fn-cvec-roomp-discharges-every-debt`).
It holds at init, is kept by every admitted record, by a release against an
open debt, by reclaim and by a profile upgrade; and a history of mixed record
kinds each admitted at its prefix is within H and below T at its actual
committed octets (`fn-cvec-admitted-history-keeps-the-vector`). The article
premise is PRF-126's (a u32 charge); every other kind's record must be within
its publication ceiling, which its codec bounds: the signed composite and
peer-carried producers are outside the producer-width proof.

The served owner reads the figures the gate compares without walking the
history (PRF-180). The committed count is the count the Store's derived event
index keeps (every put adds one; the index is built at every open and extended
by the commit's record-directory append); the committed record octets, the
completion debt and the peer carriage usage are the owner's (K . VALUE) caches,
advanced over the records committed since through the index's fixed-depth
lookup. Each equals its fold over the history while the index is the index of
that history, which holds of every owner the host reaches (PRF-144). A POST
therefore costs one lookup and one record's length, debt step and carriage step
per record committed since the previous query; the octets are folded once, at
open.

The disk is an environmental assumption, not a reservation: the observed free
octets are not owned, and a concurrent writer can take them. The pack write
then fails before the selection; the store reopens and the rerun converges
(the pack publication's cuts), so the outcome is refused or uncertain, never
torn. `status` prints `maintenance-reserve octets=R transactions=N debt=D
held|short`.


### Compaction of any length (P5; STO-012)

STO-012: Compaction covers a history of any length: `store compact` checkpoints the whole history with the log rotated and drops the covered segments; no unit of work bounds the history

On the record log (format 9, the one store format) `store compact` is the
state checkpoint published at the history's end with the log rotated, then
the drop of the segments it covers (host/native/checkpoint.lisp
`fnn-command-compact`; STO-034). The drop preserves the history the open
replays (`fn-lgw-segment-drop-preserves-the-open`, PRF-270), and the open
reads the checkpoint, then the segments its F row names. The checkpoint is
written from the state in bounded steps (`fn-store-sco-pass-step`), so no
unit of work bounds the history: tests/test_native_pack_chain.py compacts a
store of several thousand articles, and gated, the 20,000-article scale
store, over the log.

Retired (lane flip-cleanup, 2026-09-27; design 2026-09-27 storage-log
section 9 row 5): the chain of packs this section specified (P5,
2026-09-25: digest-linked `fn-x` links of one scheduling quantum each, the
chain walk and its decode-once memo, per-link temporary-space checks, the
reclaiming pack as a first link). Its native verbs went with the per-file
layout (PKT-838); its books (checkpoint-pack-chain, checkpoint-pack-chain-once,
checkpoint-pack-retire, checkpoint-compaction-preservation,
byte-store-compaction-correspondence, store-compact-verb,
store-compact-window) and host wrappers followed here. PRF-073, PRF-085 and
PRF-279 are retired.

## First executable scope

Model logical transactions before selecting sector alignment, frame lengths,
segment sizes, checkpoint layout, or a disk index. Then refine to bytes and the
chosen platform contract. These choices are M2 exit criteria, not details to
invent independently inside a file-writing adapter.

## One format and the archive

STO-028: A store has one format, `fn-store-10` (D34, fresh deploys; lane
format-bump-10): `init` and `store import` write it, and its committed
history is the record log, whose position 0 is the store's genesis
(STO-036; `journal/000000.log`), then the chained segments
`journal/000001.log`, ... (one self-checking chained entry per record or
batch, one barrier per batch of commits; planning/design-2026-09-27-storage-log.md,
lane commit-onto-log). Paragraphs of this specification that say "format 9"
describe the record log's mechanics, which format 10 keeps unchanged: the
format word, the profile's layout, the genesis and the stored digests are
what changed. There are no migrations (D38 withdrawn 2026-09-28: fresh
deploys, one format). The open the host calls reads config.json through
`fn-spo-config-open` (books/store-profile-open.lisp) and answers:

- a profile of this format: opened (`fn-spo-open-of-a-valid-profile-opens-it`);
- a sealed profile frame (under this build's digest) naming any other format
  word: `open refused reason=store-format: not an fn store of this release:
  redeploy fresh`, exit 1
  (`fn-spo-config-open-store-format-is-exactly-a-foreign-frame`);
- anything else (a corrupted file, or a frame sealed under another digest):
  the host's fault.

Nothing is translated at the open. On the record log `store compact` is the
log's rotation and drop (STO-034), and `store reclaim` is the log's content
reclamation (`fn-lgr-decide`, PRF-271). The pack verbs refuse by name
(`reason=record-log`). `store export DIR` writes the committed history the
open reads (the profile frame, the allocation frontier the log derives, each
configuration record and each committed record in sequence order: the
checkpoint's records then the log's, T8) with a MANIFEST whose names and
digest lines ACL2 renders (`fn-digest`, the store's digest: BLAKE3, b3sum's line format); the genesis is
not exported (it is the node's: its identity, salt and clock reading).
The export reads the history a chunk of records at a time and asks ACL2 for
each chunk's entries and MANIFEST lines (`fn-sxp-export-chunk`); for every
chunking the files and MANIFEST it writes are the whole history's
(PRF-366, `fn-sxp-stream-is-the-export`), so its memory is one chunk's,
never the store's. The entries are written without a per-file fence and
share ONE sync of the filesystem at the end (Linux `syncfs(2)`; elsewhere a
fence of every file under the archive); the MANIFEST is staged as
`MANIFEST.partial`, fenced after that sync, renamed onto `MANIFEST`, and the
archive directory fenced last: an archive counts as complete only once its
MANIFEST is durable. A crash anywhere leaves no MANIFEST, which the import
refuses by name before reading any entry (`import refused
reason=archive-incomplete entry=MANIFEST`), or the complete archive (PRF-370,
`fn-sxd-crash-is-incomplete-or-complete` over the byte model). The import
reads the archive a chunk of records at a time, the MANIFEST a piece at each
chunk's place, in two passes: the first decides with nothing written, the
second appends the records to the staged log; for every chunking the
decision is the whole archive's (PRF-369,
`fn-sxi-stream-plan-is-the-import-plan`), and a second pass that decides
otherwise (the archive changed under the import) is refused by name
(`archive-changed`) before anything is published.
`store import DIR [--FIELD N ...]` builds a new store of this format from
an archive of this format (an archive whose profile this format does not
decode is refused, `reason=profile store-format`; none is translated),
with its OWN genesis, writing the records into the log through its own append
and barrier, refusing a MANIFEST mismatch, a record out of sequence and a
profile the codec cannot represent by name, and admits it by the ordinary
open before it appears at its path. The import of an export replays the same
history under the same profile (PRF-205,
`fn-sxp-import-of-export-replays-the-same-history`).

The digest streams (lane format10-import, PRF-356): each line's value is
`fn-sdg-chain` of its canonical octets -- `fn-digest` of them when they are
at most one 65,536-octet block (`fn-sdg-chain-of-one-block`: the value
before), else a chain of blocks (the first block's `fn-digest`, then
`fn-digest` of 66, the running digest and the next block). `store digest`
pushes each octet into a one-block sink as the canonical encoding would
produce it (`fn-sdg-canon-rev-sink-is-the-chain-of-the-canon`), so a
1,000,000-record store digests in 5.9 GB, not past a 32 GB heap. The
history, pool, files, node, canonical and state lines of a store whose
stream exceeds a block changed value with this; no reader compares them
across images.

STO-036: the genesis. Position 0 of the log is `journal/000000.log`: exactly
one FNLG frame (version 1) of KIND 3, never a record kind the scan reads
(kinds 1 and 2), whose payload is the 32 zero octets of the empty chain and
then the genesis record, the frame-field record

| # | field | codec | content |
|---|---|---|---|
| 0 | magic | text | `fn-g` |
| 1 | format | text | `fn-store-10` |
| 2 | node identity | blob, 32 octets | drawn from the OS CSPRNG at `init` or `store import` |
| 3 | schema digest | blob, 32 octets | `fn-digest` of this format's schema text (`*fn-gen-schema-octets*`: the profile's fields, the entry kinds, the record envelopes, the identity profile, the digest) |
| 4 | profile digest | blob, 32 octets | `fn-digest` of config.json's frame |
| 5 | history salt | u64 field below 2^32 | four CSPRNG octets read big-endian |
| 6 | created-at | u64 field | the wall-clock reading at `init`, DTN seconds (a configuration record's stamp is milliseconds since PRF-378) |
| 7 | image revision | text | the creating image's source revision, or `unknown` |

(books/store-genesis.lisp, PRF-349). Byte for byte the file is the frame
header (`FNLG`, version 1, kind 3, the u32 payload length), the payload (32
zeros; then field 0 as its u16 length and 4 octets, field 1 as u16 and 11
octets, fields 2 to 4 each as a u32 length 32 and 32 octets, fields 5 and 6
as eight big-endian octets each, field 7 as u16 length and its octets) and
the 32-octet trailer `fn-frame-digest` of the protected prefix; it is not
padded (segment 0 is never appended to). Its trailer is the chain value
segment 1's first entry names as its predecessor, so every record the log
holds is chained to the genesis. `init` (books/byte-store-log-initializer.lisp,
books/store-init-log-publication.lisp) publishes it after the configuration
history and before segment 1 (stage, write, fsync, link, root fence, unlink,
then the journal/ fence `init-genesis-journal-fenced`); a re-run init keeps
an existing genesis (link EEXIST), never redraws it. Segment 0 is not a
segment index (`fn-lgs-segment-index` is positive), so rotation and the
checkpoint's drop never name it.

Recorded, not secret: the node identity is a generated id; the salt keys the
history stobj's Message-ID hash (books/history-columns.lisp `fn-hist-hash`;
the constant 0 before format 10, packet PKT-774), a node-local derived index no
answer depends on; created-at and the revision are provenance. Never in the
log: the node secret and the credential salts (host/native/admin.lisp
`fnn-csprng-octets` "credential salt"): account and key material, node-local.

Who reads it (and nothing else does): every open, through `fn-gen-open`
(host/native/io.lisp `fnn-genesis-open`), refuses by name a file that is not
a genesis frame (`genesis-damaged`), one of another format
(`genesis-format`), one of another schema (`schema-digest`: a store of this
word made under other structures) and one whose profile digest is not
config.json's (`profile-digest`: a config.json swapped under the log), and
hands the trailer to the scan of segment 1 (`fn-gen-open-of-the-genesis-init-writes`,
`fn-gen-open-of-octets-for`); the owner's install reads the salt
(host/owner-host.lisp `fn-hist-load`, `fn-gen-verdict-salt-is-32-bits`).
`store ROOT digest` prints `digest genesis` after `digest state` and outside
it; tests/test_native_replay_determinism.py test_g opens two imports of one
export (two genesis records, one history) and finds every other line equal.

Format 10's digest is BLAKE3 everywhere fn chooses (lane blake3-digest,
merged: frame trailers and the log's chain, content identities of algorithm 2
`*fn-id-algorithm-blake3*`, the MANIFEST, `store digest`, tombstones, the
catch-up chain); SHA-256 remains only where RFC 8315 forces it (Cancel-Lock,
books/sha256.lisp).

STO-029: `store import` publishes by an explicit program (P-IMPORT,
books/store-import-publication.lisp): the staged `ROOT.import-XXXX` is
created beside ROOT, every file of the plan is written and fsynced, every
subdirectory and the staged directory are fsynced, the ordinary open admits
it, it is renamed onto ROOT without replacing an existing destination
(renameat2 RENAME_NOREPLACE; an existing ROOT is `store-exists`, exit 1) and
the parent is fsynced. A crash at any cut, or an ambiguous rename or barrier
outcome, leaves no store at ROOT or the complete imported store (PRF-217).
Recovery classifies what it observes (ACL2 `fn-bs-imp-classify`): a staged
directory without ROOT is `interrupted-import` (no store was published;
remove it by name and import again); a staged directory beside ROOT is
`publication-uncertain` (run recover on ROOT, then remove the staged
directory), never "no store was created". `store export` is Store-history
export, not a node backup (docs/operator.md).

`operator init` publishes the empty store by the same program (P-INIT-PUB,
books/store-init-log-publication.lisp `fn-bs-init-log-program`: init's plan --
the three subdirectories `staging/`, `config/` and `journal/`, `config.json`,
the generation-1 configuration record and the empty log segment
`journal/000001.log` -- staged in `ROOT.init-XXXX`, init's cut names from
books/store-init-publication.lisp). A crash leaves no store at ROOT or the
complete empty store, whose segment is the empty log (PRF-268,
`fn-bs-init-log-program-crash-is-no-store-or-the-complete-empty-log`).
Before writing, ACL2's admission (`fn-bs-init-pub-admission`) refuses a
leftover staged directory by name (`interrupted-init`: remove it and init
again; `publication-uncertain`) and an existing ROOT without the store's
entries (`store-path-exists`). On OpenBSD, which has no renameat2, import
and init hold an exclusive flock on `ROOT.lock` for the whole program and
re-check ROOT's absence under it immediately before rename(2); the residual
(a process ignoring the lock creates an empty directory at ROOT in that
window) is an operator constraint (docs/operator.md).

