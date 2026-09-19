# Executable development status

fn has executable ACL2 components and a deterministic simulator. It is still an
experimental implementation: the components are not yet a durable, authenticated
news service. The broader contracts in `specs/` remain the target.

The latest [composed-store checkpoint](../tests/evidence/2026-09-18-composed-store.md)
passed its full frozen ACL2/simulator/Python batch with unchanged inputs (see
planning/ledger.md for current counts), plus an independent client over the
reopened store. The physical adapter
now uses the composed storage machine and its observed-image recovery gate.
Earlier evidence retains the independent CBOR and other interoperability cases.
The [closure queue](../planning/assurance-closure.md) tracks remaining work;
[BPv7 integration](../specs/bp-path.md) is an active architectural path.

The [follow-on batch](../tests/evidence/2026-09-18-reader-checkpoint-index.md) adds
reader/field guards, logical checkpoint equivalence, a derived index and the
legacy BP ingress model. The [actual BPA experiment](../tests/evidence/2026-09-18-bpv7-transport.md)
is separate transport evidence; the actual fn workflow/receipt exchange and
its scoped composition proofs now have the evidence described below.

## Current components

| Component | Executable scope | Remaining boundary |
| --- | --- | --- |
| [Acceptance](../books/acceptance.lisp) | Atomic local allocation, immutable Message-ID binding, staged publication, stale completion rejection, uncertainty fencing | Durable completion and recovery observations are abstract inputs; no physical disk is involved |
| [Acceptance invariants](../books/acceptance-invariants.lisp) | Mechanically checked preservation lemmas over the acceptance definitions | See the proof registry and certification evidence for the exact current theorem scope |
| [Wire framing](../books/wire.lisp) | Incremental CRLF lines, dot stuffing, article terminators, bounded retained input | Session dispatch and command conformance are separate; the bulk feed helper alone cannot decide when to enter article mode |
| [Wildmat](../books/wildmat.lisp) | Bounded strict UTF-8 grammar and dynamic-programming matching, reused for filtered LIST variants | UTF-8 progress/scalars, successful parsing and DP/reference correspondence proved; the whole-matcher work bound and this book's guards have targeted proofs (planning/ledger.md has current guard counts); parser work remains open |
| [CBOR primitives](../books/cbor.lisp) | Deterministic uint32 and definite byte strings, canonicality checks, bounded decoding | All primitive guards verified; native object/signature/batch formats remain open |
| [Article syntax](../books/article.lisp) and [invariants](../books/article-invariants.lisp) | Bounded header/body views preserve folding, unknown fields, and opaque body bytes; every successful parse provably reconstructs its exact source | Successful parse establishes syntax recognition and component bounds; this book's parser guards have targeted proofs (planning/ledger.md has current counts); the public parser work *value* is proved exact, its *cost* bound is a separate instrumented shadow roughly 16,000x above measured cost (see tests/evidence/2026-09-18-article-work.md); full RFC injection and physical resource bounds remain open |
| [Article fields](../books/article-fields.lisp) | Bounded RFC Message-ID and Newsgroups semantics, duplicate/missing/invalid classification, narrow proto-article routing checks over preserved views | Full required-field validation, injection, gateway provenance, authorization, and native signing remain open |
| [Transaction records](../books/records.lisp) and [invariants](../books/records-invariants.lisp) | Bounded schema-0 grammar, exact octet/string fields, variable group lists, complete record round-trip proof | Accepted-input canonicality and all record guards proved; provisional local format, native signature preimages remain open |
| [Retention](../books/retention.lisp) and [invariants](../books/retention-invariants.lisp) | Finite abstract accounting, distinct archive/forward pins, release gated on an exact stored evidence string match, permanent duplicate history; general release preservation and independent-pin/identity preservation | Evidence is a single admit-string equality, not an issuer/nonce/incarnation/authorization check; charging units are abstract, not measured physical bytes |
| [Node composition](../books/node.lisp) and [invariants](../books/node-invariants.lisp) | One transaction stages acceptance and its reservation; completion publishes both with permanent article-to-pin bindings; general transition preservation proved | Finite actual node traces preserve state and prior bindings; disk observations remain abstract, durable node release remains open |
| [Replay](../books/replay.lisp) and [invariants](../books/replay-invariants.lisp) | Contiguous committed records rebuild the actual node, obligations, and allocations; counter advance preserves invariants; replay has typed success/fault results from valid configurations | The last-good prefix `fn-replay-faultp` returns on fault is meant as diagnostic only, but no theorem forbids a caller adopting it; every current consumer honors that by convention, not proof. No checkpoint, rollback detection, or disk refinement claim |
| [Local store](../tools/run_store.py) | Immutable framed transaction files, data/directory barriers, locking, exact ACL2 replay, injected I/O failures | Development experiment; no qualified power-loss profile, independent freshness anchor, or byte-accurate physical reservations |
| [File-publication kernel](../books/store-files.lisp) and [invariants](../books/store-files-invariants.lisp) | One-use allocator reservations, immutable publication, actual replay and recovery gates; transition/crash preservation, stable-prefix and one-crash success retention proved | Finite file traces preserve state/history/successes; live node composition is separately proved; the physical adapter uses the composed kernel; physical syscall refinement remains conditional |
| [Live file/node composition](../books/store-node.lisp) | Fixed configuration, exact pending-record binding, actual node completion before acknowledgement and full-node replay extension | Mixed traces including refusal/abort and observed-image recovery gates certified in targeted runs; the physical adapter now reports its I/O observations through this composition; see planning/ledger.md for the current combined validation batch |
| [Journal](../books/journal.lisp) | Isolated record slots, barriers, surviving/torn volatile writes, explicit recovery faults | Integrity tags and a protected durable anchor are assumptions; no byte format, actual disk adapter, or general recovery theorem |
| [Exchange](../books/exchange.lisp) | Bounded atomic admission of immutable fact sets; duplicate/reordered merging and conflict evidence | Authorization is supplied; no serialized/resumable transfer, signatures, or durable scheduler |
| [Object assembly](../books/transfer.lisp) | Declared-byte and metadata reservations, out-of-order fragments, exact duplicates, missing ranges, and unverified complete candidates | General state/accounting and assembly/gap correctness plus hot-path work proved; the hypothesis-free `fn-transfer-missing-ranges` work bound (`transfer-public-bound.lisp:1041`) is certified but has no caller outside the transfer books, `reserve`/`add-chunk` remain uncosted, and byte-identical partial overlap is a conservative `:overlap-conflict` with no byte comparison; durable progress, validation and receipts remain open |
| [NNTP reader](../books/nntp.lisp) | Experimental reader commands including LISTGROUP ranges/cursors and filtered LIST ACTIVE/NEWSGROUPS over committed state, with independent response transcripts | Incomplete READER bundle, no POST, authentication, or signed injection |
| [Logical checkpoint](../books/checkpoint.lisp) | Capture of the exact prefix node, consumed frontier, actual suffix replay and full-replay equivalence; an explicit rejection theorem for a suffix that reuses a transaction id below the checkpoint frontier | No persisted checkpoint codec, publication or crash generation selection |
| [Derived index](../books/index.lisp) | Group/local-number materialization, soundness/completeness and independent range-query correspondence | Not yet a host index or performance improvement |
| [Legacy BP ingress](../books/bp-ingress.lisp) | Exact article ADU parsing, configured group mapping and composed-store admission | Actual host/workflow exchange is integrated for the lab profile; native signing and authenticated receipts remain open |
| [Simulator](../host/simulator.lisp) | Fixed traces executing the actual acceptance functions in ACL2 | No shadow semantics, network listener, or real disk adapter |

Run the integrated checks from the repository root with `make test`, or run
their components separately:

```sh
make check
make certify
python3 tools/run_simulator.py
python3 -m unittest discover -s tests -v
```

`make check` validates documents and registries. `make certify` invokes real ACL2
and certifies the explicitly listed books and executable assertion books. The
simulator emits traces and result records from those same logical functions.
These commands have different meanings; none is a substitute for the others.

The local reader experiment uses a persistent ACL2 process and listens only on
loopback. Its default mode serves a seeded in-memory article; it accepts no posts. Start it with
`python3 tools/run_reader.py --port 8119`. Port `0` selects an available port and
prints it. Use `--once` to exit after one connection. Reader socket tests start
and stop their own listeners. The optional `tests/interop_nntplib.py` probe uses
the independent standard-library NNTP client available in Python 3.9–3.12.

With `--store PATH`, it instead replays the local store into that same ACL2 process
and serves its validated NNTP projection. It holds a shared lock until exit, so
CLI writers are refused during that snapshot's lifetime. See the
[local walkthrough](local-experiment.md) for init/post/recover/inspect commands,
and the [store experiment](../specs/store-experiment.md) for publication and
durable allocation rules. `tests/store_capacity_probe.py` exercises the configured
128-record, 32-KiB-per-payload maximum without changing the retained data policy.

## Toolchain and evidence

The development toolchain is ACL2 8.7 on SBCL 2.6.8, installed on macOS using the
Homebrew `acl2` formula (8.7_6). Python 3.10 or later drives the tooling. Override
the ACL2 executable with `FN_ACL2`; the runner records the executable path/hash,
reported ACL2/Lisp versions, source/dependency hashes, drivers, certificates,
process results, and logs under `build/acl2/`. Missing ACL2 or failed proof events
fail the command. Custom ACL2 startup files are disabled for certification.

Books use ordinary ACL2 events, without proof-skipping, added axioms, or trust
tags. A certified book contains proved events and admitted definitions; it does
not imply that all its functions have verified guards or that its whole subsystem
contract has been established. Read theorem hypotheses as part of each claim.

## Deliberate limitations

- The acceptance model stores exact Message-ID strings and octet payloads. It
  does not yet validate RFC article syntax, sign native messages, or distinguish
  duplicate versus conflicting-ID rejection in its return value.
- The composed node ties each article to an independently charged archive pin.
  Retention release is tested separately and is not yet a node deletion API.
- CBOR's complete uint32/byte-string round trips and accepted-input re-encoding
  are certified. The composed transaction record also round-trips; portable
  native-message schemas and signature preimages remain open.
- Wire event-yield accounting and state preservation are certified; the base
  graphs and the derived index have guard evidence (planning/ledger.md has
  current counts). Implemented NNTP session/cursor preservation is certified;
  its effect typing is loose (a 2-list `(:reply octets)` shape, not a bounded
  reply-line grammar) and full RFC session refinement and other parser/physical
  resource bounds remain active.
- Limits in the byte primitives are experimental local bounds. They do not
  select a permanent interoperable format or deployment resource profile.
- Cryptographic verification, peer honesty, physical persistence, backup
  freshness, and eventual contact are environmental concerns with explicit
  assumptions, not conclusions of these small model proofs.
- There is no production deployment or flight qualification. The selected
  native-signature capability remains a requirement for the first usable release.

The [current work page](../planning/now.md) records the checkpoint and next work.
The [proof registry](../planning/proofs.json) keeps larger proof targets open
while component results accumulate. Requirement entries retain `specified`
where their complete contract is not implemented; `implementation_note` and
evidence fields identify the actual partial progress.


## Actual disconnected BP application path

The [BP exchange checkpoint](../tests/evidence/2026-09-18-bp-exchange.md) connects
actual fn sender and receiver journals through a pinned BPA. It covers outage,
process restart, explicit retry, lost application receipt, duplicate recognition,
identical receipt regeneration and durable sender acceptance of the BP return.
Both nodes retain one article/archive pin. That checkpoint's Python suite and a
scoped set of ACL2 roots cover receiver correction, outbound projection and
finite sender state/node/transport-receipt proofs (planning/ledger.md has
current counts). This is separate from the historical all-roots runs above.

A recorded BPA restart window leaves inventory without forwarding progress;
fn's durable retry handles this uncertainty. The subsequent
[composition assurance batch](../tests/evidence/2026-09-18-bp-composition-assurance.md)
adds joint pending/durable sender binding, fixed-Store receiver state/context/
receipt and journal-replay invariants, stable receipt bytes, and five actual
receiver process-death cuts; a scoped set of ACL2 roots and the Python suite
passed (planning/ledger.md has current counts). The BP ADU codec book has
verified guards; the other inventoried BP base books still need them.

General journal-byte/host refinement, composition with an evolving Store,
authentication, multi-relay/carried-media contact plans, LTP, fairness and
physical power-loss qualification remain open.
