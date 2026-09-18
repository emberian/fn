# Executable development status

fn has executable ACL2 components and a deterministic simulator. It is still an
experimental implementation: the components are not yet a durable, authenticated
news service. The broader contracts in `specs/` remain the target.

The latest [reader/storage evidence](../tests/evidence/2026-09-18-wildmat-storage.md)
records 33 certified logical/assertion books, the actual-core simulator, 31
passing tooling/socket/filesystem tests, and independent stored-reader `nntplib`
interoperability including LISTGROUP and filtered LIST variants. The earlier
[storage batch](../tests/evidence/2026-09-18-storage.md) retains the maximum-profile
store/reopen probe; the [first batch](../tests/evidence/2026-09-18-integrated.md)
is also preserved separately.

## Current components

| Component | Executable scope | Remaining boundary |
| --- | --- | --- |
| [Acceptance](../books/acceptance.lisp) | Atomic local allocation, immutable Message-ID binding, staged publication, stale completion rejection, uncertainty fencing | Durable completion and recovery observations are abstract inputs; no physical disk is involved |
| [Acceptance invariants](../books/acceptance-invariants.lisp) | Mechanically checked preservation lemmas over the acceptance definitions | See the proof registry and certification evidence for the exact current theorem scope |
| [Wire framing](../books/wire.lisp) | Incremental CRLF lines, dot stuffing, article terminators, bounded retained input | Session dispatch and command conformance are separate; the bulk feed helper alone cannot decide when to enter article mode |
| [Wildmat](../books/wildmat.lisp) | Bounded strict UTF-8 grammar and dynamic-programming matching, reused for filtered LIST variants | General decoder/matcher correspondence and complexity proofs remain open |
| [CBOR primitives](../books/cbor.lisp) | Deterministic uint32 and definite byte strings, canonicality checks, bounded decoding | No native object, signature, batch, or disk schema is frozen |
| [Article syntax](../books/article.lisp) and [invariants](../books/article-invariants.lisp) | Bounded header/body views preserve folding, unknown fields, and opaque body bytes; every successful parse provably reconstructs its exact source | Required-field semantics, full RFC validation, injection, output recognizer, and work/allocation proofs remain open |
| [Article fields](../books/article-fields.lisp) | Bounded RFC Message-ID and Newsgroups semantics, duplicate/missing/invalid classification, narrow proto-article routing checks over preserved views | Full required-field validation, injection, gateway provenance, authorization, and native signing remain open |
| [Transaction records](../books/records.lisp) and [invariants](../books/records-invariants.lisp) | Bounded schema-0 grammar, exact octet/string fields, variable group lists, complete record round-trip proof | Provisional local format; record-level reverse canonicality and native signature preimages remain open |
| [Retention](../books/retention.lisp) and [invariants](../books/retention-invariants.lisp) | Finite abstract accounting, distinct archive/forward pins, evidence-gated release, permanent duplicate history; general release preservation and independent-pin/identity preservation | Evidence is already authorized input; charging units are abstract, not measured physical bytes |
| [Node composition](../books/node.lisp) and [invariants](../books/node-invariants.lisp) | One transaction stages acceptance and its reservation; completion publishes both with permanent article-to-pin bindings; general transition preservation proved | Disk completion is still abstract; node release and journal integration remain open |
| [Replay](../books/replay.lisp) and [invariants](../books/replay-invariants.lisp) | Contiguous committed records rebuild the actual node, obligations, and allocations; counter advance preserves invariants; replay has typed success/fault results from valid configurations | A last-good prefix on fault is diagnostic only; no checkpoint, rollback detection, or disk refinement claim |
| [Local store](../tools/run_store.py) | Immutable framed transaction files, data/directory barriers, locking, exact ACL2 replay, injected I/O failures | Development experiment; no qualified power-loss profile, independent freshness anchor, or byte-accurate physical reservations |
| [File-publication kernel](../books/store-files.lisp) and [invariants](../books/store-files-invariants.lisp) | One-use allocator reservations, immutable publication, actual replay and recovery gates; transition/crash preservation, stable-prefix and one-crash success retention proved | Arbitrary traces, live pending-node composition, and actual adapter refinement remain open |
| [Journal](../books/journal.lisp) | Isolated record slots, barriers, surviving/torn volatile writes, explicit recovery faults | Integrity tags and a protected durable anchor are assumptions; no byte format, actual disk adapter, or general recovery theorem |
| [Exchange](../books/exchange.lisp) | Bounded atomic admission of immutable fact sets; duplicate/reordered merging and conflict evidence | Authorization is supplied; no serialized/resumable transfer, signatures, or durable scheduler |
| [Object assembly](../books/transfer.lisp) | Declared-byte and metadata reservations, out-of-order fragments, exact duplicates, missing ranges, and unverified complete candidates | No wire grammar, complete-object validation, durable progress, receipt, or general transition/work proof |
| [NNTP reader](../books/nntp.lisp) | Experimental reader commands including LISTGROUP ranges/cursors and filtered LIST ACTIVE/NEWSGROUPS over committed state, with independent response transcripts | Incomplete READER bundle, no POST, authentication, or signed injection |
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
- Wire state bounds and one-byte preservation are certified; parser complexity,
  complete session refinement, and raw-execution guards remain open.
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
