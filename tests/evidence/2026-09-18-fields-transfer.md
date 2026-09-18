# Article fields, transfer staging, and storage proofs — 2026-09-18

`make test` passed on revision `ddeb657`: 38 ACL2 logical/assertion roots,
the actual acceptance simulator, and 32 Python tests (4 tooling, 10 reader,
18 store). The recorded source hashes were unchanged during the run.

The [machine-readable record](2026-09-18-fields-transfer.json) retains the exact
command, revision, source/certificate/driver digests, versions, results, and raw
log locations. The toolchain was ACL2 8.7 on SBCL 2.6.8, Python 3.14.7, macOS
26.6.1 arm64. The [previous batch](2026-09-18-wildmat-storage.md) retains the
independent stored-reader `nntplib` test; it was not repeated for these changes.
Socket regressions remain part of this combined run.

## Added behavior and evidence

| Area | Established scope |
| --- | --- |
| Article fields | RFC 5536 Message-ID/Newsgroups grammar over preserved syntax views; exact identity comparison; explicit missing/duplicate/invalid results; a narrow RFC 5537 proto-article routing subset |
| Field boundaries | Message-ID's 250-octet cap, no folding, required initial SP; bounded group parsing, duplicate/source preservation and forbidden Injection-Info/Xref vectors |
| Transfer staging | Full declared-byte reservation, separate metadata-slot and fragment-count limits, out-of-order chunks, exact duplicates, missing ranges, conservative overlap conflicts, and unverified complete candidates |
| Transfer regressions | Zero fragment budget refuses the first nonempty fragment; zero metadata budget refuses even empty objects; a one-slot budget admits one empty object, permits its exact replay and refuses a second label |
| File-model proofs | Transition/crash recognizer preservation, stable-record prefix preservation, exact surviving candidate with frontier dominance, and one-crash acknowledged-record retention |
| Real recovery fault | A transaction-file read error closes the mutation gate even on an already-live Store object; allocation stays refused until successful same-object recovery, retaining the actual article and pin |

The transfer assertion book includes byte/count exhaustion, gap/resume, duplicate,
overlap and Lisp-looking octet cases. Its small theorems establish valid initial
state and specified no-overwrite paths; executable examples do not establish
all transition preservation or assembly correctness.

The file theorem `fn-sf-prior-success-has-record-after-one-crash` applies to one
modeled crash from a valid state. It preserves a matching record for each prior
success under the model's crash choices. It is not an induction over arbitrary
reachable histories, a verification of the real adapter, or a power-loss test.

## Remaining boundaries

- Article-field checks are a routing/identity subset. Full mandatory headers,
  injection, generated identifiers/dates, native signatures, gateway provenance,
  and authority policy remain open.
- Transfer outputs are unverified candidates, never acceptance or retention
  receipts. There is no portable batch grammar, dependency closure, persistent
  fragment queue, selected cryptography, transport, or general work proof.
- File-model results leave live pending-node composition, fixed configuration,
  arbitrary traces, frame/namespace validation, and byte/POSIX refinement open.
  Stable media, barrier semantics, syscall association, and cooperative ownership
  remain explicit assumptions in the [refinement contract](../../specs/store-refinement.md).
- No full reader/POST service, authenticated native messaging, private groups,
  deployment, or flight qualification follows from this batch.
- The unfinished `records-canonicality` proof book was excluded from this frozen
  source set and its 38 default certification roots. Primitive canonicality and
  complete record value round trips retain their existing evidence.

PRF-007, PRF-011 and PRF-016 have additional component evidence. The larger
requirements, scenarios and milestones retain their open status.
