# First integrated executable batch — 2026-09-18

Result: `make test` passed. It ran document/registry checks, certified 19 ACL2
logical and assertion books, executed the acceptance simulator, and passed nine
Python tooling/socket tests. A separately launched reader passed the independent
Python 3.9.6 standard-library `nntplib` probe.

The [machine-readable record](2026-09-18-integrated.json) preserves tool versions,
invocations, exact source/dependency hashes, certificate hashes, outcome records,
and original log locations. ACL2 reported version 8.7, hosted by SBCL 2.6.8 on
macOS. The root compared all recorded logical source hashes with the working
files before writing this record. No generated certificate is treated as a
substitute for its corresponding source and actual successful certification run.

## What this establishes

| Area | Actual evidence |
| --- | --- |
| Acceptance | Initial validity; general prepare/complete/recover state preservation; exact preservation of existing article bindings; fresh local numbers; atomic cross-post, retry, stale event, abort, and uncertainty traces |
| Node composition | General prepare/complete/recover state preservation; committed article-to-archive-pin relation and old bindings preserved; refusal and staged publication scenarios; mismatched and orphaned metadata rejected |
| Retention | Admission preserves the ledger; no wrong-evidence release; independently charged archive/forward pins; repeated release retains history cost and eventually exhausts capacity |
| Wire | Dot transformation inverse; one-byte state preservation with explicit buffer bounds; proper-input fixed-mode partition composition; event-yield tests at coalesced POST/article boundaries; closure discards rejected tails |
| CBOR | All uint32 encode/decode round trips; big-endian reconstruction and octet/bound helpers; accepted/rejected uint and byte-string vectors |
| Journal | Executable isolated-slot/barrier/crash experiments; dependency/gap/damage fault lemmas; four surviving/lost subsets for two uncommitted object writes; acceptance txid skips distinct from contiguous journal sequences; uncertain abort after a marker requires recovery |
| Exchange | Fact membership merge/idempotence/order lemmas; four-node overlapping, duplicate, reordered, carried-batch scenarios; refusal and conflict preservation |
| NNTP | Exact expected reader transcripts, case-sensitive Message-ID lookup, decimal boundary regressions, projection-injection rejection, truthful limited capabilities; socket fragmentation/coalescing, isolation, malformed input, QUIT, RST survival |
| Host | Persistent ACL2 process runs the actual core; bounded numeric octet marshalling; fixed bridge calls; failure closes the affected connection; no Python implementation of protocol or acceptance semantics |

The independent client exercised CAPABILITIES, GROUP, STAT, HEAD, BODY, ARTICLE,
LIST, and QUIT against the actual loopback listener. It is a client compatibility
experiment for this subset, not a complete RFC audit or a full newsreader UI test.

## Remaining boundaries

- These are one-step logical invariants. Whole-system trace induction, verified
  guards, efficient concrete representations, and all subsystem properties are
  separate targets. No complete broad proof target is closed by this batch.
- The composed node does not yet execute the journal. Its durable completion
  and recovery observations remain trusted abstract events. Node release is not
  implemented; the separate retention ledger's general release preservation
  proof remains open.
- Journal integrity tags abstract a future frame check. Barriers, isolated writes,
  and a separately protected durable acknowledgement anchor are assumptions.
  There is no real disk adapter, checkpoint/compaction implementation, or general
  theorem that every acknowledged history survives every allowed crash.
- The crash constructor selects surviving/torn volatile slots and puts surviving
  volatile writes in reverse order. The four-case experiment enumerates subsets,
  not all physical reorderings, write-unit failures, or power-loss behavior.
- CBOR byte-string full round-trip and accepted-encoding uniqueness remain open.
  No portable article/signature/batch or persistent frame schema is frozen.
- Wire retained-state bounds do not establish linear runtime or the complete
  session-sensitive protocol theorem. The reader supports only a laboratory
  subset, with no READER bundle, POST, authentication, or durable ingestion.
- Exchange validation and release evidence are supplied policy/authentication
  observations. No cryptography, actual peer retention, resumable bytes,
  persistent transfer queue, or eventual delivery is proved. Finite-capacity
  arrival order only commutes under the stated combined-admission hypotheses.
- The host's program-mode adapter helpers, Python transport, ACL2/SBCL, and the
  installed `ihs/quotient-remainder-lemmas` system book remain in the stated trust
  boundary. The local source audit rejects named proof/trust facilities; it is
  a conservative lexical check plus human review, not macro-expansion analysis.

## Review repairs included

The two batched Sol/Astra reviews and integration checks resulted in fixes for
improper record tails, fenced completion handling, uncharged release history,
framing work after closure, command/article yield boundaries, weak wire bounds,
reversed decimal article numbers, unsafe NNTP field interpolation, optional
CAPABILITIES arguments, journal sequence/transaction conflation, and unsafe
known-abort classification after a marker. Node invariants also reject missing
stages, duplicate binding keys, and orphan bindings. Regression assertions cover
the repaired cases; open proof scope was kept open rather than hidden by review.

To reproduce the main batch, install the documented toolchain and run `make test`.
For the independent client, start `python3 tools/run_reader.py --port 0 --once`,
then run `python3.9 tests/interop_nntplib.py PORT` using the printed port (Python
3.9–3.12 with `nntplib` is suitable). The original run used `/usr/bin/python3`.
