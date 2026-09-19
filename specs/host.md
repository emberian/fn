# Host and execution boundary

Status: ACL2 8.7/SBCL 2.6.8 development model and interpreted simulator are present.
An experimental subprocess/socket bridge runs the reader. A local file adapter
now executes the [persistence experiment](store-experiment.md) through the same
ACL2 node and record/replay definitions. The production Common Lisp packaging,
guard boundary, and platform qualification remain open.

## Core interface

Conceptual events include connection-opened, input-octets, connection-closed,
clock/contact observation, storage-completed, storage-indeterminate, and operator
request. Effects include output-octets, close-connection, persist-transaction,
schedule-work, and report-fault. M1 supplies exact constructors and guards.

HST-001: the host executes the same core definitions used for the proof claims,
or a separately justified refinement. It does not reimplement acceptance,
authorization, numbering, or GC in a different language. Guard verification and
boundary argument validation establish conditions for safe raw execution.

HST-002: events/results carry connection and transaction generations sufficient
to reject stale completions after restart, disconnect, or identifier reuse.
Scheduling serializes shared semantic transitions. Output may be partially written;
the host tracks offsets and never reruns a state transition to finish a write.
Quotas bound per-session staging and pending effects so one peer cannot monopolize
the state owner merely by refusing to consume output.

HST-003: platform persistence primitives have a documented contract tied to
A-DURABILITY and A-WRITE-ISOLATION. The host reports known failure and uncertain
completion distinctly. Recovery owns reconciliation after uncertainty; socket
disconnect does not establish storage rollback. Adapter/platform validation is
required in addition to ACL2 proofs.

HST-004: I/O, clocks, cryptographic primitives, and authentication are explicit
trust-boundary entries. The production integration must not contaminate book
certification with arbitrary raw-mode changes or hide trusted code inside a
claimed proved function. Certify the pure core in a clean environment.

## Durability barriers by platform

Every barrier the specifications call a durability barrier — staged file data,
final directory namespace, configuration, allocation frontier, journal record
and inbound frame — goes through one helper, `run_store.durable_barrier`, which
`workflow_journal` and `receipt_journal` import rather than reimplement.

| Platform | Primitive | What it establishes |
| --- | --- | --- |
| darwin | `fcntl(fd, F_FULLFSYNC)` | The device is asked to flush its own write cache. `fsync(2)` alone on APFS returns once data reaches the drive, which does not order it against a power cut. |
| darwin, filesystem rejecting `F_FULLFSYNC` | `fsync(2)` after `ENOTSUP`/`ENOTTY`/`EINVAL`/`EOPNOTSUPP`/`EPERM` | Only the `fsync(2)` contract of that filesystem. The stronger claim is not available there. Any other errno is reported, never downgraded. |
| other platforms | `fsync(2)` | The filesystem's own `fsync(2)` contract. |

This selects the strongest primitive each platform offers. It is not a
power-loss qualification: A-DURABILITY and A-WRITE-ISOLATION remain assumptions
about the device and filesystem, and no test here observes an actual power cut.
The barrier is measurably more expensive than `fsync(2)` — about 5.5 ms versus
0.04 ms per call on this development machine's APFS volume — which is the cost
of asking for the flush rather than assuming it.

## CLI exit codes

Uncertain, refused and accepted stay distinct all the way out (HST-003). Every
CLI in `tools/` maps one host outcome to one code through
`run_store.exit_code_for`:

| Code | Meaning | Source |
| --- | --- | --- |
| 0 | Accepted, or the query answered. A durable acceptance whose BPA delete has not completed also exits 0 and names the pending obligation on stdout (`bpa-delete=pending`). | normal return |
| 1 | Refused: a known, clean refusal that changed no durable state. A duplicate Message-ID conflict, a contended store lock, a configured bound reached, an absent article on `inspect`. | `StoreError` |
| 3 | Uncertain: the outcome of a publication is unknown and recovery is required before further mutation. | `StoreIndeterminate` |
| 4 | Fault: invalid durable state or an I/O fault. Corrupt or ungapped committed history, a store whose core cannot replay it, a barrier or descriptor failure, a poisoned ACL2 bridge. | `StoreFault`, `OSError` |
| 5 | Usage: the invocation itself is wrong. | `UsageParser`, `UnicodeError` on arguments |

A reader whose ACL2 bridge is poisoned exits 4 rather than answering the next
client from a pipe whose replies can no longer be matched to its commands.

## ACL2 bridge correlation

The bridge is a pipe to one interpreted ACL2 process. Every call first writes
`(cw "FN_CALL_<nonce>~%")` with a fresh `os.urandom` nonce and reads that
marker to its own prompt; only then is the real form written and its reply
read. A reply is accepted only when this call's marker preceded it, so a lost,
late or duplicated reply cannot be returned as the next call's result.

A correlation failure, a reply timeout, an output-bound trip or a broken pipe
poisons the bridge: every later call raises `StoreError("ACL2 bridge
poisoned")` and the only recovery is a new bridge, which is a new ACL2 process.
A correlated reply that reports an ACL2 error is an answer, not a loss; it
leaves the pipe synchronized.

Reply bounds are proportional, not fixed. An ordinary call allows
`ACL2_CALL_BASE_SECONDS` (20 s, covering process scheduling and book-resident
work) plus `ACL2_CALL_PER_KIB_SECONDS` (0.004 s, about 4 s/MiB) times the form
size, because external bytes cross as decimal-octet literals whose marshaling
dominates. Recovery allows `ACL2_RECOVER_BASE_SECONDS` (30 s) plus
`ACL2_RECOVER_PER_RECORD_SECONDS` (1 s) per recovered record, or the size-based
bound, whichever is larger. The recorded maximum-profile reopen on this machine
is 11.7 s for 128 records, so the bound is about 158 s: an order of magnitude
above measurement, instead of a fixed 20 s that sat within 2x of it.

## Scope of the first adapter

Prefer one host process, one owner of core state, bounded I/O staging, and local
configuration. A test host first interprets effects against simulated disk and
network models. The real host follows after its event contract and error behavior
are executable. The BP adapter and durable workflow journal are active work
alongside the local service. Web/9p interfaces can follow using the same contracts.

Exact packaging is open: use certified ACL2 definitions in a supported host image
with controlled integration, and document any raw Lisp boundary. A hand-maintained
shadow implementation is not the intended path to a smaller binary.
