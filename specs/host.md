# Host and execution boundary

Status: ACL2 8.7/SBCL 2.6.8 development model and interpreted simulator are present.
An experimental subprocess/socket bridge runs the reader. A local file adapter
now executes the [persistence experiment](store-experiment.md) through the same
ACL2 node and record/replay definitions. The production Common Lisp packaging,
guard boundary, and platform qualification remain open.

## Selected production runtime

D07 requires a native Lisp node and operator CLI, executing the ACL2 core
directly in the supported host image. The deployed service, launchers, recovery,
NNTP posting/peering, BP workflows, live configuration, control and selected
identity/anchor operations must not require a Python interpreter, module or
helper subprocess. Python remains permitted in build, certification, test,
benchmark and differential-oracle tooling outside the deployed node.

This is a requirement, not the current implementation: `bin/fn` and the service
unit still start the Python owner. Native store, reader and BP components do not
yet establish complete service parity. `FN_HOST=native` through a Python argument
parser is a test convenience, not a conforming production entry point.

HST-001 includes this runtime boundary. The replacement host must call the same
ACL2 semantic subjects or a named justified refinement; translating Python's
decisions into raw Lisp does not meet it. Configuration defaults, bounds, framing,
identity derivation and persistence decisions retain one ACL2 owner. External
configuration/control data use bounded parsers, never the Lisp reader/evaluator.
HST-002 through HST-005 still apply to the native owner, including uncertainty
fencing, generation checks, concurrent sessions and fault isolation.

The v0 runtime gate must exercise the installed CLI and two native services in
an environment without Python, including restart/recovery and all selected
features. Record image/source/dependency identities and child-process execution;
a restricted PATH alone cannot exclude an absolute Python helper. An external
Python harness may drive the gate but is not part of either node. Missing native
features remain open rather than falling back to the Python service. Existing
Python integration results remain scoped historical evidence.

Raw Lisp I/O, FFI, TLS/crypto libraries, runtime/compiler and filesystem/hardware
assumptions remain explicit trust boundaries. A Python-free process is a
deployment property, not a theorem of functional correctness or durability.

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

HST-005: a fault in the host costs the connection that caused it and nothing
else. An unexpected exception while serving one connection must not end the
process, because a news server faces untrusted peers and one peer's input
would then be a denial of service against every other. The host decides only
whether it still trusts that socket; the reply, the scope and everything the
state owner forgets are the core's one fault transition, which closes the
connection, clears the submission it had in flight and the transaction it
held, and leaves every other connection equal to what it was. The reply is a
FOURTH outcome, distinct on the wire from accepted, refused and uncertain, so
a fault is never read as a verdict on an article. A fault the host cannot
attribute to a connection or a peer abandons nothing, so it is counted and
bounded; and a lost core image is not a fault the host survives, because the
core is where every decision is made.

HST-004: I/O, clocks, cryptographic primitives, and authentication are explicit
trust-boundary entries. The production integration must not contaminate book
certification with arbitrary raw-mode changes or hide trusted code inside a
claimed proved function. Certify the pure core in a clean environment.

## Durability barriers by platform

Native file and directory barriers use `fnn-durable-barrier` in
`host/native/io.lisp`. The development Python adapter uses
`run_store.durable_barrier`, imported by its workflow and receipt journals.
These are platform adapters to the same stated contract; their agreement is
an adapter obligation, not a theorem about the operating system. Publication
ordering and uncertain outcomes belong to the ACL2 storage/journal machines.

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

Uncertain, refused and accepted stay distinct all the way out (HST-003). The
store and BP-ingress CLIs map one host outcome to one code through
`run_store.exit_code_for`; the reader returns the same codes directly.
`tools/run_simulator.py` and `tools/certify_books.py` are evidence runners with
their own conventions and are outside this table.

| Code | Meaning | Source |
| --- | --- | --- |
| 0 | Accepted, or the query answered. A durable acceptance whose BPA delete has not completed also exits 0 and names the pending obligation on stdout (`bpa-delete=pending`). | normal return |
| 1 | Refused: known nonacceptance of this request, such as a Message-ID conflict, contended lock, configured bound, or absent article on `inspect`. A refusal after reservation may consume a durable allocator number; it does not imply byte-for-byte unchanged storage. | `StoreError`, native `fnn-store-error` |
| 3 | Uncertain: the outcome of a publication is unknown and recovery is required before further mutation. | `StoreIndeterminate` |
| 4 | Fault: invalid durable state or an I/O fault. Corrupt or ungapped committed history, a store whose core cannot replay it, a barrier or descriptor failure, a poisoned ACL2 bridge. | `StoreFault`, `OSError` |
| 5 | Usage: the invocation itself is wrong. | `UsageParser`, `UnicodeError` on arguments |

A reader whose ACL2 bridge is poisoned exits 4 rather than answering the next
client from a pipe whose replies can no longer be matched to its commands.
Native conditions use the same outcome distinctions through `fnn-exit-code-for`;
the operator plan's code projection is ACL2-owned. Successful queries and an
article accepted with a retention obligation both use code 0, so callers must
also interpret the named operation and its result.

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

## The native host

`build/fn-host` is one saved SBCL image: ACL2 8.7, the certified books the
hosts drive, the `:program` wrappers in `host/*-host.lisp`, and the raw-Lisp
adapter `host/native/io.lisp`. `tools/build_native_host.sh` feeds
`host/native/build.lisp` to a certified ACL2 and refuses the image on any
error marker, any uncertified-book warning, or a missing ready marker; the
books it `include-book`s are Makefile certification roots, so the image holds
the certified definitions and nothing reinterpreted. `tools/fn_native.py`
launches it with the Python hosts' command-line surface, and `FN_HOST=native`
makes `tools/run_store.py` and `tools/run_reader.py` delegate to it after
parsing, so the same tests drive either host.

The Python launchers above are development conveniences. The Python-free
component launcher is `packaging/fn-native`; its current operator commands and
unsupported profiles are documented in [the operator guide](../docs/operator.md).
It does not yet satisfy the full two-node production gate.

The decimal-octet pipe, its nonce correlation and its reply bounds do not
exist in this host: every call is an in-process application of the wrapper's
executable counterpart (`fnn-call`, the raw-Lisp spelling of `ec-call`), under
the image's `guard-checking-on`, which the entry asserts is `t`, the same
policy the interpreted bridge evaluates under. A `:program` wrapper therefore
runs raw beneath its counterpart in both hosts; the complete call-graph guard
requirement of packet C3-05 is unchanged by the packaging.

### The served reader path

One socket read is one `fn-served-step` (books/served.lisp): a fold of
`fn-wire-feed-byte` with `fn-nntp-post-step` on each framed event, with the
reply concatenation, over a five-field connection that carries the posting
configuration and the clock observation pinned at `fn-served-open`. The host
hands the whole chunk over and takes back reply octets, a closing flag and
whatever submission the step produced; it re-feeds nothing, frames nothing
and holds no wire state, so `fn-wire-drive` has one owner and it is the book.
A submission is completed as refused while the reader holds only a shared
lock, and ACL2 -- never the host -- writes the 240 or the 441.

### The owner submission path

Served POST, inbound transit and a running owner's control `POST` all enter
the same serialized owner submission slot. The control boundary is one ACL2
event over the Message-ID, groups and exact authored article octets; it does
not allocate an NNTP connection or synthesize a loopback protocol session.
`fn-owner-take` then exposes the same in-flight submission shape used by the
served path, and `fn-owner-control-outcome` consumes the same owner completion
predicate that gates a served 240.

Before the store transaction, `fn-owner-submission-intent` projects the ACL2
chosen feed targets, object obligation identity, provenance, configuration
generation, transaction id and tick into one FNFD intent per target. All
intent frames reach their durable per-peer journals before the host calls
`durable_post`. After a known result,
`fn-owner-submission-resolution` repeats those exact values in a commit or
abort frame; the resolution is durable before the owner enqueues a committed
article or reports the outcome. An indeterminate store result writes no
resolution, reports uncertain distinctly, and stops the current owner after
that reply so recovery precedes every later mutation.

Startup scans and repairs every configured or retained peer journal after the
store's authoritative recovery. ACL2 folds unresolved intents and compares
each with the recovered article binding and retention evidence. The host only
appends the commit/abort frame ACL2 returns. Any incomplete or contradictory
recovery evidence is uncertain and fences the whole owner image.

The store path opens on the replayed configuration history: `config/*.cfg`,
oldest first, to `fn-store-sn-recover` with the article records and the
frontier. A store with no configuration record is refused, and the served
group names, their codes and the generation come back from the core
(`fn-store-cfg-served/-domain/-generation`); the image holds no compiled
group table and `init` asks `fn-cfg-host-initial-octets` for generation 1.

### Trust boundary of the native host

Everything below is asserted, not proved. The raw surface is exactly
`host/native/io.lisp`, loaded under the trust tag `:fn-native-host`, which is
retired (`(defttag nil)`) before the image is saved; `fn-native-entry` is the
one ACL2-visible symbol whose raw definition that file replaces.

| Surface | Functions | What it does |
| --- | --- | --- |
| SBCL runtime | `sb-ext:exit`, `sb-sys:enable-interrupt` (SIGTERM exits 143), `sb-sys:make-fd-stream` on descriptors 1 and 2, `sb-ext:*posix-argv*` after `--fn` | Process entry, exit and standard streams; `--disable-debugger` in the saved script so an escaped condition exits rather than waits on a terminal |
| Files (sb-posix, sb-unix) | `fnn-open`, `fnn-close`, `fnn-fstat`, `fnn-lstat`, `fnn-check-regular`, `fnn-read-fd`, `fnn-read-regular-bounded`, `fnn-write-all`, `fnn-list-directory`, `fnn-link`, `fnn-replace`, `fnn-unlink`, `fnn-mkdir`, `fnn-safe-directory` | The same `O_NOFOLLOW` opens, `fstat` regularity checks, bounded reads, `O_EXCL` staging, `link`/`rename` publication and directory grammar as `tools/run_store.py` |
| Barriers | `fnn-durable-barrier`, `fnn-fsync-file`, `fnn-fsync-dir`, `fnn-fsync-regular` | The platform table above: `fcntl(fd, 51)` (`F_FULLFSYNC`, which sb-posix does not name) on darwin, `fsync(2)` after `ENOTTY`/`ENOTSUP`/`EOPNOTSUPP`/`EINVAL`/`EPERM`, `fsync(2)` elsewhere; the five recovery barriers, the staged-file and directory barriers are real calls |
| Locks | `fnn-flock` (alien `flock(2)`), `fnn-open-lock` | `LOCK_EX`/`LOCK_SH` with `LOCK_NB`, the same refusal and fault classes |
| Cryptography | `fnn-trailer` calls `fn-frame-trailer`; `fnn-sha256` remains only behind the diagnostic `sha256` verb | Store and metadata trailers are computed by `books/sha256.lisp` through `books/crypto-attach.lisp`, as they are in the Python bridge. `python3 tools/fn_native.py sha256-selftest` still compares the separate diagnostic raw-Lisp SHA-256 with `hashlib`; that result is not used to frame durable data. |
| Store metadata | `fnn-metadata-config-frame/-decode`, `fnn-metadata-frontier-frame/-decode/-next`, `fnn-transaction-name`, `fnn-load-config`, `fnn-load-frontier` | `config.json` and `allocation-frontier.json` contain the same ACL2-sealed `FNSM` frames that the Python adapter uses. `books/byte-store-frame.lisp` owns profile values, framing, parsing, integrity and the frontier successor; `books/byte-store-txn-name.lisp` owns the published transaction name. The native host moves octets and retains format-5 JSON in place while refusing normal open pending offline migration. |
| Core calls | `fnn-call`, `fnn-core`, `fnn-core-state`, `fnn-global` | Counterparts of `fn-store-sn-reset/-recover/-io/-prepare/-existing-action/-pending-octets/-known-abort/-refuse-reservation/-finish/-article-count/-next-txid/-group-next/-pin-count/-reserved/-lookup/-lookup-foundp`, `fn-store-record-sequence/-txid`, `fn-store-frame-constants/-store-protected/-store-decode`, `fn-store-metadata-config-frame/-decode`, `fn-store-metadata-frontier-frame/-decode/-next`, `fn-store-txn-name`, `fn-store-subject-id`, `fn-store-obligation-preimage/-id`, `fn-store-post-boundary`, `fn-store-charge`, `fn-store-group-codes` (names against the replayed domain), `fn-store-cfg-generation/-served/-domain`, `fn-cfg-host-initial-octets`, `fn-reader-use-seed/-use-store/-set-posting/-reset/-chunk/-outcome`, `fn-reader-model-octets`; the globals `fn-reader-output`, `fn-reader-closep`, `fn-reader-submit-octets/-msgid`, `guard-checking-on`. A `raw-ev-fncall` throw, Lisp error, core error flag or malformed result is a fault; a returned semantic refusal remains a refusal |
| Sockets | `fnn-listen` (`sb-bsd-sockets` `inet-socket`/`inet6-socket`, loopback unless an address is passed), `fnn-connect`, `fnn-accept-loop`, `fnn-socket-fd`, `fnn-socket-shut`; `fnn-recv`, `fnn-send-all` (`sb-sys:wait-until-fd-usable` with absolute deadlines over nonblocking read/write retries; DNS/connect remain outside this contract), `fnn-graceful-close` (alien `shutdown(fd, SHUT_WR)` then a one-second drain), `fnn-serve-client` | `tools/run_reader.py`'s loop: 512-octet reads, **one `fn-served-step` per read** and no retained suffix, the reply octets from `fn-served-reply-octets`, close after a framing rejection. These eight are the whole socket surface, and the surface `host/native/tcpcl.lisp` is to build on (planning/lanes/HANDOFF-w4-tcpcl.md) |
| Entry | `fnn-main`, `fnn-dispatch`, `fn-native-entry` | The fixed positional protocol behind `--fn`, the outcome-to-exit-code map (reader setup and escaped core conditions retain refusal 1, uncertainty 3 and fault 4) |

The native anchor follow-on is loaded by the common saved-image build:

| Surface | Functions | What it does |
| --- | --- | --- |
| Roughtime primitives | `fnn-crypto-startup`, `fnn-crypto-ed25519-observe`, `fnn-crypto-anchor-leaf` in `host/native/crypto.lisp` | Reinitializes libsodium after every saved-image restart; returns primitive observations only over ACL2-produced subjects |
| Roughtime acquisition | `fnn-anchor-csprng-nonce`, `fnn-anchor-udp-exchange`, `fnn-anchor-acquire` in `host/native/anchor.lisp` | Consumes ACL2's selected server/key/wire-bound profile, reads the nonce from `/dev/urandom`, sends ACL2's request in one connected IPv4 UDP datagram, probes one byte beyond ACL2's response bound, calls the ACL2 parser and crypto seam, and preserves observed/refused/uncertain/fault |
| Anchor decision and FNAN | `fnn-command-anchor`, `fnn-anchor-decision`, `fnn-anchor-publish`, `fnn-anchor-recovery-barriers` | Holds the store writer lock, calls the actual ACL2 acceptance entry, drives ACL2 `fn-anchor-rp-step` through pre-syscall issue and every result, reports accepted only after the directory barrier, and barriers a recovered final file and directory before decode |

`books/anchor-servers.lisp` owns the bounded name-to-endpoint/key mapping and
the acquisition sizes.  The common image loads `host/native/crypto.lisp`
before `host/native/anchor.lisp`; `anchor acquire` calls
`fnn-crypto-startup` in the restarted image before network use.  DNS has no
whole-path deadline; send and receive readiness each get the selected timeout.
Exit 0 follows only durable FNAN replacement, refusal is 1, uncertainty is 3,
and host/core fault is 4.

Remaining Python-only: the BP hosts (`run_bp_ingress.py`, `run_bp_receive.py`,
`workflow_journal.py`, `receipt_journal.py`), the in-process `Acl2Store`,
`Store` and `Acl2Reader` classes that the fault-matrix, process-crash and
partition tests drive through `mock.patch`, and the reader's
`ReaderBridgeFault` path, which has no in-process analogue: a Lisp condition
that escapes a core call while serving is reported and exits 4.

The native I/O repair at `3312778` shares EINTR/progress handling across file
and socket calls, preserves partial offsets and EOF, and rejects zero write
progress. `tests/native_io_progress.lisp`, run by
`sh tests/test_native_io_progress.sh`, injects POSIX observations into the same
raw functions and exercises reader condition propagation. Its error assertions
check the requested condition type; a wrong-type witness checks the test helper.
These are deterministic host tests, not ACL2 proofs or physical I/O qualification.
The follow-on socket packet `28c5b90` sets `O_NONBLOCK` at `fnn-socket-fd`
and returns EAGAIN/EWOULDBLOCK races to the same absolute-deadline readiness
loop. Real socketpair EOF/backpressure tests accompany deterministic EINTR,
partial-write and zero-time-poll tests. DNS and connection establishment remain
outside this read/write deadline contract; this is not real-time OS qualification.

The [native guard review and disposition](../planning/evidence/claude-native-store-guard-response.md)
distinguish verified callee guards from unverified program-mode host wrappers.
Selecting an executable counterpart does not discharge all caller preconditions
or prove that every inner guard runs. The adapter's maintained-state and boundary
correspondence remains explicit; no new validation/proof claim follows from its
startup check of `guard-checking-on`.

### Differential evidence and measurements

`python3 -m unittest tests.test_native_served_differential` feeds one chunk
list through the image twice -- `--fn model` (one `fn-served-open` then one
`fn-served-run`, projected with `fn-served-reply-octets`) and `--fn reader`
(the production listener) -- and requires identical bytes, for a whole
transcript, three cut points, a bytewise partition, a cut inside a UTF-8
sequence, input after QUIT and a framing rejection. It is the native mirror
of `tests/test_served_differential.py`, and it is what says the thing on the
socket is the certified fold and nothing else. Recorded run (persvati,
2026-09-20, image built by `FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 sh
tools/build_native_host.sh` against the `dev-bdd59d2` gate certificates:
`built build/fn-host (250M core)`, 8.5 s wall): 7 tests, OK, 0.38 s. The
image is what found the two defects that no static check could: the SBCL
banner on stdout (`--noinform` belongs in `save-exec`'s `:host-lisp-args`,
not its `:toplevel-args`) and a record metadata field taking identity text
(`fn-store-identity-text`) over v1 subject preimages, not v0 canonical
octets.

`python3 tests/native_differential.py` runs one scripted store sequence
through both hosts and compares, after every command, the exit code, standard
output and every byte under the store (staging names, which carry a pid and
random octets, are compared by content), then twelve identically damaged
copies, then four reader transcripts octet for octet. Recorded run:
FN_DIFF_RESULT. The four test files `tests/test_store.py`,
`tests/test_store_corruption.py`, `tests/test_reader.py` and
`tests/test_reader_partitions.py` under `FN_HOST=native`: FN_TEST_RESULT.

Reopen of the 128-record maximum profile (32768-octet payloads, both groups),
same machine, load average FN_LOAD at the time:

| Host | Commit 128 records | Reopen (recover, replay, five barriers) | Scope |
| --- | --- | --- | --- |
| Python (`tests/store_capacity_probe.py`) | FN_PY_COMMIT s | FN_PY_REOPEN s | the reopen includes starting a fresh ACL2 process and loading the books, then marshaling about 34 MiB of decimal octets |
| native (`fn-host --fn store DIR probe 128`) | FN_NA_COMMIT s | FN_NA_REOPEN s | in-process; image start (`status` on an empty store end to end) is FN_NA_START s |

## Scope of the first adapter

Prefer one host process, one owner of core state, bounded I/O staging, and local
configuration. A test host first interprets effects against simulated disk and
network models. The real host follows after its event contract and error behavior
are executable. The BP adapter and durable workflow journal are active work
alongside the local service. Web/9p interfaces can follow using the same contracts.

Exact packaging is open: use certified ACL2 definitions in a supported host image
with controlled integration, and document any raw Lisp boundary. A hand-maintained
shadow implementation is not the intended path to a smaller binary.
