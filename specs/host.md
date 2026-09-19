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

Uncertain, refused and accepted stay distinct all the way out (HST-003). The
store and BP-ingress CLIs map one host outcome to one code through
`run_store.exit_code_for`; the reader returns the same codes directly.
`tools/run_simulator.py` and `tools/certify_books.py` are evidence runners with
their own conventions and are outside this table.

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

The decimal-octet pipe, its nonce correlation and its reply bounds do not
exist in this host: every call is an in-process application of the wrapper's
executable counterpart (`fnn-call`, the raw-Lisp spelling of `ec-call`), under
the image's `guard-checking-on`, which the entry asserts is `t`, the same
policy the interpreted bridge evaluates under. A `:program` wrapper therefore
runs raw beneath its counterpart in both hosts; the complete call-graph guard
requirement of packet C3-05 is unchanged by the packaging.

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
| Cryptography | `fnn-sha256` (A-CRYPTO) | SHA-256 in Lisp; `python3 tools/fn_native.py sha256-selftest` compares it with `hashlib` on the FIPS vectors and random lengths across the padding boundaries. Digest octets go to the constrained `fn-frame-digest` consumers exactly as Python's do |
| Metadata JSON | `fnn-json-parse`, `fnn-json-canonical`, `fnn-with-checksum`, `fnn-frontier-with-checksum`, `fnn-load-config`, `fnn-load-frontier` | `config.json` and `allocation-frontier.json`: a bounded hand parser (never the Lisp reader) and Python's `json.dumps(sort_keys=True, separators=(",", ":"))`. This is a host decision with two host implementations; the differential run is what keeps them equal (see open items) |
| Core calls | `fnn-call`, `fnn-core`, `fnn-core-state`, `fnn-global` | Counterparts of `fn-store-sn-reset/-recover/-io/-prepare/-existing-action/-pending-octets/-known-abort/-refuse-reservation/-finish/-article-count/-next-txid/-group-next/-pin-count/-reserved/-lookup/-lookup-foundp`, `fn-store-record-sequence/-txid`, `fn-store-frame-constants/-store-protected/-store-decode`, `fn-store-subject-id`, `fn-store-obligation-preimage/-id`, `fn-store-post-boundary`, `fn-store-charge`, `fn-store-group-table-id/-codes`, `fn-reader-use-seed/-use-store/-reset/-chunk`; the globals `fn-reader-output`, `fn-reader-closep`, `fn-reader-suffix`, `guard-checking-on`. A `raw-ev-fncall` throw or Lisp error inside a call is a refusal, as an `ACL2 Error` reply is for the pipe |
| Sockets | `sb-bsd-sockets` `inet-socket`, `socket-bind` (127.0.0.1 only), `socket-listen 1`, `socket-accept`, `socket-name`, `socket-close`; `fnn-recv`, `fnn-send-all` (`sb-sys:wait-until-fd-usable` with the 10 s timeouts), `fnn-graceful-close` (alien `shutdown(fd, SHUT_WR)` then a one-second drain), `fnn-serve-client` | `tools/run_reader.py`'s loop: 512-octet reads, one wire event per core call, the retained suffix as transport bytes, close after a framing rejection |
| Entry | `fnn-main`, `fnn-dispatch`, `fn-native-entry` | The fixed positional protocol behind `--fn`, the outcome-to-exit-code map (the reader's pre-listen failures exit 1, as an uncaught Python exception does) |

Remaining Python-only: the BP hosts (`run_bp_ingress.py`, `run_bp_receive.py`,
`workflow_journal.py`, `receipt_journal.py`), the in-process `Acl2Store`,
`Store` and `Acl2Reader` classes that the fault-matrix, process-crash and
partition tests drive through `mock.patch`, and the reader's
`ReaderBridgeFault` path, which has no in-process analogue: a Lisp condition
that escapes a core call while serving is reported and exits 4.

### Differential evidence and measurements

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
