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

The repository `bin/fn` and its legacy service templates still start the Python
development owner. `packaging/install-native.sh` now installs a separate native
`bin/fn`, saved core, relocated SBCL runtime and native service templates without
starting a service. Its [scoped installation evidence](../planning/evidence/native-distribution-qualification-2026-09-21.md)
covers the frozen production image's startup and shutdown on persvati; it does
not establish complete service parity. `FN_HOST=native` through a Python argument
parser remains a test convenience, not the production entry point.

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

### The release

HST-017: The release is one tarball per platform (`fn-REV12-linux-x86_64.tar.gz`,
`fn-REV12-openbsd-amd64.tar.gz`) built by `packaging/release-tarball.sh` on
that platform from a `git archive` of REV, never a worktree. It is built only
when every book of the default image profile's include closure is green at
its digest (`tools/green_check.py --profile default --strict`, its line in
`share/fn/release-gate.txt`), from certificates acquired and load-checked
from the cache, and it carries the production image only. It holds one
directory `fn/`: `install.sh`, `bin/fn`, `libexec/fn/` (the frozen launcher,
the core, `source-revision`, the SBCL runtime and the libraries the image
loads that the platform lacks), `share/fn/` (the service template, the
example configuration, `docs/install.md`) and `SHA256SUMS`. `bin/fn
--version` prints REV. An installation is one directory: `install-native.sh`
and `install.sh` refuse a prefix that exists, and a reinstall is stop,
export, remove, install, import, start (D34); `install.sh` asks the new
release's own `status` about an existing node and stops at a store-format
refusal.

HST-018: No Python is on the path a deployed node or its operator verbs
execute. `tools/runpath_check.py` checks the tree (`make check`: every
process site in `host/`, the dlopen candidates, the shipped scripts and
service files) and every release before it is packed (`--tree`: no Python
file, interpreter or link; every executable a `/bin/sh` script or ELF; no
link or command outside the release; each ELF object's interpreter the C
library's loader, no RPATH outside, every DT_NEEDED carried or the C
library; every shared-object name in the saved core carried, the C library,
or the system TLS library HST-016 names).

HST-029: A release's `clients/` (packaging/install-clients.sh: the
command-line client programs, Python 3.9+) is held apart from the node's
path. `tools/runpath_check.py --tree` walks the node without `clients/`,
holds `clients/` to its own rule (Python source in `clients/lib/` only, no
object code or bytecode, launchers in `clients/bin/` that run only `python3`
and file-name tools, no service template: a client is never a service), and
fails when any script, launcher or service of the node's names `clients/`:
nothing the node runs can start a client. HST-018's claim is the node's; the clients' requirement (Python) is
stated in `clients/README.txt`.

HST-021: The Linux release runs on glibc 2.36 (Debian 12) and later. No
ELF object it bundles (the SBCL runtime, libsodium, libfn-mldsa65) needs a
`GLIBC_x.y` symbol version above `GLIBC_FLOOR` in `tools/runpath_check.py`,
the one place the floor is set; the release build's `--tree` check refuses
one that does, naming the symbol. Because a saved core starts only on the
runtime with its build-id, the floor runtime is the same SBCL version rebuilt
from its signed source with that build-id in a Debian 12 container
(`packaging/floor-runtime.sh`, `release-tarball.sh --runtime-from`), and the
freeze refuses it unless it prints the same version and starts the image's
core. The floor is a property of the bundled objects' version needs; it says
nothing of a glibc below it, and a symbol a core resolves by name at start
(the linkage table) is checked only by running there.

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

HST-005: the property names its fault domain. A demonstrably
connection-local fault costs that connection; a fault inside a shared owner action fences the store and
stops the service (exit 4) because the shared authority is uncertain. An
unexpected exception while serving one connection, outside the shared owner
action, must not end the process, because a news server faces untrusted
peers and one peer's input would then be a denial of service against every
other. Conversely the host does not keep mutating shared state to honour
the connection-local half: an indeterminate persistence observation fences
at exit 3 and any other failure inside the serialized owner action at exit
4, whichever connection it arose on. The host decides only
whether it still trusts that socket; the reply, the scope and everything the
state owner forgets are the core's one fault transition, which closes the
connection, clears the submission it had in flight and the transaction it
held, and leaves every other connection equal to what it was. The reply is a
FOURTH outcome, distinct on the wire from accepted, refused and uncertain, so
a fault is never read as a verdict on an article. A fault the host cannot
attribute to a connection or a peer abandons nothing, so it is counted and
bounded; and a lost core image is not a fault the host survives, because the
core is where every decision is made.

The native boundary makes attribution structural. Bounded receive, send and
graceful-close calls execute outside `fnn-owner-serialized` and cannot mutate
the owner, a Store or a journal; `fnn-owner-connection-call` may therefore map
an unexpected failure in exactly those scopes to the connection-local
condition. Its handler calls the host-called `fn-owner-fault` while holding the
owner mutex, copies the ACL2-produced 403/close effects and abandons only that
socket. EOF remains an ordinary close. Store/core conditions and process
resource exhaustion are never remapped by that envelope.

Conversely, anything unexpected during `fnn-owner-serialized` has crossed the
shared semantic boundary. Indeterminate persistence installs the exit-3 fence;
a core/store fault, an unclassified OS failure or any other serious condition
installs the exit-4 fence before releasing the mutex. Only the existing known
semantic-refusal class may escape without a global fence. Once either fence is
set, connection unwind performs no later owner close transition; service
cleanup wakes and joins all workers before closing journals or the Store.

HST-004: I/O, clocks, cryptographic primitives, and authentication are explicit
trust-boundary entries. The production integration must not contaminate book
certification with arbitrary raw-mode changes or hide trusted code inside a
claimed proved function. Certify the pure core in a clean environment.

The native BLAKE3 (lanes digest-native, blake3-digest) is such an entry,
visible by name: `host/native/digest.lisp` replaces, in the saved images only
and after a start-up check against the official vectors and the ACL2
definition, the raw bodies of the three BLAKE3 realisers the digest seams
attach to with the vendored C in `lib/libfn-blake3` (A-CRYPTO-NATIVE,
specs/failures.md). The books, their certificates and every theorem are
unchanged; the ACL2 definitions stay the reference and the fallback.

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

HST-009: Every native fn command exits with the code of its outcome class,
one fn-wide table: exit(f, x) = code(classify(f, x)). Each verb family
classifies its own outcome into one of seven classes, and one ACL2 map gives
the code (`*fn-outcome-codes*`, `fn-outcome-code`, books/outcome-class.lisp;
PRF-143). A code is a class, never a reason: many refusals share 1 and every
acceptance shares 0; the reason is the word the command prints. A wrapper
script reads the number, not the verb family.

| Code | Class | Meaning, and the question to ask next |
| --- | --- | --- |
| 0 | `:accepted` | Success, or already satisfied (a query answered, a duplicate of a held article, a replayed admission). An acceptance whose BPA delete has not completed also exits 0 and names the pending obligation on stdout (`bpa-delete=pending`). |
| 1 | `:refused` | A known refusal with a stable reason, printed as a word: a Message-ID conflict (`CONFLICT`), no store at the configured path (`NO-STORE`, with the `run init` line), a contended lock, a configured bound, an absent article on `inspect`, a BP refusal, a `bp decode` verdict the clock cannot decide. A refusal after reservation may consume a durable allocator number; it does not imply byte-for-byte unchanged storage. |
| 3 | `:fenced` | Indeterminate local durable authority: the outcome of a publication is unknown and recovery is required before further mutation. Nothing else is 3. |
| 4 | `:fault` | The host could not carry out the operation: invalid durable state, an I/O fault, a poisoned ACL2 bridge. |
| 5 | `:usage` | The invocation itself is wrong or unsupported in this image. |
| 6 | `:interrupted` | A connection lost after it existed. The peer may or may not hold the bundle; the local durable work is retained and re-offered under its own identity. No recovery is required. |
| 7 | `:not-connected` | No connection was established. Nothing left the node; the job stays queued. |

The families and their classify functions: the operator verbs
(`fn-native-operator-outcome-class`), the store verbs and every host
condition (`fn-outcome-of-host-condition`, which `fnn-exit-code-for` in
host/native/io.lisp calls), the control clients (`fn-native-control-outcome-class`;
`fn-thlc-outcome-class` for topic control), and the BP verbs
(`fn-bprc-class`; `fn-bprc-decode-class` for `bp decode`). The host's
`+fnn-exit-*+` constants are `fn-outcome-code` of their classes, read when
the image is built. The classes' codes are disjoint and fixed
(`fn-outcome-code-separates-the-classes`, `fn-outcome-code-table-by-definition`);
in every family the code is 3 exactly when the family's evidence is a fence
(`fn-outcome-code-is-fenced-iff-fenced`,
`fn-native-operator-exit-is-fenced-iff-uncertain`,
`fn-native-control-exit-is-fenced-iff-uncertain`,
`fn-outcome-host-condition-fences-iff-indeterminate`,
`fn-bprc-run-exit-code-is-fenced-iff-fenced`), so a fence is never masked
and a refusal is never reported as one (`fn-bprc-decode-never-fences`;
NO-STORE, `fn-native-operator-absent-store-is-refused`).

Outside the seven, and never an outcome class: `operator CONFIG health`
exits with its verdict (0 all clear, 19 unobserved, 20 to 29 the first held
state; HST-007). It is the one exception to the table, and it never
overlaps it: for every verdict the code is 0 or at least 19, and it is an
outcome code exactly when it is 0, the code of `:accepted`
(`fn-nh-exit-code-is-zero-or-past-the-outcome-codes`, books/native-health.lisp,
PRF-172, which reads `*fn-outcome-codes*` through `fn-outcome-codep`, so the
two tables cannot drift apart; PKT-329). A process ended by
a signal exits 128 plus the signal (143 on SIGTERM before an owner runs).
`tools/run_simulator.py` and `tools/certify_books.py` are evidence runners
with their own conventions.

Scope: the table is the native executable's, and its 3 is about this
node's own Store. An external client that lost a reply (tools/fn_client.py,
any NNTP client) is uncertain about the server's state, not about a local
Store, and must not run Store recovery; fn_client's outcome record carries
`"scope": "server"` and its own exit table (docs/agents.md).

The `CONFLICT` word is appended to the FNCT reply enumeration
(`*fn-nctrl-statuses*`), so every earlier status keeps its octet
(`fn-nctrl-conflict-keeps-every-earlier-octet`). An image from before it
decodes the new word as `:bad`; its control client then answers the
transport outcome after submission, uncertain (exit 3), not 4
(an executed witness in tests/acl2/outcome-class-tests.lisp). Clients are upgraded
with the node.

A reader whose ACL2 bridge is poisoned exits 4 rather than answering the next
client from a pipe whose replies can no longer be matched to its commands.
Successful queries and an article accepted with a retention obligation both
use code 0, so callers must also interpret the named operation and its result.

### BP run classes

The BP verbs (`bp`, `bp-service`, `bp-contact`, `bp-node`, `bp-app`,
`bp-obligation`, `tcpcl`) classify their run into five of the classes
above, which ACL2 computes from the evidence the host records
(books/bp-run-class.lisp, PRF-131): the reason of each `:forward-refused`
effect (the durable `:requeued` record's), each TCPCL session's outcome and
whether a publication in its delivery callback was uncertain, each article
verdict, and each publication program's classification. A fence dominates
everything, then a connection lost after it existed, then a refusal, then a
connection that never existed; the code is the table's
(`fn-bprc-exit-code` is `fn-outcome-code`).

The codes separate the classes (`fn-bprc-exit-code-separates-the-classes`);
no later or earlier evidence masks a fence (`fn-bprc-fence-is-never-masked`);
connection-local evidence never fences (`fn-bprc-connection-local-never-fences`).
Every `fnn-store-indeterminate` a BP verb raises is rendered as the fenced
code (`fnn-bp-verb`). `bp decode` answers an article verdict, not a run, and
publishes nothing: 0 accepted, 1 refused, and 1 for the verdict the clock
cannot decide, whose reason it prints (`fn-bprc-decode-never-fences`).

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

Native feed links retain peer identifiers as ACL2 octet lists. Socket buffers
remain byte vectors, converted explicitly at the core boundary. The actual
`fnn-feed-link-for-peer` constructor and `fnn-feed-dial-plan` calls are exercised
by `tests/native_feed_peer_octets.lisp` using the production conversion helpers
and a boundary observer. This regression rejects the previous vector-valued
identifier, which made the logical peer lookup report an absent endpoint. It
checks representation transport only; configured lookup, reconnection and
two-node exchange still require the saved-image gate.

The per-file layout's transaction namespace observer: a format-9 store has
no transactions/ directory, and the native open reads none; the record
log's segments are named and ordered by ACL2 (`fn-lgs-open-plan`,
books/store-log-segments.lisp). The one caller of the namespace decision
left is the Python store (tools/run_store.py through tools/frame_bridge.py,
`fn-store-txn-observation-octets` over `fn-store-txn-observation-selected`),
which still reads the per-file layout.

`build/fn-host` is one saved SBCL image: ACL2 8.7, the certified books the
hosts drive, the `:program` wrappers in `host/*-host.lisp`, and the raw-Lisp
adapter `host/native/io.lisp`. `tools/build_native_host.sh` feeds
`host/native/build.lisp` to a certified ACL2 and refuses the image on any
error marker, any uncertified-book warning, or a missing ready marker; the
books it `include-book`s are Makefile certification roots, so the image holds
the certified definitions and nothing reinterpreted. The world comes in
through ONE umbrella book, `books/image-world.lisp` (`-dtn`, `-store-test`
for the variants; generated by `tools/extract/world.py` from the script's
and its host files' includes), included first; the compiler is then off
until the trust tag, so every later `include-book` is a redundant event that
loads nothing, and a closure check prints `FN_IMAGE_WORLD_CLOSED`. A
top-level `include-book` reloads the compiled files of its whole closure, and
each load of a constrained or non-executable stub takes a thread-local-storage
index SBCL never frees (planning/evidence/arena-store-8-tls.md): at ~600
top-level includes the developer build used 60% of the saved launcher's
`--tls-limit 65536`, loaded once 4%. The build prints `FN_NATIVE_TLS` and
the script refuses an image over 25% (`FN_TLS_BUDGET_PERCENT`);
`tools/tls_check.py` checks the scripts' shape in `make check`, and
`--measure` names each compiled file's cost. `tools/fn_native.py`
launches its component store surface for development tests. Raw reader/owner
component tests use the separately built `developer` image profile; the
production image reaches the served owner only through the public native
operator.

The Python launchers above are development conveniences. The Python-free
component launcher is `packaging/fn-native`; its current operator commands and
unsupported profiles are documented in [the operator guide](../docs/operator.md).
It does not yet satisfy the full two-node production gate.

The build selects and serializes one entry profile, including in the DTN-only
build. The default `production`
profile writes `build/fn-host`, does not register the raw `owner` verb and
refuses the raw `reader` branch. Its one news-service start is
`operator CONFIG run`, whose store, listener, authentication, control and
posting projections come from the ACL2 native-operator/configuration plan.
`FN_NATIVE_PROFILE=developer tools/build_native_host.sh` writes the separate
`build/fn-host-developer` image with those two diagnostic entries enabled.
The DTN-only build writes `build/fn-host-dtn` by default and
`build/fn-host-dtn-developer` with the explicit developer profile.
Changing that environment variable when a saved image restarts does not change
its serialized profile. The developer image also honours the developer
selectors (the environment variables of `+fnn-developer-selectors+` and the
`store ROOT post` entry and its FAULT argument; [the operator guide](../docs/operator-internals.md#developer-selectors)
lists them). A production image refuses to start with any of them: `fnn-main`
runs `fnn-developer-selector-gate` before dispatch and exits 5 naming the
selector, before any store or socket is opened. Store diagnostics and the existing BP/TCPCL/application
verbs remain available in the production image; this split does not claim full
operator parity for them.

**Selected production entry restriction (2026-09-23).**
Raw `store ROOT post` is a developer diagnostic. A production image,
including the production DTN image, must reject that entry with the existing
unsupported-entry/usage exit 5 before opening the store, reading a payload,
or performing any publication. The serialized image profile controls this
restriction; an environment override at invocation cannot enable it.
Production posting goes through `operator CONFIG post` or the served NNTP
submission path, with the normal injection and durable outcome contract.
Store inspection and recovery remain available. The host startup gate and a
direct handler guard implement this restriction; saved-image evidence remains
required for the combined source. SCN-015 must exercise both
rejection orders (fresh and existing store), developer raw insertion, and
successful ordinary production submission. This changes the required
production surface; the da5fd8cb image still exposes raw posting.

Native peering now composes with that same public owner lifecycle in source.
At accept, raw Lisp supplies only the kernel address family and fixed-width
address octets. `fn-owner-peer-for-socket-address` owns their numeric IPv4 or
IPv6-loopback projection and configured-peer lookup, and `fn-owner-open-peer` owns
the session role. The lookup and open occur under the shared owner mutex. The
public operator installs the existing outbound feed's start, wake and close
hooks on this owner; the developer-only low-level owner entry remains a
separate diagnostic and does not acquire those hooks. A source-matched
production image at `915d5c72` passed private-loopback native transfers in
both directions, duplicate suppression, source-death requeue and a client
reset while a transit completed, as recorded in
`planning/evidence/native-peering-915d5c72-2026-09-21.md`. The native
listener profile accepts ACL2-parsed numeric IPv4 literals and explicit IPv6
loopback; general IPv6 textual policy remains open.

The public native operator also plans `peer add` and `peer remove` in ACL2.
The add plan constructs the complete typed peer record, including bounded
inbound and outbound defaults, and the ACL2 host wrapper applies its exact
set/remove delta through the existing configuration transaction. Raw Lisp
executes one accepted plan and never parses a host/port pair, wildmat,
streaming flag, source authorization or peer-record default.

The decimal-octet pipe, its nonce correlation and its reply bounds do not
exist in this host: every call is an in-process application of the wrapper's
executable counterpart (`fnn-call`, the raw-Lisp spelling of `ec-call`), under
the image's `guard-checking-on`, which the entry asserts is `t`, the same
policy the interpreted bridge evaluates under. A `:program` wrapper therefore
runs raw beneath its counterpart in both hosts; the complete call-graph guard
requirement of packet C3-05 is unchanged by the packaging. One exception, by
declaration (D40): an entry whose `definterface` carries `:raw-with (THM ...)`
is applied as its guard-verified definition, not its counterpart --
guard verification is the condition for faithful raw execution, and the named
theorems are the argument that the guard's carried conjuncts (the owner's
`fn-sn-statep` of the live Store, established at the open and preserved by
every transition) hold at the call. `books/definterface.lisp` checks declaration
shape against the loaded world, including a positive predicate conclusion.
That lint does not prove that theorem premises hold or that its arguments
name the entry's actual state and effects. The five proposed owner annotations
are withheld until that host-subject argument exists; they still use their
executable counterparts. The entry guard's arity and kind checks run before
either dispatch, and
`planning/interfaces.json` (`raw_dispatched`) lists every such entry. The
developer image keeps the counterpart path behind
`FN_NATIVE_DISPATCH_COUNTERPART=1` so a native can compare both.

The live carry state boundary is `fn-owner-retain-carry` with
`fn-owner-retain-carry-put` (books/owner-retain-state.lisp). Reading after
put returns exactly the supplied value, and writing a different global
leaves that read unchanged (PRF-1067). The actual carry writers use this
setter. These state effects do not establish the validity of the supplied
value or the invariant across a whole owner transition.

The off-mutex owner reclamation rebuild calls the logical entry
`fn-owner-orcp-rebuild` (books/owner-reclaim-carry.lisp). Its returned field 2
always satisfies `fn-prc-carryp` (PRF-1060), including a refused open's nil
carry. This initializes a returned value; live installation and later carry
preservation remain separate obligations. Its cold callees are not all
guard-verified, so the entry remains `:ideal`; this theorem enables no raw
owner dispatch.

### The saved image's memory

HST-025: The saved image carries the execution world only, and the owner
serves on a small collection trigger. `host/native/build.lisp` (and
`build-dtn.lisp`) loads `host/native/strip-world.lisp` after the last event and
immediately before `save-exec`. Every symbol keeps, at its current value, only
the twelve execution properties (`symbol-class`, which the `*1*` dispatch
reads, the signatures and guard the guard-failure forms read, the stobj and
attachment properties), and the world keeps the other pairs a node was
recorded reading (lane image-anatomy: LP's translate of the return form, two
tables, five world globals) plus the landmarks and indices of the start path
with `ACL2_SYSTEM_BOOKS` set, over a bottom of command 0, event 0 and
`project-dir-alist` so that LP's `lookup-world-index` and
`replace-project-dir-alist` still find what they walk to. The build residue
goes too: the closed input-channel symbols of every file the build read,
ACL2's documentation text, defconst's redundancy discriminators, the
build-sized hons space (replaced by a small one) and memoize call array.
`tools/build_native_host.sh` refuses an image whose log lacks the strip
marker. (A second save of the stripped core, from a process that never ran
ACL2, was measured and is not taken: it raised the resident set at start
from about 36 to 63 MiB on hbox and from 39 to 47 MiB on OpenBSD.) No
compiled definition changes: they live in function cells, not in the world.
A guard violation inside `fnn-call` is the same fault line and exit code as
before (the developer verb `guard-probe`), because the guard term in the
failure is compiled into the executable counterpart. The owner collects every
64 MiB during recovery and a checkpoint publication (PKT-316), less when the
process reserved under 1 GiB (a sixteenth of the reservation, at least 8 MiB:
a copying collection of the nursery needs as much again free); after recovery
one full collection returns the recovery's garbage pages to the system; from
`LISTENING` it collects every 8 MiB. The figures and the ACL2 8.7 source that
reads each kept property are in `planning/evidence/image-floor-2026-09-26.md`;
the native case is `tests/test_native_image_floor.py`. The heap a profile
needs is still heap-from-profile's derivation (HST-013), which the list
representation of the retained history dominates.

The prover's session state outside the world goes too (lane image-strip,
`fnn-strip-prover-state`): the global enabled structure (a state global) and
the compressed arrays of every enabled structure (`ENABLED-ARRAY-n`,
`ARITHMETIC-ENABLED-ARRAY-n`), and the type-set tables (ACL2's boot constants:
each value, its `-LIST` source and its compressed array). Their readers in the
ACL2 8.7 source are event and prover functions only (`ens`, `set-w`,
`update-wrld-structures`, the enabled-structure installers,
`with-useless-runes-aux`, `type-set-binary-+`, `type-set-binary-*`,
`type-set-<`, `type-set-finish-1`, the proof builder's), which the stripped
world already cannot serve. Each value becomes an `fnn-stripped` instance
naming it; the arrays lose their `acl2-array` property; the `#n=` reader's
buffer is reset small (ACL2 grows it on demand) and the memoization tables,
caches, are cleared. The strip lists what it replaced as the `S` lines of
`IMAGE.world-deps` (version 2). The qualification check
(`tools/runtime_image/world-deps-check.lisp`, loaded by
`tests/test_native_image_differential.py` into every stripped run) proves at
load that each item holds its trap, traces every reader above (a call is a
`PROVER-READ`, a failure) and reports at exit whether anything rebuilt an
item. ACL2's system code is compiled at safety 0, so a prover read of a trap
is not guaranteed to signal (one faulted at address 0); the trace, not the
trap, is the check. A use from code compiled with safety signals a type error
naming the item (the module's witness). The size gained is measured at
convergence.

The thread stacks are the reservation's second part
(`books/heap-reservation.lisp` `fn-heap-reserve-decide`, called by
`host/native/heap.lisp` `fnn-heap-reservation` from the `heap -- ARGV` probe).
SBCL reserves for every thread its control stack and 2.5 to 3 MiB of runtime
areas; the image's own launcher gave every thread 64 MiB, so a node with 32
connections reserved about 4 GB beside its heap, and on OpenBSD, where a
reservation counts against the login class's datasize, the fourteenth thread
was refused at 1,536 MiB. The figure is the heap-figure heap, plus the
image's own mappings outside the dynamic space (at most the core file), plus
THREADS x (STACK + <!--limit:thread-runtime-mib-->4<!--/limit--> MiB; measured 2.5 MiB on Linux, at most 3 on OpenBSD):
THREADS the <!--limit:fixed-threads-->12<!--/limit--> fixed threads, the <!--limit:mux-loops-->2<!--/limit--> I/O loops that serve every connection
(a connection is no thread since connection-multiplexing; the reservation
counted one per `max-connections` until lane reservation-after-flip) and the
<!--limit:control-clients-->16<!--/limit--> control clients: <!--limit:fixed-threads + mux-loops + control-clients-->30<!--/limit-->; STACK a constant <!--limit:stack-kib,-->1,024<!--/limit--> KiB, seven times the 142 KiB
the node needs whatever the article since the served path's per-line
recursions became loops (lane served-line-iterative, PRF-218; before, the
need grew by 32 octets per line and this figure carried a per-line term). A total the machine cannot hold is refused by name
before anything runs (`refused machine-cannot-hold-threads reservation=MB MB
machine=M MB`, exit 1), and the launcher passes `--control-stack-size KBKB`
with the heap figure. The probe prints `heap=MB MB profile=WORD machine=M MB
stack=KB KB threads=N`.
`init` sizes within an explicit process budget and prints its decision
(`fn-heap-init-decide`, PKT-582; gpt-6's wave-5 review s.8): the budget is
the least of the physical memory less the OS's share (a quarter, at least 512
MiB: detected memory is not all the service's), each limit the process runs
under (RLIMIT_DATA, RLIMIT_AS, every cgroup memory.max: systemd's MemoryMax,
OpenBSD's login class) and the operator's `FN_INIT_BUDGET_MB`. A request that
names no capacity field (a bare `init`, and every mission: they set only the
article bound and groups per article) takes a conservative preset: development
when the budget holds its whole reservation at the configuration's default
max-connections, else the small preset (R raised to the article record the
request needs); never scale. `FN_INIT_SIZING=largest` takes the first of
scale, development and small the budget holds. The request's own fields are
laid over the preset and never lowered; when no preset holds them, init
refuses by name and creates nothing: `refused init-budget-cannot-hold-profile
profile=WORD sizing=MODE reservation=MB MB budget=MB MB`, exit 1. A request
that names a capacity field or a preset (`--profile development|scale`) is
the operator's: written as named, never resized
(`fn-heap-init-decide-honors-the-operators-request`). init prints `init:
profile=WORD sizing=conservative|largest|requested reservation=MB MB
budget=MB MB within-budget=yes|no`; for a capacity-free request it is always
`yes` (`-sized-init-is-held`) and the reservation is within the budget and so
within the machine the run judges
(`fn-heap-init-decide-fits-the-budget-and-the-machine`); `no` names an
operator's request the launcher's probe will refuse on this machine.
Under 2 GiB the default mission (1 MiB articles) inits on the small preset's
capacity with its own fields (1,326 MB with 60 stacks of 1 MiB).

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

The reply octets are never built as a list on the served read (PRF-192,
2026-09-26, lane egress-span; PKT-491): `fn-served-reply-to-buffer`
(books/served-reply-buffer.lisp) writes each `(:reply octets)` effect into
an octet buffer, and its keystone `fn-served-reply-to-buffer-is-the-reply`
says the buffer's range [0, len) is `fn-served-reply-octets` of the effects
whenever every reply effect is octets (the answer `:ok`); the host faults on
`:malformed` as it did on a non-octet reply. Until HST-023 the buffer was
the live `fn-octets`, filled under the service mutex and copied out once
before the mutex was released.

HST-023: The owner mutex is entered through a gate whose next class ACL2
picks, and a served reply is an immutable render plan the connection's I/O
loop writes off the mutex in windows ACL2 sizes. The native owner keeps one
mutation owner (every bounded semantic step runs under the service mutex),
and the decision the Lisp runtime's mutex used to make -- which waiting
thread runs the next step -- is ACL2's (books/owner-scheduler.lisp
`fn-osch-next`): four service classes, control (with maintenance), reader,
poster and transit, in that cyclic order; the host observes how many threads
of each class wait (the class of a quantum is the socket it arrived on: the
control socket's requests and the maintenance steps are control; a reader
connection's open, steps, idle, close and release are reader; a peer
connection's, the feeds', the pull's and the BP node's quanta are transit; a
submission through the control socket is poster) and asks ACL2 which class
runs the next quantum (the class's slot too is ACL2's, `fn-osch-class-index`);
within a class the host serves arrival order, so the bound below is on the
class's turn, and a control request behind N control requests waits N + 1
turns; a thread that re-enters the gate while it holds the owner is a host
fault. The keystone
`fn-osch-control-waits-at-most-the-bound`: while control has a waiter, at
most three quanta of the other classes run before a control quantum, from
any cursor. That bound counts the picks outside a batch in flight; while
one is in flight only `:inspect`, `:commit` and `:reader` run, and until
lane durability-bugs (2026-09-28) the pipelined committer prepared a next
batch behind every barrier, so under sustained POST load a batch was always
in flight and a control, poster or transit request was never admitted. Now
the committer's wake (`fn-ocp-wake`, BLOCKED; host
`fnn-owner-commit-wake`, which reads the gate's waiting counts, and again
inside the START-NEXT quantum) prepares no next batch once one of those
classes has waited through four `:commit` quanta in flight (the pass budget
`*fn-ocp-pass-bound*`, counted by the gate's pick and reset at a pick where
none waits: background waiters, the feeds' transit ticks and maintenance
steps, arrive during nearly every barrier, and stopping at the first would
unpipeline every batch), and the keystone
`fn-ocf-control-waits-at-most-the-bound` (PRF-901,
books/owner-commit-fairness.lisp) holds over the host's pick, wake and
commit events from any scheduler value: while a control request waits at
every pick, before it is admitted (or the owner stops) at most 22 quanta run
that are not `:inspect`, a reader during a barrier or a START-NEXT that took
nobody, and at most six batches are sealed, so its wait is at most seven
barriers plus those quanta (in practice two or three). A quantum is one bounded semantic
step, unchanged by this requirement (a served read with its drain, one control request, one transit
step); the journal writes stay inside it. The exposure charge (PRF-161) is
decided in the same critical section as the step it admits. What leaves the
critical section is the reply's rendering: `fn-owner-chunk-span` returns one
typed step result (books/served-plan.lisp `fn-splan-step-make`: the effects,
the close, STARTTLS and submission projections, the consumed prefix, the
refusal lines and the exposure close) and the connection's I/O loop
(host/native/mux.lisp) renders the plan into a fresh private buffer, never
the live `fn-octets`, one window per `fn-splan-window` call, writing each
window before it renders the next and holding one window and the plan's
continuation, never the whole reply. ACL2 sizes each window
(`fn-splan-window-size`: the remaining octets of the effect the window
starts in, so a materialized reply effect is rendered whole rather than held
as a list sixteen times its size while the socket drains; zero exactly when
the plan is done, `fn-splan-window-size-is-positive-until-done`, so the loop
progresses). The keystones `fn-splan-window-is-a-prefix-of-the-reply` (a window followed by
the continuation's debt is the plan's debt, and an unfinished plan's window
writes something) and `fn-splan-windows-are-the-reply` (a plan drained to
done wrote exactly `fn-served-reply-octets` of the effects) say the bytes on
the socket are the bytes the served machine decided, whatever the window
size and however the socket paced the windows; a pull's logical connection
renders its plan the same way (host/native/pull-service.lisp). `health`
prints, after the
log-sink line, one line per class with its holds in five buckets (under 1,
10, 100 and 1,000 ms and at least a second), the longest hold, the longest
wait and the waits of a second or more, folded by ACL2
(`fn-osch-observe`, `fn-osch-health-lines`); the exit code stays the
verdict's (`fn-nh-report-exit-of-render-and-more`). The live octet buffer
`fn-octets` is input-only under the mutex. Measured on the mixed hour and
under 40 readers in planning/evidence/owner-scheduler-2026-09-26.md.

### The disk as an adversarial environment

HST-026: The node's answers are stated relative to a disk (and a clock)
with unbounded latency: a batch barrier is a request with a deadline, the
disk's mode is ACL2's, reads and status never wait on a barrier, and a POST
that arrives while the disk is slow is refused try-later with the reason.
Design: planning/design-time-model-2026-09-27.md; slice 1 of it is this
requirement (PRF-311, books/owner-time-model.lisp). The gate's value
carries the disk's state and a recorded time: every disk event (the
barrier's issue, its completion, a clock event) carries one monotonic
reading the host takes under the gate mutex, recorded monotone (a lower
reading is counted, `:clock-regressed`, and moves nothing back); every
decision reads the recorded time. The barrier's deadline D is the live
configuration's `barrier-deadline-ms` limit (default 5,000 ms). The
committer's wait for the syncer is timed by ACL2 (`fn-otm-wait-ms`: to the
deadline, then each second) and each expiry appends a clock event. A
barrier pending past D makes the disk `slow`: a timeout is not a failure
(the batch stays in flight and its members wait for their replies, which
follow the completion: `fn-otm-disk-event-keeps-the-pipeline`); a served
POST arriving then is answered RFC 3977 section 6.3.1's 441 with the reason
(`441 posting failed; the disk is slow (a write has waited N ms, deadline D
ms): nothing was stored, try again later`) through fn-own-outcome's
`:refused` outcome, nothing stored (436 is IHAVE's code, section 6.3.2);
`health` and `status` print `disk slow: barrier N ms pending` (a shed
happens exactly when they do: `fn-otm-shed-iff-slow`); the service log
names the episode entered and left. The completion is the recovery
(`fn-otm-return-recovers`). Keystone `fn-otm-barrier-reader-bound`: while a
barrier is pending and a reader waits, only `:inspect` and `:commit` quanta
run before it, at most one START-NEXT that took members, and at most one
more `:inspect` than `:commit`; the device's latency is not a quantity of
the bound.

Slice 2 (lane time-model-2; PRF-311, PRF-323). The limits are three
profile fields, the live configuration's `barrier-deadline-ms` (D),
`barrier-stall-ms` (H, read as at least D) and `clock-event-ms` (the
committer's cadence) rows, each set by `policy set SLOT N` (ACL2's
books/native-admin.lisp: positive milliseconds; defaults 5,000, 30,000 and
1,000) and carried by the barrier's issue; a batch in flight keeps the
limits it was issued with. While the disk sheds (`slow` or `stalled`): a
served read runs with posting not permitted, so a POST command is answered
RFC 3977 section 6.3.1's 440 with the reason before any article is sent
(`fn-otm-read-span-while-shedding`); an article whose POST was answered 340
before is answered 441 with the reason as in slice 1 (both lines are ACL2's,
`fn-otm-disk-effects`, in place of the served machine's generic texts, only
when the connection's posting bit was on before the read); a peer's read is
a reader-class quantum under the disk-slow posture, so IHAVE is answered 436
"retry later; the disk is slow" (RFC 3977 section 6.3.2) and CHECK 431 (RFC
4644 section 2.4), at once and whatever the node holds
(`fn-peer-shed-offer-is-disk-slow`, PKT-858); an operator post, a live
configuration change or a moderation request on the control socket is
answered BUSY at once, before it waits for the gate. Past H the disk is
`stalled`: once per barrier every poster of the batch in flight and of the
batch prepared behind it is told ACL2's uncertain reply and closed -- never
accepted, never refused (`fn-otm-stall-tells-no-member-its-outcome`): the
barrier is pending, not failed, and its bytes may still become durable --
and the POSTs queued behind them are refused try-later, nothing stored.
A POST the store refuses when it is drained -- full (`unaffordable`,
`memberships`) or malformed -- wrote nothing, so it is never a member of a
batch: it is told its named refusal at its drain, before any barrier and
whatever that barrier does, and a START all of whose POSTs were refused so
issues no sync (`fn-ocs-unstaged-start-tells-its-refusals`, PRF-354). A
refusal that names another record (a duplicate, a conflict, the generic
refusal) still waits for its batch's barrier: the record it names may be one
the barrier has not fenced.
When the device returns the batches complete: an article whose poster was
told uncertain IS stored. That is the documented ambiguity, and it is RFC
3977's (section 6.3.1: a client without a clear answer checks before it
reposts). fn's check is the SAME article re-sent under the SAME Message-ID
(NNT-019), never a STAT: a 430 while the barrier is pending proves nothing,
because the barrier may still complete. The re-sent article is refused
try-later while the disk sheds (nothing is stored twice) and, after the
completion, answered `441 posting failed; this article is already stored
here` or `240`. A member told uncertain is never answered again: the stall's
release is an early answer in ACL2's ledger of the request in flight, and
the barrier's late completion is consumed once, into its own generation,
answering only the members not told (HST-031, PRF-384,
`fn-otb-a-member-is-answered-once`,
`fn-otb-a-late-completion-is-consumed-once`; the sealed batch stays the
syncer's until then, `fn-otb-a-deadline-keeps-the-io-owned`). The adopted
bars (D 5 s, H 30 s with at most 1 s notification slack, a cold read's 5 s
dependency deadline and its 403) are planning/design-time-model-2026-09-27.md
section 4b. A restart is a new clock domain: the decision journal's start
entry records the wall observation and whether it is usable, never a
monotonic origin, and no decision of a run reads an earlier run's reading
(`fn-otb-a-restart-forgets-the-previous-clock-domain`; the push feed's
back-off, PRF-385). F4-W
(`fn-otm-f4w-stall-within-h`): the committer's clock events, each within
its wait plus the timer's lateness L, enter `stalled` at most H + L after
the barrier's issue (its wait never reaches past H), so every POST is
answered accepted, refused, uncertain or try-later within H + L + one
quantum of its article's arrival. `health` and `status` print `disk
stalled: barrier N ms pending ... members=uncertain`; the service log names
the stall and the recovery after it. Not yet: a transfer during `slow` (an
IHAVE article after a 335 given before the disk went slow, a TAKETHIS) waits
for the barrier as in slice 1, the inline barrier and
configuration publication as requests (slice 3), `health`'s exit in
`stalled` (PKT-853 (b)).

A graceful stop (SIGTERM, PKT-875; PRF-357, books/owner-stop-drain.lisp)
drains before its fence: the owner stops accepting and stepping input, the
I/O loops keep delivering and the committer keeps committing, and each
poster is told at its batch's COMPLETE as always (240 only after a fenced
barrier). ACL2 decides from each observation (`fn-osd-drain-step`, every
100 ms after a clock event): the fence comes only when no member awaits its
reply, no reply is unsent and no batch is in flight unless its members were
released (`fn-osd-stops-only-when-nothing-is-owed`); at the drain deadline,
the configuration's H after the SIGTERM, the members still in flight are
released uncertain by the stall's own rule and the queue shed
(`fn-osd-releases-only-at-the-deadline`), and the drain ends 10 s after that
release at the latest (`fn-osd-drain-ends-by-the-deadline`). A stop never
closes a connection whose article committed without its reply before that
bound. Not covered: a command read but not yet stepped at the SIGTERM (an
article after its 340) is not answered; it is not stored. The fence itself
still waits for a barrier that does not return (a stuck device holds the
exit, never a reply).

HST-028: Every decision that stores nothing is reproducible from the
decision journal (PRF-322, books/owner-time-journal.lisp). Each event the
scheduler's disk-and-clock value takes -- a barrier's issue and completion,
a clock event of the committer, of a status render or of a served read
(whose monotonic and wall readings are the owner's clock for that read:
N3 of lane proto-determinism; the wall reading's validity is ACL2's,
`fn-otm-wall-reading`) -- and each note (the stall's release: members told,
queued POSTs refused) is one entry `SEQ OP READING A B C WORD`, rendered by
ACL2 and offered to the service-log writer thread, which appends it to
`STORE/decisions/decisions.fnj`: never written on the owner and never waited
on, so a journal on the disk that is stalled costs nothing but queue space,
bounded by ACL2's sink; an entry the sink drops is counted and is a gap in
SEQ. Keystone `fn-otm-journal-determines-the-decisions`: the journal of
any run of the host's calls reads back whole and replays from the run's
start (a start entry, SEQ 0, per run) to agreement at the run's disk and
clock, and every decision the host asks of the value reads only those.
The operator's replay is `fn store ROOT journal`: ACL2 reads the file back
and replays it (`fn-otm-journal-report`, `fn-otm-journal-exit`: exit 0 when
it agrees, 1 at a gap, divergence or malformed entry).
What a process death with entries unflushed loses is exactly those entries:
the replay of decisions that stored nothing. No durable state depends on an
entry (a disk event keeps the pipeline; a refusal stores nothing), and the
record log alone determines the durable state.

The free space (lane health-truth; PRF-359, PKT-872). A full filesystem
was found by the append (ENOSPC after the members had sent their articles:
the recovery event, every member uncertain). The free octets of the store's
filesystem are now a recorded observation, a `:space` event (journal op 6)
carrying statvfs's figure and ACL2's need (`fn-otm-space-need`: PRF-129's
maintenance reserve, two batches at `log-batch-octets`, and the operator's
`disk-reserve-octets` row, `policy set disk-reserve-octets N`, default 64
MiB), taken at every barrier's issue, at every `health` and `status`
render, and before a served read's admission when ACL2 says one is due
(`fn-otm-space-due-p`: a cadence after the last). Below the need the disk is
`full` and every write is shed as while `slow`: a POST command is answered
`440 posting not permitted now; the disk is full (F octets free, N needed),
try again later` before its article, an article already sent `441 posting
failed; the disk is full (...): nothing was stored, try again later`
(`fn-otm-full-sheds`, `fn-otm-admit-keeps-the-space-need`); `health` holds
`disk` with `mode=full` (exit 28); the next observation with room recovers
(`fn-otm-space-recovers`). An unobserved figure is never `full`: an append
that then meets ENOSPC stays the recovery event.

HST-030: The decision journal never keeps a torn line (PKT-872, PRF-360,
books/owner-time-journal-writer.lisp). The writer thread appends each entry
by ACL2's rule: it carries the length of the file's whole entries; an append
that fails (ENOSPC part-way through a line, any write error) is truncated
back to that length, and when the truncation itself fails the journal is
closed for the run, so no line is ever appended after torn octets. The
first entry written after a lost one (a failed append, or an entry the sink
dropped at its bound) is preceded by a mark line `0 7 0 0 0 0 0`, which the
replay reads as `gap-at-N`, N the first sequence number missing; a gap
detected by the sequence numbers also names the first one missing. At each
run's start the file is cut back to its last whole entry (read backwards in
bounded chunks), so a process that died mid-append leaves nothing the next
run appends after. Keystone `fn-otm-jw-file-reads-agrees-or-gap`: from a
file of whole entries, whatever happens to each offered entry -- written,
dropped, failed after any number of its octets with the truncation holding
or not, and so at every process-death cut -- `store ROOT journal` reads
`whole` or `torn`, never `malformed`, and replays to agreement or to the gap
one past the last entry replayed (`fn-otm-jw-gap-is-the-first-lost`: the
sequence number of the first entry lost). A journal that cannot be written
costs replay of decisions that stored nothing, never service: the owner
keeps serving and `health`'s log-sink line counts what was dropped.

HST-031: The adopted F4 bars (PRF-384, PRF-385; planning/design-time-model-2026-09-27.md
section 4b): D 5 s, H 30 s with at most 1 s notification slack, a cold read's
declared 5 s page-dependency deadline. A deadline is a notification, never a
cancellation. The barrier's late completion is consumed exactly once, into
the generation it was issued under, answering only the members not told at
the stall (`fn-otb-a-member-is-answered-once`,
`fn-otb-a-late-completion-is-consumed-once`); what the I/O owns is kept until
then (`fn-otb-a-deadline-keeps-the-io-owned`). A read whose page does not come
by its deadline is answered `403 article temporarily unavailable ... it is
not absent`, never 430 or 423 (`fn-otb-a-late-page-is-unavailable-never-absent`;
its host call site is the asynchronous page fault still to come). A restart
is a new clock domain: the decision journal's start entry records the wall
observation and no monotonic origin, and no decision of a run reads an
earlier run's reading (`fn-otb-a-restart-forgets-the-previous-clock-domain`);
the push feed's restart forgets the previous process's back-off deadline
(`fn-feed-restart-forgets-the-previous-clock-domain`). Scenario SCN-202.

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
oldest first, to `fn-store-sn-recover-records`, the host's intern and `fn-store-sn-recover-rows` with the article records and the
frontier. The native host sends the article records in chunks closed at
`fn-srs-chunk-fullp`'s work quantum (one record always taken first, so none
is refused or split for its size): per chunk `fn-store-decode-records` and
the guard-verified `fn-srs-intern-step`, then `fn-store-sn-recover-rows` over
`fn-srs-rows`; no octet list or decoded event of the whole history exists at
once, and any chunking opens the same Store
(`fn-srs-steps-are-one-step-of-the-concatenation`,
books/store-recover-stream.lisp, PRF-261). Without a selected pack the
transaction files are read a chunk at a time as the replay takes them: each
file goes to `fn-store-unframe-split` as its protected prefix and trailer
(the payload is the prefix's tail, no copy:
`fn-srs-unframe-is-the-frame-decode`), and the chunk to
`fn-srs-checked-decode` with each file's number, which checks every record's
sequence in the one decode (`fn-srs-checked-decode-is-the-per-file-check`,
PRF-266). The open answers the history's record count and keeps no records;
a verb that needs their octets reads them after the open under its lock
(`fnn-history-records`). On a format-9 store (what `init` writes) the open is
`fnn-recover-log`, which answers the count the same way (a state-checkpoint
open answers S plus the suffix's count, without re-encoding the covered
prefix), and `fnn-history-records` reads the record log: the
history as the open read it (`fnn-log-history-each`, streamed; a checkpoint's
covered prefix a chunk at a time when segments were dropped, the closed segments scanned again
from disk, then the log kernel's committed records, `fn-lgk-committed`); a
rotation in the process since the open is a fault, never a shorter history.
The per-file reads are unreachable since the open refuses a format-8 profile
by name (`:store-format`). A store with no configuration record is refused, and the served
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
| SBCL runtime | `sb-ext:exit`, `sb-sys:enable-interrupt`, `sb-sys:make-fd-stream` on descriptors 1 and 2, `sb-ext:*posix-argv*` after `--fn` | Process entry, exit and standard streams; outside owner mode SIGTERM exits 143. Owner mode's handler only sets a process-global monotonic flag and calls raw `shutdown(2)` on a captured listener fd kept open through cleanup; the main owner thread performs stop, joins, module close, FNFD/Store close, then exits 0. `--disable-debugger` prevents an escaped condition from waiting on a terminal. |
| Files (sb-posix, sb-unix) | `fnn-open`, `fnn-close`, `fnn-fstat`, `fnn-lstat`, `fnn-check-regular`, `fnn-read-fd`, `fnn-read-regular-bounded`, `fnn-write-all`, `fnn-list-directory`, `fnn-link`, `fnn-replace`, `fnn-unlink`, `fnn-mkdir`, `fnn-safe-directory` | `O_NOFOLLOW` opens, `fstat` regularity checks, bounded reads, `O_EXCL` staging, `link`/`rename` publication and directory grammar |
| Barriers | `fnn-durable-barrier`, `fnn-fsync-file`, `fnn-fsync-dir`, `fnn-fsync-regular` | The platform table above: `fcntl(fd, 51)` (`F_FULLFSYNC`, which sb-posix does not name) on darwin, `fsync(2)` after `ENOTTY`/`ENOTSUP`/`EOPNOTSUPP`/`EINVAL`/`EPERM`, `fsync(2)` elsewhere; the five recovery barriers, the staged-file and directory barriers are real calls |
| Locks | `fnn-flock` (alien `flock(2)`), `fnn-open-lock` | `LOCK_EX`/`LOCK_SH` with `LOCK_NB`, the same refusal and fault classes |
| Cryptography | `fnn-trailer` calls `fn-frame-trailer`; the diagnostic `blake3` verb asks ACL2 (`fn-blake3-of-prefixed-buffer-any`) | Store and metadata trailers are BLAKE3 (`books/blake3.lisp`, attached by `books/crypto-attach.lisp`; the C BLAKE3 in the saved images after its start-up check, A-CRYPTO-NATIVE). `python3 tools/fn_native.py blake3-selftest` compares the image's verb with `tools/blake3_ref.py`'s pure-Python BLAKE3. |
| Store metadata | `fnn-metadata-config-frame/-decode`, `fnn-metadata-frontier-frame/-decode/-next`, `fnn-load-config`, `fnn-refuse-another-format` | `config.json` holds the ACL2-sealed `FNSM` profile frame. The store has no frontier file: the allocation frontier is derived from the record log at open, a reservation goes through `fnn-log-reserve` (`fnn-advance-frontier`), and the frontier's `FNSM` frame is built only where an export carries it. `books/byte-store-frame.lisp` owns profile values, framing, parsing, integrity and the frontier successor. The native host moves octets; a `config.json` that ACL2's open names as another format is refused before any other check reads the store (`fnn-refuse-another-format`). |
| Core calls | `fnn-call`, `fnn-core`, `fnn-core-state`, `fnn-global` | Counterparts of `fn-store-sn-reset/-recover-records/-recover-rows/-io/-prepare/-existing-action/-pending-octets/-known-abort/-refuse-reservation/-finish/-article-count/-next-txid/-group-next/-pin-count/-reserved/-lookup/-lookup-foundp`, `fn-store-record-sequence/-txid`, `fn-store-frame-constants/-store-protected/-store-decode`, `fn-store-metadata-config-frame/-decode`, `fn-store-metadata-frontier-frame/-decode/-next`, `fn-store-txn-name`, `fn-sbud-post-boundary`, `fn-store-charge`, `fn-store-group-codes` (names against the replayed domain), `fn-store-cfg-generation/-served/-domain`, `fn-cfg-host-initial-octets`, `fn-reader-use-seed/-store`, `fn-reader-set-posting`, `fn-reader-reset/-chunk/-outcome`, `fn-reader-model-octets`, and the payload-arena updates the host performs itself (`fn-intern-events` at the open after emptying the arena; the seal of the octets a prepare's `(:seal OCTETS)` or `:seal-buffer` names, through the arena's exports in `books/payload-arena.lisp`), because a `:program` entry that updated the arena would carry ACL2's invariant-risk; the globals `fn-reader-output`, `fn-reader-closep`, `fn-reader-submit-octets/-msgid`, `guard-checking-on`. A `raw-ev-fncall` throw, Lisp error, core error flag or malformed result is a fault; a returned semantic refusal remains a refusal |
| Sockets | `fnn-listen` (`sb-bsd-sockets` `inet-socket`/`inet6-socket`, loopback unless an address is passed), `fnn-connect` (one nonblocking `connect(2)` and `SO_ERROR` completion under its caller deadline), `fnn-accept-loop`, `fnn-socket-fd`, `fnn-socket-shut`; `fnn-recv`, `fnn-send-all` (`sb-sys:wait-until-fd-usable` with absolute deadlines over nonblocking read/write retries), `fnn-graceful-close` (alien `shutdown(fd, SHUT_WR)` then a one-second drain), `fnn-serve-client`; AF_UNIX bind/connect in `host/native/control.lisp` | The feed gets its TCP completion timeout from ACL2. Synchronous DNS remains a separate availability boundary: the host does not claim that this deadline bounds `getaddrinfo`, and it never terminates a resolver thread. The served reader loop and bounded FNCT local-control transport use the same raw socket surface. Control accepts one sealed request and returns one sealed reply per connection; ACL2 owns both frames and their caps. Raw Lisp transports the bytes and never opens the Store from the control module. |
| Entry | `fnn-main`, `fnn-dispatch`, `fnn-select-image-profile`, `fn-native-entry` | The fixed positional protocol behind `--fn`, the build-time production/developer entry split, and the outcome-to-exit-code map. Production owner start is only the registered public `operator`; raw owner/reader diagnostics exist only in the developer image. |

The native anchor follow-on is loaded by the common saved-image build:

| Surface | Functions | What it does |
| --- | --- | --- |
| Roughtime primitives | `fnn-crypto-startup`, `fnn-crypto-ed25519-observe`, `fnn-crypto-anchor-leaf` in `host/native/crypto.lisp` | Reinitializes libsodium after every saved-image restart; returns primitive observations only over ACL2-produced subjects |
| Roughtime acquisition | `fnn-anchor-csprng-nonce`, `fnn-anchor-udp-exchange`, `fnn-anchor-acquire` in `host/native/anchor.lisp` | Consumes ACL2's selected server/key/wire-bound profile, reads the nonce from `/dev/urandom`, sends ACL2's request in one connected IPv4 UDP datagram, probes one byte beyond ACL2's response bound, calls the ACL2 parser and crypto seam, and preserves observed/refused/uncertain/fault |
| Anchor decision and FNAN | `fnn-command-anchor`, `fnn-anchor-decision`, `fnn-anchor-publish`, `fnn-anchor-recovery-barriers` | Holds the store writer lock, calls the actual ACL2 acceptance entry, drives ACL2 `fn-anchor-rp-step` through pre-syscall issue and every result, reports accepted only after the directory barrier, and barriers a recovered final file and directory before decode |

HST-016: The native host's cryptographic libraries are ones every
supported system has or the release carries; none is a build of a specific
OpenSSL. Three seams, each loaded at image build and re-loaded and re-checked
at every start (a missing library or function refuses the start by name):

| Seam | Library | Functions | Found |
| --- | --- | --- | --- |
| TLS (STARTTLS, the TLS-only listener, the peer feed's client) | the system libssl/libcrypto: OpenSSL 3.0 or later, or LibreSSL 3 or later | `TLS_server_method`, `TLS_client_method`, `SSL_CTX_new/free/ctrl/use_certificate_chain_file/use_PrivateKey_file/set_default_passwd_cb/check_private_key/set_verify/load_verify_locations`, `SSL_new/free/set_fd/accept/connect/set1_host/ctrl/get_verify_result/get_error/pending/read/write/shutdown`, `ERR_clear_error/get_error/reason_error_string`, `OpenSSL_version(_num)`, and for `tls reload` and the served line (HST-020) `SSL_CTX_get0_certificate`, `X509_get0_notBefore/notAfter`, `X509_get_ext_by_NID/get_ext`, `X509_EXTENSION_get_data`, `ASN1_STRING_get0_data/length`, in `host/native/tls.lisp` (`*fnn-tls-required-symbols*`); the protocol floor and SNI go through `SSL_CTX_ctrl`/`SSL_ctrl` command numbers both libraries implement | `libcrypto.so.3`/`libssl.so.3` (Linux), `libcrypto.so`/`libssl.so` (OpenBSD), Homebrew `openssl@3` (macOS); `FN_OPENSSL_PREFIX` optionally names another matched pair |
| Ed25519, SHA-512 | libsodium | `crypto_sign_verify_detached`, `crypto_sign_detached`, `crypto_sign_keypair`, `crypto_hash_sha512`, width and init checks, in `host/native/crypto.lisp`, `signatures.lisp`, `peer-invite.lisp` | the system's (Linux, OpenBSD package, Homebrew) or the release's `lib/libsodium.so.23` |
| ML-DSA-65 | `lib/libfn-mldsa65`: vendored PQClean ml-dsa-65 clean (`third_party/pqclean-ml-dsa-65`, upstream commit in `UPSTREAM.txt`) behind `host/native/fn-mldsa65.c`, built by `tools/build_mldsa65.sh` | `fn_mldsa65_public_from_pem_file`, `fn_mldsa65_sign_pem_file`, `fn_mldsa65_verify`, `fn_mldsa65_generate_pem`, `fn_mldsa65_widths`, in `host/native/signatures.lisp` and `peer-invite.lisp` | `lib/` beside the image's core (`FN_MLDSA_LIBRARY` overrides) |

HST-020: A running owner takes a renewed certificate and key without a
restart. `operator CONFIG tls reload` (FNCT request kind 19, reply kind 20,
`books/tls-reload.lisp`) makes the owner build a candidate context from the
paths `run` loaded and report what the library observed: whether the chain
loaded, the key loaded, the key matches the leaf (booleans), the leaf's
notBefore and notAfter contents octets, its subjectAltName extension value,
and the host clock. ACL2 parses the times (RFC 5280 section 4.1.2.5) and
the dNSNames (section 4.2.1.6) and decides (`fn-tlsr-decide`, PRF-212): the
new pair is served exactly when both loaded, they match, the clock lies in
the validity window, the names are readable and every name the served
certificate names is still named; otherwise the refusal names the first
failing fact and the served context is untouched. An accepted pair is
swapped in under the context's lock that `SSL_new` also takes, so every
handshake after the swap uses it and a session already open keeps the
context it was created from (SSL_new holds its own reference). `status`
against a running owner prints the served names and notAfter
(`tls names=... not-after=...`, rendered by ACL2).

HST-015: No Python on the path a deployed node executes. A release runs
`bin/fn` (`/bin/sh`), which execs the frozen launcher `libexec/fn/fn-host`
(`/bin/sh`), which execs the bundled SBCL runtime on the saved core; the core
loads the three libraries above and starts another program only at the one
process site in `host/` (`fnn-workflow-ion-run-helper`: the absolute path of
an operator-named pinned ION helper, `:search nil`, reachable only from
`app-journal workflow-ion-submit`). The service files (systemd, launchd,
OpenBSD rc.d) start `PREFIX/bin/fn`. `tools/runpath_check.py` checks this
statically in `make check` and over every release before it is packed; it
cannot judge an operator-supplied helper or what the loader resolves at run
time. Python stays for clients and tests.

The digest is ACL2's (`books/blake3.lisp`; the vendored C in `lib/libfn-blake3` runs it in the images after checking it against ACL2's), RFC 8315's lock hash SHA-256 is ACL2's `books/sha256.lisp`; randomness is `/dev/urandom` in the
host and `getentropy(2)` inside the ML-DSA-65 library; neither uses OpenSSL.
ML-DSA-65 is FIPS 204 final, pure, with the empty context and hedged
signing, which is what OpenSSL 3.5's `EVP_PKEY_sign` for "ML-DSA-65" makes.
Its key files keep their encoding: the PKCS#8 private key (seed and expanded
key, as OpenSSL writes it; the seed-only and expanded-only forms are read
too, and a seed that does not regenerate its expanded key is refused) and the
SubjectPublicKeyInfo public key, recognized by exact DER layout. The
interoperation is checked, not assumed: `tests/mldsa65_interop.py` has
OpenSSL verify PQClean's signatures and PQClean verify OpenSSL's, compares
the PEMs byte for byte, and verifies every committed OpenSSL-made signed
carrier (planning/evidence/crypto-deps-2026-09-26.md).

`books/anchor-servers.lisp` owns the bounded name-to-endpoint/key mapping and
the acquisition sizes.  The common image loads `host/native/crypto.lisp`
before `host/native/anchor.lisp`; `anchor acquire` calls
`fnn-crypto-startup` in the restarted image before network use.  DNS has no
whole-path deadline; send and receive readiness each get the selected timeout.
Exit 0 follows only durable FNAN replacement, refusal is 1, uncertainty is 3,
and host/core fault is 4.

Development Python adapters remain in `run_bp_ingress.py`, `run_bp_receive.py`,
`workflow_journal.py` and `receipt_journal.py`; their presence is not a native
runtime dependency or evidence of native feature parity. The native BP carrier,
application, service and workflow paths live in `host/native/bp.lisp`,
`bp-app.lisp`, `bp-service.lisp` and `workflow.lisp`; the canonical obligation
writer is `bp-obligation.lisp`. Their composition and evidence are tracked in
[the current work record](../planning/now.md). Python `Acl2Store`, `Store` and
`Acl2Reader` remain development harnesses used by the fault/partition tests.
A Python `ReaderBridgeFault` test alone does not establish the corresponding
native Lisp condition behavior.

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

### Typed results across the native boundary

HST-019: The native owner's wrappers return typed ACL2 results the host checks once; no global result mailboxes, no LF name grammar, no frame fetched by index

A host/owner-host.lisp wrapper returns its whole result as one ACL2 value
with a guard-verified recognizer (books/owner-results.lisp): a feed step
returns a FeedPublication (its word, the peer its effect names, the sealed
frame plan as (peer . frame) pairs in append order, the completion token,
the rendered command and its status, the log line), a configuration staging
step a ConfigResult (:staged with one encoded record, or :refused with the
reason). The native host checks the recognizer once
(host/native/owner.lisp `fnn-owner-result`; a malformed value is a core
fault, exit 4), reads fields through ACL2's accessors, appends each pair's
frame to that peer's journal before it writes the command, and splits no
name list: a list of names is a list of strings. PRF-208's keystone equates
the plan with the by-index fetch it replaced. Nothing on the wire or on disk
changes. The take returns a SubmissionTaken (word, id, message-id, stored
octets, groups; the host reads those five) in place of six globals; the
submission path's FeedPublication carries the in-flight id as its token,
and that id is one of the owner's two submission ids, a connection number or
the control id `*fn-own-control-id*` (an `operator post`, a BP application
or transit submission): PRF-208's keystones say the host's check holds of
the intent's and the resolution's value for every outcome word, given that
and a codec that accepts each journal record. A recognizer checks only the
fields the host reads. The capture result carries the checkpoint
pipeline's ten fields in its order; the served step's result is the owner
scheduler's render plan (not this section's).

### The host entry guard

HST-027: The host hands an ACL2 entry only the kind of value its guard names; a payload handle where octets are meant, an octet vector where a list is meant, or the wrong argument count is refused by name before the entry runs

Typed results (HST-019) check what comes back across the boundary; this
checks what goes in. The image runs with `guard-checking-on` = `t`, but a
`:program` wrapper, and a total (`:guard t`) function beneath it, accepts
any value: a natural is a good argument to `consp` and `len`. Since the
records flip the retained article's payload is an arena HANDLE
(books/payload-kinds.lisp `fn-payload-handle-p`, disjoint from
`fn-cbor-octet-listp` octets by PRF-319's keystones), and on 2026-09-27 six
defects handed a handle, or the wrong argument count, to code that meant
octets; each surfaced as a silent refusal downstream (441 on signed POSTs,
ARTICLE 503, BP sends refused, a feed's empty command, moderation's
envelope-malformed, stored-octets 0).

`fnn-call` (host/native/io.lisp), the dispatcher every `fnn-core*` wrapper
applies, runs `fnn-entry-guard` first. It reads the entry's formals,
stobjs-in and guard from the image's world once per name (strip-world keeps
them) and evaluates, on the actual arguments, the arity and exactly the
conjuncts `(R v)` of that guard with `R` one of `*fn-entry-guard-kinds*`
(each guard-t and at most linear in the argument it reads, which the entry
consumes anyway) and `v` a non-stobj formal. A failure is
`fnn-entry-guard-fault`, a store fault (exit 4) whose message is
`host-entry-guard: ENTRY argument N (FORMAL) must be KIND (RECOGNIZER); the
host passed DESCRIPTION`, the description bounded (a natural's value, a
list's or vector's length, never contents). Any other conjunct, such as a
whole-state invariant, stays ACL2's and is never evaluated here. The kinds
are named in the entries' own guards: every host wrapper's byte-carrying
formal (`tools/harness_check.py` entry-guards, gating), and every
definition in books/ that reads a retained payload declares whether it
works in handles or in the octet model (`fn-payload-kind`,
`tools/payload_kind_check.py`, gating). The check has no waivers (lane
entry-guards-2): each consumer it found reads the arena at the handle
(control status and HDR :fn-control, reclaim's counts, the book owner's
feed reply), or is the octet model a proved function over the arena equals
(`fn-rcl-verdict`, `fn-rcl-summary`: `fn-rcl-store-counts-is-the-model-over-
alpha`), or no longer reads a payload (`fn-rcl-reclaimable`, the standing
verdict; the keyring-less opens build the empty statement index,
`fn-stx-index-of-store-without-a-keyring`), or was retired (the five pre-flip
duplicate-check twins).

### Differential evidence and measurements

`python3 -m unittest tests.test_native_served_differential` now uses the
explicit developer image and feeds one chunk
list through the image twice -- `--fn model` (one `fn-served-open` then one
`fn-served-run`, projected with `fn-served-reply-octets`) and `--fn reader`
(the diagnostic listener) -- and requires identical bytes, for a whole
transcript, three cut points, a bytewise partition, a cut inside a UTF-8
sequence, input after QUIT and a framing rejection. It is the native mirror
of `tests/test_served_differential.py`, and it is what says the thing on the
socket is the certified fold and nothing else. Recorded run (persvati,
2026-09-20, image built by `FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 sh
tools/build_native_host.sh` against the `dev-bdd59d2` gate certificates,
before the production/developer entry split:
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

### Native configuration-history observation

Native recovery observes at most `*fn-nco-max-config-observations*` physical
entries from `config/` before retaining the list.  Each observed entry must be
a regular non-symlink file whose bounded octets exactly decode as a
configuration record.  ACL2 derives the record generation, compares the
observed basename with `fn-native-admin-config-name`, orders decoded entries
by generation, and accepts only a nonempty contiguous plan from generation 1.  An
unreadable directory, excess entry, symlink/non-file, decode failure, alias,
duplicate, generation gap, or empty directory is a recovery fault retaining the on-disk
evidence; it is never treated as an absent history or a replayable prefix.

This is a configuration-namespace recovery boundary only.  It does not claim
that all existing/retry initialization paths, later durable barriers, or
platform crash persistence correspond to the ACL2 model.

## Status while the owner runs

HST-006: The operator's status, pins, obligations and peers answer while the
owner runs, in the offline words: the running owner renders the same ACL2
report (`fn-nls-report`, books/native-live-status.lisp) of the state it
carries that the offline command renders from the Store, and answering changes
no state. The running owner's report is `fn-nsc-answer-report`
(books/native-status-columns.lisp, PRF-368): its reclaim line reads each
article's tombstone flag from the catalog column the intern decided and makes
one walk for all seven figures, never realizing a payload; under the column
relation it is the offline report's function of the same state
(`fn-nsc-answer-report-is-answer-report`). The `obligations` report, whose
size grows with the retention ledger, is never rendered whole (PRF-371,
books/native-live-pages.lisp): the owner answers FNLS request frame kind 4
(kind code, VERSION, PAGE) with reply frame kind 5 (status, VERSION, PAGE,
last-page flag, at most 128 KiB of the report) one page per request, from a
cursor it keeps under the version it issued on the report's first page
(`fn-nlp-answer`). Work and allocation per request are one page, plus the
ledger's length on the first; the page and version counters wrap, so no
report length is refused. A version the owner no longer holds, or a page
other than the one its cursor stands at, is answered `version-gone` by name
and the client restarts, at most eight times, then answers uncertain. The
pages a client joins at one version are the report of the ledger the owner
held at the first page, with no hypothesis on the width, the fuel or the
owner's other cursors (`fn-nlp-pages-join-to-the-report`), and that report is
the whole report of kind `obligations` (`fn-nlp-live-report-is-the-report`);
another client's requests leave a version's cursor where it stood or drop it
(`fn-nlp-answer-keeps-other-versions`); with nothing between its requests a
client reaches the report in ceiling(L / W) requests
(`fn-nlp-pages-reach-the-report`). The whole-report exchange (frame kind 1)
refuses kind `obligations` by the name `report-is-paged`. The offline
command writes the same report a page at a time
(`fn-nlp-offline-pages-join-to-the-report`). The operator guide's
[status section](../docs/operator-internals.md#status-while-the-owner-runs) describes the
verbs.

## Operator health

HST-007: The operator's health verdict names which of ten things is wrong,
never one red bit. `operator CONFIG health` prints one line per state in a
fixed order: fenced, exhausted, unqualified-profile, space-pressure,
no-route, stranded-transfer, unavailable-peer, receipt-debt, disk (PRF-358:
the running owner's disk stalled or full, exit 28, both PROVISIONAL until
ember decides the F4 bars and the health exit; appended so 20..27 keep
their meaning; a slow disk is the `disk slow` line only, provisional per
PKT-853 (b)), checkpoint-deferred (PRF-963, PKT-542: the running owner's
automatic checkpoint publication is deferred, `reason=R estimate=E
budget=B`, so every restart until one fits is a full replay; exit 29,
appended so 20..28 keep their meaning); each line says
`held` (with the figures that hold it), `clear`, or `unobserved` (the source
was not observed: offline there is no feed table, a fenced store is not
opened). The exit code is 20 plus the index of the first held state, 19 when
none is held and some state is unobserved, and 0 when every state is clear.
One ACL2 verdict (`fn-nh-verdict`, books/native-health.lisp) decides every
line from the sources the status report reads: the headroom and profile the
`status` report prints, the retention ledger's forwarding obligations, the
configuration's BP route table, the running owner's outbound feed table, and
the host's observation of a fence (a clone fence file, a writer lock held by
a process the configured socket does not reach, or a socket that accepted and
did not answer). A writer lock held where an owner would listen and nothing
answering yet is the fence reason `starting`, and the report's first line
says so (`health exit=20 state=fenced reason=starting`); a lock with no
configured socket, or one the probe could not read, is `store-held`
(`fn-nh-fence-of-starting-iff`). `starting` is a reason of the fenced state, exit 20, never a ninth code (PKT-454), and it clears on the one observation listening changes: the host takes every observation of one invocation before ACL2 decides (`fn-nh-health-step`), which reports `starting` exactly while no clone fence is present, the lock is held, an owner would listen and nothing answered, and gives the owner's own report, with no fence, for the same lock and fence once the owner answers on its socket (`fn-nh-starting-clears-on-listening`). The running owner renders the same verdict over the state it
carries (FNLS kind 6); the exit code the host returns is read back from the
rendered octets (`fn-nh-report-exit-of-render`). The operator guide's
[health section](../docs/operator-internals.md#health-which-of-nine-things-is-wrong)
describes the verb.

HST-010: The operator's daily verbs distinguish an owner starting, a fenced
store, a stale control socket and a refusal by name, and ACL2 decides each
from the host's observations. `health` with the writer lock held where an
owner would listen, and nothing answering, says `starting`, not `store-held`
(`fn-nh-fence-of`, PKT-283). An offline `control` or `peer` verb decides its
path from two observations, the socket node at the configured control path
and the writer lock (`fn-native-control-liveness`, books/native-control.lisp;
PKT-344): a socket node with the lock free or absent was left by an owner
that died, and the verb removes it under the control-path lease, says `stale
control socket removed` and runs offline; the offline executor starts
exactly when the lock was seen free or absent
(`fn-native-control-liveness-decides`), and no socket with a held lock is
refused `store-held` without opening the store. A refusal names its reason:
`operator CONFIG post` and a live `control`, `peer` or other administrative
verb print ACL2's word for the decision's reason after the status
(`refused operator post REFUSED unknown-group`, `refused operator control
REFUSED no-such-grant`): the client asks with the reasoned FNCT request
(kind 13 for a post, 17 for an administrative vector, the payloads of kinds 1
and 3 unchanged) and the owner answers it, and only it, with reply kind 18,
the status and then the reason word (`fn-nctrl-reason-word`,
books/native-control-reason.lisp); the printed word is the reason the owner's
decision named (`fn-native-control-printed-reason-is-the-decisions`). The
kind-2 reply is unchanged, so a client that sends the plain request reads
what it always read; a new client that meets an owner predating kind 13 gets
that owner's refusal of a frame it could not decode and resends the plain
request once. PRF-172; the native cases are SCN-102. A decision that owes
the operator a sentence (a live `policy set max-transactions|max-history-
octets|max-article-octets N`: what was applied, what the next start
reserves, the use a lowering is below) is answered with reply kind 23: the
status, the reason word (the decision's class: `applied`, `recorded`,
`below-current-use`, ...) and a LINE ACL2 rendered
(`fn-lim-decision-line`; printable ASCII, spaces allowed, at most 1,024
octets), which the client prints after the status (`ACCEPTED applied limit
max-transactions=14 heap=2342 MB: served now, no data moved`); a reply with
no line is kind 18, unchanged (books/native-control-line.lisp,
`fn-native-control-printed-line-is-the-decisions`, PRF-975;
tests/test_native_limits_live.py).

HST-011: An operator reads what the owner decided about withdrawing
articles, in ACL2's words. `operator CONFIG control log` prints the count and
one line per withdrawal record the owner carries (`withdrawal target=T
cause=C principal=P scope=S generation=G`, the principal's cancel scope and
the configuration generation the record was decided under), and `control
evidence MESSAGE-ID` prints that article's decision context: whether the
owner holds it, the txid of its acceptance record, its stored verdict, the
decision its refresh made (`decision=` and the log's line for a withdrawal
record, `decision=declined reason=R`, or `decision=none` when it names no
target), and each record naming it as target with that record's effect on it
(books/control-evidence.lisp `fn-cev-report`). Both are status reports: the
running owner renders them over its committed view and pages them as FNLS
frames (request frame kind 3 carries the report kind and its argument; kinds
1 and 2 are unchanged), and with no owner the offline command renders them
over the replayed Store, deciding the records as recovery does. Under the
owner's maintained relation the evidence's decision is a record of the log
exactly when it is a withdrawal record, and its words are the log's line
(`fn-cev-evidence-decision-is-in-the-log`, `fn-cev-decision-line-is-a-log-line`).
`store ROOT retention` takes a store root, not a configuration, so it stays
offline (its shared lock refuses while an owner holds the Store); its two
figures are the ones `operator CONFIG obligations` opens with, through the
same ACL2 functions (books/retention-figures.lisp,
`fn-nls-obligations-figures-are-the-retention-figures`).
PRF-185; the native case is SCN-114.

HST-012: The owner never waits on its service log. While it serves, each
log line and diagnostic is offered to a queue: ACL2 queues it, or, once a
line is pending and the pending octets with this one would pass 1 MiB, drops
it and counts the drop (books/log-sink.lisp `fn-log-sink-offer`; a line
offered to an empty queue is always queued, so no line is too long to log).
One writer thread drains the queue with blocking writes outside every owner
lock and reports each outcome back (`fn-log-sink-take`); a failed write
counts as a drop. The relation every offered line is written, pending or
dropped, and the backlog is within the bound unless one line is pending,
holds from the writer's start and is preserved by both transitions
(`fn-log-sink-offer-preserves-okp`, `fn-log-sink-take-preserves-okp`). A
sink that stops draining (stderr on a pipe nobody reads, a stalled journald,
a slow disk) therefore costs lines, never service: before this, the writing
thread blocked under the owner mutex and the whole node, control socket
included, stopped answering. The running owner's `health` ends with
`log-sink pending=P dropped=N written=W`; the exit is the verdict's
whatever follows the eight states (`fn-nh-report-exit-of-render-and-more`).
Losing a log line loses no decision: the log is an operator's record, never
evidence of durable acceptance. Under systemd stderr is the journal, which
drains, so nothing changes there unless journald stalls. PRF-187; the native
case is SCN-116.

## Operator walk

HST-008: One installed `fn` (packaging/fn, which locates the saved image and
forwards every argument, deciding nothing) takes an operator from nothing to
a recovered node, and each verb answers every store state with a distinct,
documented outcome. On an **absent** store (none of the store's five entries
beside `[store] path`), every verb that opens a store answers `refused` with
exit 6 and ACL2's line naming `init`, never a fault (4): the decision is
`fn-native-operator-store-outcome` over the host's `lstat` observation, made
before any open (PRF-130). When an interrupted `init` or `import` left its
stage (ROOT.init-* or ROOT.import-*) beside an absent store, those verbs refuse
(1) by the stage's name instead, INTERRUPTED-INIT or INTERRUPTED-IMPORT, and
ACL2's line names the stage to remove (`fn-nsst-store-outcome`, PRF-971,
PKT-781), since `init` itself refuses while the stage remains. `init` creates the store (0), refuses an existing
one (1) and, under a mission's `fn.toml`, takes group words only: a profile
word is a usage error (5) whose line says what it accepts. On a **fenced**
store (a writer lock held with no answering owner, a clone fence) `health`
answers 20 and the offline verbs refuse (1) without opening it. On a
**running** store the status, health and administrative verbs are answered
by the owner over its control socket; offline administration refuses (1).
On a **recovered** store (after a process death) `recover` reports the
replayed history (0) and `run` serves it. Usage errors print ACL2's accepted
form before the tagged result line. An outbound peer that refuses `MODE
STREAM` (RFC 4644 section 2.3) is stopped by name for the owner's run, never
re-dialled with it. There is no store rollback (D34): a deploy is a reinstall with `store export`
and `store import` (HST-014). The operator guide's
[native component entry](../docs/operator-internals.md#native-component-entry) and
[deploy section](../docs/operator-internals.md#deploy-a-new-release-d34-fresh-deploys-no-migrations)
describe the verbs.

## HST-014: the deploy is a reinstall

HST-014: A deploy is a reinstall (D34): stop the node, `store export` when
its data must survive, remove the store, install the release (one
`libexec/fn/`, replaced whole), `init` or `store import`, start. There is no
upgrade verb, no versioned release directory and no rollback of a store.


## Process heap

HST-013: The node's heap is its store profile's figure on this machine, and a
profile the machine cannot hold is refused by name at start. SBCL fixes its
dynamic space when the process starts, so the installed `bin/fn`
(packaging/fn with `libexec/fn` beside it) first runs the same image as
`heap -- ARGV` and then execs the command with `--dynamic-space-size MB`
(through `SBCL_USER_ARGS`, which every image launcher splices after its own
figure; SBCL takes the last). ACL2 decides the figure
(books/heap-figure.lisp `fn-heap-operation-decide` over
books/heap-store-figure.lisp, host/native/heap.lisp `fnn-heap-reservation`;
re-derived from the records flip's payload arena by lane
reservation-after-flip and re-measured by lane reservation-figure,
2026-09-27): the image's dynamic content (the least of the core file's
length and the dynamic space in use when the probe starts); the store's
state at the profile's bounds -- the paged arena (the payload octets, one
page of slack and its page table: `fn-heap-arena-octets`), 48 octets of
handles and, twice for the collector, 12,288 octets per record and 320 per
group membership (the measured live state a record less its payload, 8 to 10
KB, and 0.18 KB a membership: per-record-state, catalog-columns); the
open's transient over the history on disk, which the probe observes (the
history files' octets and the transaction files' count): the open streams
one log entry and one 1 MiB chunk at a time, so one chunk and one record as
lists with their decode, the checkpoint suffix's record vectors and 1 KiB
per record, twice for the collector; the request in flight (the record and
three header copies as lists) and the two checkpoint buffers at the
profile's file bound (`fn-ock-capture-budget`);
and twice the collection trigger the host sets in the space it gets
(`fn-heap-nursery-trigger`: a sixteenth of it, at least 8 MiB, at most the
host's 64 MiB), the figure being the least space that holds all of it
(`fn-heap-with-nursery`), in MiB rounded up. The profile is the one the
command's store was saved with (`config.json`), or for `init` the profile it
will write, judged by the first run of the empty store it makes; a command
that names no existing store is given the store-less figure. The machine is
the least of the host's observations: physical memory (`sysconf`), on Linux
the cgroup's `memory.max` from the process's group up and `RLIMIT_AS`, and
`RLIMIT_DATA` (which OpenBSD's login classes set). A figure above the
machine is refused: exit 1 (outcome class `refused`), `refused
machine-cannot-hold-profile heap=MB MB machine=M MB` on stderr, and the
command does not run. An accepted figure holds every store the profile
admits with an open of the store on disk
(`fn-heap-operation-decide-holds-the-store`,
`fn-heap-decide-admits-every-store-the-profile-admits`). `status` and
`health` end with `heap=MB MB profile=WORD machine=M MB stack=KB KB
threads=N`, the reservation the launcher's probe makes for the store's next
`run` over the store on disk (books/heap-reservation.lisp
`fn-heap-status-decide`, `fn-heap-status-decide-is-the-launchers-run-reservation`). The small preset (T 16,384, H 8 MiB, R
196,608, A 32,768, G 16, K 128) reserves 908 MB of heap for the run of an
empty store on the production image and 963 MB at its bounds;
`fn-heap-small-profile-run-fits-a-small-machine`: its empty store's run
fits 1,536 MiB for any image of up to 512 MiB of dynamic content. The probe itself runs in the core's size plus 128 MB,
a bound on its work (it reads `fn.toml` and `config.json`, 16 KiB each). A
checkout's `packaging/fn` passes `FN_TEST_HEAP_MB` when set and otherwise
the image launcher's own figure; the installed launcher ignores both
`FN_TEST_HEAP_MB` and the caller's `SBCL_USER_ARGS`. The D27 default profile
(H = 1 TiB, T = 2^32 - 1 records of up to 4,096 groups) needs about 10 PiB
and is refused on every machine (PKT-582); the development and scale
presets' figures are their G = 65,535 group memberships a record (2 x T x
320 x G octets: nothing else bounds a store's memberships).
PRF-198; the native case is SCN-127.


## Served connections

HST-024: The node serves every reader and transit connection from a fixed set
of I/O loop threads, and a connection capacity the machine cannot hold beside
the store is refused by name, at start and at a live change. Lane
connection-multiplexing (2026-09-26, PKT-605; PRF-223).

The owner thread structure is unchanged: every protocol, exposure and owner
decision is a call through `fnn-owner-serialized`, one at a time. What
changed is who waits. host/native/mux.lisp runs `+fnn-mux-loops+` (2)
threads, each polling (poll(2), Linux and OpenBSD alike) the connections it
owns and a wake pipe; the accept threads hand each accepted socket to a loop
instead of starting a thread for it. A connection is a record: the input the
next step is handed (one read, or the suffix a step left; the read size is
ACL2's per step since lane input-loop-2, 2026-09-27: `fn-cbud-step-read-octets`,
books/connection-budget.lisp, installed by `fnn-owner-refresh-read-octets`
after every served step, reads 512 octets under a step rate such as the
public listener's default `exposure-steps-per-second` of 64, so the rate
keeps its meaning in octets per second, and 4 KiB without one (loopback, or
the rate row set to 0); each loop reads into one buffer of that size,
`fnn-mux-read-buffer`),
the one reply being written (the connection is neither read nor stepped
while it is queued, so a client that does not read meets TCP backpressure
and holds one reply), and its timers: the exposure wait (`fn-exp-charge`'s
milliseconds), the idle check (`fn-exp-idle` each second without input), the
send deadline (10 s), the handshake deadline (10 s) and the drain after a
graceful close (1 s). TLS never waits inside OpenSSL: SSL_accept, SSL_read
and SSL_write are single attempts answering which readiness to wait for,
with partial writes, moving write buffers and released idle buffers; at
most 8 handshakes per loop are in progress. An implicit-TLS connection meets
`fn-exp-open` before any handshake work (PKT-639), when a handshake slot is
free; until then it waits unadmitted (no handshake work, no share of the
capacity) in a queue of at most 256 per loop for at most 10 s, and past that
it is closed (`busy`, `timeout`). A refused one is closed without SSL_accept; a TLS failure is
named in the service log (`tls refused reason=... connection=N`, PKT-640).

The memory (books/connection-budget.lisp): a connection costs a heap part
(the record, its input, the one reply of the stated workload -- the
profile's largest article rendered, 2A + 1,024 octets -- and the parser's
command line, 32 octets of heap per octet of a 512-octet line) and a native part (the kernel's socket buffers; the TLS session when
a context is loaded). The base is heap-figure's figure for the store, the
core outside the dynamic space and the fixed threads (12 + the loops + the
control clients) with their stacks and 4 MiB of runtime each. The bound is
the machine less the base, divided by the per-connection figure. At `run`,
after recovery and before listen, ACL2 decides the live capacity against it
(`fn-cbud-run-decide`, host `fn-owner-connection-budget`): `connections
holds=B per-connection=K KiB` to the service log, or `refused
connections-exceed-memory capacity=C holds=B per-connection=K KiB machine=M
MB` and exit 1; when the base itself does not fit (neither the store's heap
figure nor the process's dynamic space, each with the fixed threads and the
core, is within the machine: holds=0 whatever the capacity), the line goes
on ` base-exceeds-machine heap-figure=F MB dynamic=D MB fixed=R MB`
(`fn-cbud-run-refusal-line`). A live reconfiguration whose capacity passes the bound the
run held is refused `:connections-exceed-memory` before anything is staged
(`fn-owner-reconfigure-deltas`). Trusted sources count in the capacity like
every other (the trusted range exempts a source from the per-address rule
only, PRF-211).

The articles in flight (lane zero-copy-commit, 2026-09-28; PRF-377, SCN-193).
An article's body retained mid-article, and its submission until the commit
answers it, are the per-connection terms that grow with the profile's A;
until this lane the dynamic space held none of them (they were charged to
the machine), so enough concurrent posters of large articles exhausted the
heap and the node exited 4. The store's heap figure (books/heap-store-figure.lisp)
now holds a POOL of `fn-heap-article-slots` credits, each
`fn-heap-article-reserve-octets` (2 x 16 x (512 + A + HDR): the body as
wire lists, then the injected article and its groups as lists, the
collector's copy included), the pool `fn-heap-articles-octets` = max(one,
min(32, the 64 MiB budget)) credits. A credit is taken BEFORE the body is
retained: every served read is `fn-oas-read-span`
(books/owner-article-slots.lisp, host `fn-owner-chunk-span-at`, the slots
installed by `fn-owner-connection-budget` from the store's profile), which
keeps what the owner holds (`fn-oas-held`: connections in article mode,
queued submissions, the batch in flight) within the slots across every
read: a read from an owner holding at most the slots leaves it holding at
most the slots (KEYSTONE `fn-oah-read-span-keeps-held-within-the-slots`,
books/owner-article-held.lisp), whatever the read carried -- including a
TAKETHIS (RFC 4644 section 2.5), a pipelined IHAVE or POST, or a small
article whose command and whole body arrive in one socket read, which
enters article mode and leaves it within the read with one more
submission queued; and a connection entering article mode does so within
the slots (KEYSTONE `fn-oas-read-span-admits-within-the-slots`). A read
that would take the owner past the slots and past what it held is refused
in three tiers, the first the slots hold: a POST is answered `440 posting
not permitted now; the articles in flight fill the memory, try again later`
at the command (RFC 3977 section 6.3.1: no article is sent); else an article
the read entered is dropped with its wire closed and `400 the articles in
flight fill the memory; try again later` and close (RFC 3977 section
3.2.1), what the read completed before it kept; else the whole read is
refused, 400 and close, nothing it carried taken (a TAKETHIS in one read:
RFC 4644 offers it no "later"). A read of one connection leaves every other
connection's record, and so its wire mode, as it was (KEYSTONE
`fn-oah-read-span-leaves-the-others-article-mode`). The credit moves with
the request: held in article mode, then in the owner's queue, then in the
batch in flight, and released when the commit answers; a client that
disconnects mid-article drops its wire (nothing else owns it), a queued
submission stays counted. The completion policy is RESERVE-TO-FINISH: a
credit is the whole article's worst case (past the body limit the wire
closes with 441), so an admitted connection's reads that complete or
continue its article are the reads before the slots exactly (KEYSTONE
`fn-oas-read-span-never-blocks-an-admitted-article`), and past the slots
only an article such a read began after completing its own is closed
(`fn-oah-admitted-read-keeps-what-it-completed`); partial uploads cannot
hold the pool while each needs more of it; a stalled upload holds its
credit until the idle timeout closes its connection. The launcher's former
room (connection-budget's launch figure, 1,024 connections' heap parts, no
caller since lane reservation-figure) is gone. Not yet: the body in bounded
pooled chunks (one octet a byte) instead of wire lists, which lowers the
credit about 32-fold; the queue's growth by the control channel and BP
deliveries (no connection's read).

Memory credits (lane credits, B5, 2026-09-28; PRF-380, SCN-194). The
article slots are now one instance of the credit ledger
(books/memory-credits.lisp): the run's ledger (`fn-owner-credits`, installed
by `fn-owner-connection-budget` as `fn-mca-initial`) has the launcher's heap
figure as its budget, the figure's fixed terms as its base, the open's terms
as a completion reserve that nothing is admitted against, the collector's room
as the runtime reserve, and exactly the articles' pool free
(`fn-mca-initial-funds-exactly-the-articles`). Every served read is
`fn-mca-read-span` (books/owner-credits.lisp) over `fn-oas-read-span`: the
connection's credit becomes one reserve while it is mid-article plus one per
queued submission of it; growth past the budget is refused by name (the
memory 440 at a POST command, else `400 the articles in flight fill the
memory; try again later` and close, the read not run) and shrinking or
holding steady never is (reserve to finish). The credit then follows the
buffer: the committer's take moves it to `:open`, the batch's append to
`:sealed`, and only the batch's COMPLETE, after its barrier returned,
releases it. A close, an idle timeout, a stall's uncertain answer or a fault
releases the connection's own body and queue only
(`fn-mca-close-keeps-what-the-commit-owns`): the pipeline feeds each member's
outcome before the barrier, so the owner's queue and in-flight field are empty
while the syncer's fdatasync still owns the batch. No cache is charged yet: a
committed article is held by the base's state term at the profile's bounds.

Not claimed: a reply larger than the stated workload's (an OVER or LISTGROUP
over a large range) is outside the figure until replies are rendered in
windows (lane owner-scheduler's plans; PKT-644); the measured constants
(record, kernel, TLS) are measurements pinned by tests/test_native_mux.py,
not theorems.

### Operator commands and owner critical sections

Lane operations, 2026-09-28 (planning/evidence/operations-2026-09-28.md).

HST-032: An operator command carries any number of words of any length (PKT-867, PRF-902). ACL2 parses the argv the kernel admits in one pass in constant stack (loop twins), the administrative vector travels in the record codec, and what bounds one command is the control frame the owner reads under the profile's bound; KEYSTONE `fn-native-control-admin-decode-of-encode`: an argv the client can seal is the argv the owner decodes.

HST-033: The owner holds its mutex for no disk I/O at a connection's greeting or a checkpoint's capture (PRF-907). The free-space observation (statvfs) is taken before the gate admits a quantum, at the NEED ACL2 computed under the mutex; the log rotation's spare is staged, preallocated and fenced off the mutex, the switch under it is one rename, and `journal/` is fenced off it before anything in the new segment is acknowledged or named (KEYSTONE `fn-lgrs-journal-fence-names-the-acknowledged-batch`).

HST-036: Maintenance while serving (row S3, PRF-964, PRF-965). `recover` and `store inspect` on a running owner are answered by that owner over the same administrative route as HST-034 (ACL2's liveness decision over the socket and the writer lock, books/owner-maintenance-request.lisp `fn-omr-route`): `recover` is accepted by name (the owner's open recovered the store; its status follows), `store inspect ID` is the owner's own lookup answered as a word that the client renders as the offline report (KEYSTONE `fn-omr-inspect-live-is-the-offline-report`); an owner that holds the lock and answers nothing refuses by name (`owner-holds-the-store`) with what it would take; the offline executors run only when no owner holds the store. `status` and `health` on a stopped store read the newest checkpoint's 37-octet header and the journal's sizes, never a replay: `stopped checkpoint=N journal-octets=B transactions-at-most=M` (KEYSTONE `fn-omr-transactions-at-most-bounds-the-count`); `status --replay` is the report over the replayed log.

HST-034: Compaction needs no stop (PKT-868, PRF-908). `store compact` and `store checkpoint` on a running owner are a request it answers by name (requested, coalesced, nothing-to-compact, refused while a deferral blocks) and serves with its own publication in bounded batches off its mutex; KEYSTONE `fn-ock-requested-next-is-due-with-a-suffix`.

HST-035: The operator lists, inspects, pauses, resumes and drops the BP carry obligations (PKT-869, PRF-914) with `operator CONFIG carry JOURNAL ...`; each control is a durable record of the carry journal (domain `:carry`, frame FNCC) ACL2 decides, and a paused or dropped work's request is refused by name before anything is written (KEYSTONE `fn-bpcc-gate-refuses-a-held-work`). A drop keeps the Store pin: only the receipt's evidence releases it, or the operator's waiver, `carry JOURNAL drop WORK --abandon REASON` (PRF-950): a `:waive` record of the carry journal (the principal, ACL2's rendering of the effective uid, and the reason) decided only while the pin stands (`reason=not-held` otherwise), made durable before the Store retention event it authors, which is the receipt's own event (the pin's id, subject and evidence; `fnn-owner-retention-commit`), so retention has one release path. A waiver durable without its Store event (a process death between the two) is completed at the next writable owner open; once the pin is gone ACL2 authors no second event, and a later receipt for the work is refused (`carry-waived`) (KEYSTONE `fn-bpcw-waiver-releases-exactly-once`; `fn-bpcw-only-a-waiver-waives`).


### Offline snapshot blessing

HST-039 (S7a, local fn policy): `operator CONFIG store bless-snapshot DIR`
(or `store ROOT bless-snapshot DIR`) validates the named copy read-only.
It requires a regular `DIR/SNAPSHOT` completion marker before opening the
copy. ACL2 `fn-osn-bless-open-needed` omits the open when the marker is
absent; `fn-osn-bless-word` selects the first failing observation:
`snapshot-incomplete`, `open-refused` with the open's own refusal sentence,
or `no-node-secret`. The copy's open checks its own checkpoint/log lineage,
and the existing node-secret reader checks the key file's regularity,
permissions and ACL2-decoded format. The configured source store is never
opened by this action. Accepted output is `blessed snapshot=DIR
transactions=N`; the exit code follows ACL2's status. PRF-1050 states the
three-observation blessing predicate, with teeth in
`tests/acl2/owner-snapshot-request-tests.lisp`; SCN-217 exercises the host.

The marker is the producer's completion observation, not authentication of
a snapshot producer or proof of atomic capture. Its fields are provenance.
A complete older copy may open; blessing does not determine freshness or
prevent local number reuse on restoration. S7's running snapshot producer
remains unfinished: bounded file-set ownership across replacement/unlink,
its committed frontier and concurrent key/configuration changes, and its
marker-last durability program need their own implementation and evidence.
SCN-217 uses stopped copies with explicitly supplied completion-observation
fixtures; it establishes no running-capture guarantee.


### Snapshot producer

HST-040 (S7, planned): the running or stopped producer captures one committed
Store frontier, its configuration history, genesis identity, retained identity
snapshots/verdicts and keyring generation. A restore must recover the retained
article/conflict/provenance, configuration, identity, consumer obligation,
topic, resource and history state at that frontier. Transient connections,
recovery barriers and process-local descriptors are not copied state.

The chosen implementation reconstructs a complete state checkpoint from an
O(1) owner capture and protected arena generation, with a captured empty suffix
segment after the normal rotation. The producer writes outside the owner mutex
in bounded batches. It copies immutable configuration records only through the
captured epoch; node-secret file mutations require the same exclusive writer
lease and therefore cannot overlap a running capture. Shared publication
scratch and reclaim must be excluded throughout the producer lifetime. Pinned
old artifacts and new resident/disk/fd/worker demands must be funded by the
supported resource profile before work; exhausting a quantum resumes rather
than truncates a store.

PRF-1068 is the required maintained-live-projection to target-recovery
correspondence. PRF-992's checkpoint-open theorem alone is insufficient: its
captured-history-open premise must be derived, including independent identity,
consumer and topic prefixes, and actual post-replay keyring installation.
PRF-1069 scopes the host-called file-copy cursor to exact captured prefix
coverage and bounded I/O; source version ownership and durability are separate.
The completion marker is published last only after all target data is durable;
ambiguous rename/fence failures stay uncertain and preserve recovery evidence.
SCN-215 is reserved for actual producer output and subsequent complete restore
checks. The offline checker SCN-217's artificial observation fixtures establish
none of these producer guarantees.

The S7 producer under development builds a private sibling staging tree.
Its completion tail is ACL2's `fn-osd-seal-program`: write and fence
`SNAPSHOT` after every captured data file is fenced, fence staging/config/
journal/keys names and the staged root, publish by no-replace rename, and
fence the parent. The logical full program is the existing arbitrary-tree
import publication program with `SNAPSHOT` last. An error once rename may
have been issued yields **uncertain**, including failure of the parent
fence; status must preserve that outcome. The copied target is absent
until publication. A stage left behind is named in the diagnostic and is
not evidence of a completed target.

This component is implemented source, not an enabled producer. Its
streamed checkpoint prelude must refine the full byte program; the
capture must preserve the actual Store statement keyring, retained
verdict/provenance and independent identity/consumer/topic projections;
and a funded maintenance resource profile must cover old pinned artifacts
and the new tree simultaneously. The existing checkpoint disk estimate
does not bound Lisp summary conses, history-image scratch or its host hash
index. None of marker presence, an ARTICLE-positive reopen or the generic
crash theorem closes those pending obligations.

The pending running capture adapter `fn-owner-osn-capture` returns the actual
immutable Store pointer, profile, genesis and installed owner node secret
under the owner mutex, alongside a fresh process-local ticket and the
Store's carried committed record count. It acquires the existing shared
publication slot only when no snapshot, checkpoint or reclaim occupies
it. The caller must pin the arena before leaving that mutex. Configuration
history and Store statement keyring/generation belong to the captured Store,
not later globals. The owner node secret is a separate captured field.
`fn-owner-osn-release` clears exactly that snapshot ticket and shared count;
it never updates the source checkpoint base, attempted/durable counts or
its deferred verdict. A stale callback cannot clear a newer capture at the
same frontier. Source file versions and maintenance resource reservations
still need their own actual lifetime/refinement, so the adapter is not yet
wired to a running request.

The first resumable preparer component is
`fnn-snapshot-prepare-configured-fold`, driven by guard-verified ACL2
`fn-osp-cpr-tick`. The continuation carries the unconsumed config and event
lists by pointer and yields after each input transition. It preserves the
original paused checkpoint fold, including the configuration records after
the last event staying unconsumed, every refusal, and its position.
One-input progress is not a byte-cost bound of the inner configuration or
event operation. The remaining summary folds, canonical-row preparation,
history-image build/commit and write-map construction must have their own
resumable funded phases before the producer uses this component.

The second summary component `fnn-snapshot-prepare-summary-folds` carries
identity, consumer, topic and event-index accumulators independently and
advances one event per tick. It does not append a growing record prefix on
each tick. Its refinement requires a valid captured event list and a
normalized consumer result; those must come from maintained capture
relations, never a served whole-history validation. Full image/commit and
canonical-row preparation remain pending. The inherited event-index codec
addresses only its existing unsigned-32 sequence range; this component
copies that format behavior and does not qualify larger operator profiles.

The S7 canonical preparation component `fn-osp-canon-tick` retains the
existing canonical writer's exact row continuation through two phases:
one captured row per canonicalization tick, then one list cell per reversal
tick. Its host helper yields between ticks and requires the captured arena
lease for the entire read. Real interned article rows with an orphan payload
witness the changed canonical handles. This is row-transition progress;
inner row conversion still requires a supported allocation/work bound, and
the actual controller, page/hash preparation and funded lifetime remain open.

The snapshot checkpoint reconstruction component now assembles those
completed cursor values through `fn-osp-assemble`, preserving the original
checkpoint tuple at the named definition boundary. It no longer calls the
whole-history `fn-owner-sco-next` to recompute them. Arena lengths/segment
setup, history-image page commit and writer hash preparation still need
resumable/funded composition. Restored canonical handles differ from the
captured source handles; the final recovery guarantee must compose the
existing arena writer/load alpha refinements with the captured-view inverse.

PRF-1081 replaces S7's old canonical re-interning component with the
snapshot-specific `fn-orm-tick`. It changes only held payload handles,
retaining frozen facts, context/verdict generation, local numbers,
withdrawal, evidence and every other retained field; a composite keeps its
original statement and remaps its held article separately. Its dispatcher
examines at most fifteen outer cells, and its tick guard inspects only the
fixed-position natural handle. The valid captured suffix is a maintained
proof invariant and is never revalidated per tick. Preparation advances
one row or one reversal cell without reading payload bytes.

The complete retained-row abstraction `fn-orm-retained-alpha` includes
the composite-held payload as well as metadata. Equal original statement
bytes alone do not establish that held-payload correspondence. The physical
arena writer/load must supply the source-to-target payload map for both
ordinary and composite-held rows before the inverse becomes a full restore
claim. SCN-215 names the genuine producer/restore/cut scenario; current
orphan/remap teeth are component evidence only. History/page preparation,
funded capture/controller and matching native execution remain pending.

Snapshot capture admission calls `fn-osl-ready-acquire` (PRF-1074) on the
carried `fn-sf-phase` field. A phase other than `:ready` refuses before changing
the snapshot ticket, lease or shared checkpoint slot. This retains the actual
committed source semantics required by the recovery inverse; it never scans
`fn-osr-retainedp` or another whole-history predicate. Resource admission still
precedes this capture and remains a separate producer obligation.

The captured source cursor (`fn-osrc-begin/tick`, PRF-1099) borrows
`fn-sf-records-field` rather than materializing `fn-sf-records`. It restores
snoc suffix order one cell per tick, requests each based row from the separate
incremental decoder, and emits `(:resident row)` or `(:decoded node)`. Each
decoder completion binds the captured scalar frontier, two-cell capture lease
and ordinal. A stale completion refuses without advancing the cursor. The
physical source pin survives every census/column pass and cleanup. Reversal
conses are additional funded source scratch. Once the bounded preparation
finishes, `fn-osrc-restart` reuses its immutable ordered suffix pointer in
constant work for further passes; a premature restart refuses. Provider row correctness and
complete source refinement remain required before producer completion.
