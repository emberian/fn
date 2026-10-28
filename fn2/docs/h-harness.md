- The fn1 node runs on hbox, not the laptop. The laptop has no fn1 image and building one certifies the ~1,440-book closure (hours; the common brief puts anything over minutes on hbox). hbox holds the published image set /tank/fn/images/keyed/c14e9e8e29ef4e34765271d69885970751f516ba317e583774b9bb9d261a40c4 (TREE_SHA d377d4559, one commit below origin/dev 6521f18c4; the only differences are tools/hbox_native.sh and tools/test_budget.py, no node code). Codex writes and unit-tests on the laptop; the seat runs every fn1 verification on hbox under swarm-build with PID files.
- The natives are not edited. They run through an import shim that replaces `tests.native_harness`; the adapter's fn1 backend is fn1's own Node, so a green fn1 run through the shim is evidence the adapter preserves behaviour, and the fn2 backend is the stub whose named failures are the list of what layer D owes.
- fn1 key `[resources] cold_*`/`output_*` -> fn2 `[profile]` (RELEASE-PLAN §1, the accepted key set): replaced by name, old names refused by name.

# H1b: the Node adapter and isolated runner

The adapter implements the seven inventory operations and preserves the remaining
fn1 Node methods. `Fn1Backend` subclasses the separately loaded
`fn1_native_harness.Node`. `Fn2Backend` inherits its exact constructor and scratch
fixture behavior, translates the configuration table name, and raises the original
`NodeDead` at every node execution entry. It does not launch an echo host or claim
NNTP liveness. This is the seat's specified stub, not layer D's implementation.

`NodeInterface` is a structural Protocol. Its counts are module unions across all
120 inventory entries: start 120, stop 120, config 119, socket 110, control 120,
kill_at 49, observe 120. `socket` returns the node's port/tls_port/session interface;
`control` remains the original path so existing CLI calls stay unchanged.
`kill_at` forwards the control-fault selector plus any death_cut options in fn1.
The inherited returned process remains the object that existing death-cut helpers
inspect; the adapter does not fabricate a new died_at implementation.

## Imports and host selection

`shim.install()` writes both `sys.modules['tests.native_harness']` and the package
attribute before any native import. Public fn1 names are copied; missing private
names are forwarded with module `__getattr__`, because `compress` explicitly imports
`_line_containing` and harness controls use private state. The fn1 module itself is
never patched. `Node.session()` uses the shim's Client subclass so observation also
covers clients created through a Node.

Under fn2, `native_image` resolves every image variable to `FN2_HOST`, defaulting to
`fn2/host/fn` under the repository root. Only that path is treated as executable by
the shim's `executable` and `requires`. `slow` is unchanged. The lower-level shim
`run`, `start`, and `start_filed` also name missing execution requirements when
called with this host path. `installed_launcher` returns the fn2 host path directly;
fn2 must not construct an SBCL core layout or run fn1's heap probe.

Direct module checks of `os.access`, `Path.is_file`, environment opt-ins, source/core
hashes, external tools and fixture availability are untouched. Direct subprocess
calls and imported fixture tools are not intercepted to manufacture a NodeDead.
Their remaining skips and errors are reported. This means the requested universal
named-failure acceptance is not reached by the unchanged modules on this laptop.

## Configuration and remaining host requirements

`node.CONFIG_KEYS` explicitly covers the JSON inventory's config-key union. All
known non-resource keys are kept. `dynamic` is an unresolved inventory expression,
not an accepted configuration key. Every inventoried `resources.*` entry moves to
the same leaf name under `profile`, including `reclaim_live`; retaining a one-key
old resource table would otherwise leak the old layout into this fixture.
This mapping only writes fixture names. Layer D/E still owes the profile semantics
and refusal of old resource names. The stub cannot establish either behavior.
Extra/TLS/protected-only text follows the original writer; the resource section
header is translated in appended fixture text as well as `cold_resources`.

The module docstring is generated at import from the top 40 aggregate host
requirements, sorted by descending module count and then kind/value. Print it with
`python3 -m fn2.tests.harness.node --requirements`. These are fn1 dependency names;
they do not authorize carrying obsolete verbs, cuts or representations forward.
The stub still reexports fn1's EXIT and reply helpers. It neither invents a fn2
outcome table nor claims to implement the host's future source dependencies.

## Measurements and process containment

`FN2_OBSERVE_DIR` enables JSONL records per test ID with monotonic nanoseconds,
kind, phase and operation fields. Clients retain the original constructor and
protocol. Command octets (before the harness adds CRLF), line replies and block
bytes are hex; node snapshots include retained stdout/stderr and the actual argv,
pid and exit class. Before a launch, the record has the proposed image argv and
null pid; after a successful launch it has the actual installed-launcher argv.
CLI captures keep the first 4 KiB per stream. Nonzero exits use fail; exceptions
and timeouts use info because completion is unknown. Default observation performs
no capture, serialization or filesystem work. Fixture events outside a running
test use the original stack-based test ID, or `fixture` when none exists.

Each module runs in a fresh session/process group. Its PID is written beside its
JSON and log. A timeout sends SIGKILL only to that child's recorded group and reaps
the child; no process pattern is used. Child PID files are claimed before spawning, so an existing file cannot leave an untracked child. The optional parent PID file is exclusive
and removed at exit. `--one` is the subprocess entry, also usable for local module
controls. `--modules` accepts inventory short names; `--verdict` intersects the
selection; omitting a selection defaults to all inventory modules.

The result records every collected test, its outcome, first exception line, skip
reason, elapsed duration, and calls to TestCase assert*/fail* methods. Delegating
assertion methods count each call; Python assert statements and custom helpers
that never call TestCase are outside this metric. Methods are restored after the
run. `failureException` is a class, not an assertion method, and is never wrapped.
Class/module setup failures are attributed to every blocked test with zero test
assertions; the original fixture event is retained separately. Fixture assertion
calls count once in the module total and `fixture_assertions`, never once per
blocked test. Subtest and cleanup failures preserve additional diagnostics.

Retired in-image/internal-only methods are removed from the active suite before
class setup, then reported as explicit intended skips with the inventory verdict
and reason. Mixed methods remain active. Inventory names not collected are not
fabricated as tests (some name nested controls or inherited helper definitions).
Every fn2 non-ok test is classified by its exception prefix as named-node-dead or
other; intended skips remain in the other count and are also counted separately.
The printed other list excludes intended retirements. `all ok` in the module table
means no failure/error, and can therefore include modules with only skips; test
outcomes and skip counts are the acceptance evidence.

The H1b laptop instruction forbids starting SBCL. A child-only audit hook under
fn2 rejects direct SBCL subprocess exec with an explicit error. This was added
after the initial discovery sweep accidentally ran tls_transport's four raw
component tests; those processes ended. The corrected acceptance lists the four
blocked tests, does not call them retired, and does not claim fn2 coverage from
their initial results. This guard does not alter the fn1 backend or constitute a
general subprocess sandbox.

Real fn1 verification remains the seat's hbox task. The laptop dry control checks
only that web/auth produce the identical 23 image-absent skips and reasons through
the shim and directly. Full acceptance output, residual cases and the safety
incident are recorded in `build/REPORT.md`.
