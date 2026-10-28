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

# H4

`fn2/tests/surface/` partitions the 120 inventoried obligations across nine
families, with one shared target gate, hook factory and isolated native runner.
The manifest preserves §1 row links, §2.2 forms (including explicit dashes),
simulator schedules, fixture paths, performance rows and §2.5 cadence. Counts
include rewrite-row obligations; no native is duplicated between families.

The default fn2 target skips every selected test with the fixed prefix
`layer D/E not yet serving`, followed by the relevant `node.Fn2Backend`
requirement. fn1 runs the carried examples and a Hypothesis NNTP state machine
against H2's model; the latter's current scope is empty-group reader/cursor
sequences and reconnects. Wider seeded wire comparison uses H2b solely through
`python3 -m fn2.tests.model.differential` and its public CLI. Other models, full
fixture replay, D2 grammar generation, convergence and load drivers remain named
hooks/skips, never passing placeholders. Consumer/durable history hooks consume
H3b observations and retain unmapped reasons.

Laptops select E/S/F/H at 200 model examples; hbox adds performance rows and uses
5,000 examples. Each uses 50 steps. Fuzz drivers share one serial wall budget
(600 seconds / 3,600 seconds); H5 still owes CPU allocation inside the 30
CPU-minute envelope. `surface.json` and one Markdown table per family publish
selection, outcomes, skips and assertion calls beside the profile. Performance
values appear under `published, not a gate` and are never threshold assertions.
Missing drivers and fn2's lack of service produce skips; failures/errors alone
make the exit nonzero. The parent and child drivers own exclusive PID files.

`run_natives --env-plan IMAGES` invokes `native_env.py plan --allow-skips` once
for the selected modules. Its selection-sized planning timeout is separate from
the per-module native timeout. The parser uses `shlex`, expands only `$T`,
`$FN_TEST_OPENSSL_BIN` and `$FN_FIXTURES_DIR`, and never evaluates shell code.
Each child gets its own plan assignments; other modules' managed image/fixed
assignments are removed. Parent manual opt-ins remain available. Absent tool
substitutions expand to empty, so real pre-node tool failures stay visible.

For fn1, `--identity IMAGE --source SHA` reads native_env's exports and requires
all four identity values. For fn2, planning also supplies all four automatically:
all are `fn2-host-absent` while FN2_HOST is absent. A present single fn2 executable
supplies its SHA-256 for launcher/core/runtime identities (there is no SBCL core
or runtime); source uses the explicitly supplied SHA or that executable digest.
This is stub provisioning, not an assertion of fn1 image equivalence. Image
assignments point to FN2_HOST, defaulting to `fn2/host/fn`. Native modules that
check a real core, permissions, identity equality, installed packaging, OpenSSL
or fixtures before constructing Node still fail/skip at those checks. No script
or cryptographic tool is intercepted. The existing raw-SBCL guard is unchanged.

H4's laptop evidence is in `build/REPORT-H4.md`. This session's sandbox denies
loopback binds, so the complete harness command and native sweep cannot qualify
the socket paths here. The new provisioning controls and fn2 empty surface run
are executable without that privilege; fn1 service verification remains the
seat's hbox work. No image was built, no SBCL was started, and H4 does not change
H2b's files or Git's index.


## H4b

The fn2 sweep now provisions `build/fn2-host-placeholder/fn` whenever `FN2_HOST`
(default `fn2/host/fn`) does not exist. Creation is idempotent, including file
mtimes and executable permissions. Every child receives the resolved `FN2_HOST`
and all native image aliases, including reference/profiling aliases. Functional
opt-ins and the slow peer-row functional witness are enabled; measurement flags
remain explicit opt-ins. An unset OpenSSL tool path resolves through PATH.

The POSIX shell launcher delegates to an inert shell runtime, prints
`fn2 layer D not yet serving: fn <argv>` on stderr and exits `EXIT.REFUSED` (1),
fn1's known-refusal class from `tools/outcome_codes.py`. There is no separate
service-unavailable exit class; `NOT_CONNECTED` describes a transport attempt.
Core, world-deps, library and runtime-home files carry placeholder headers;
`image.sha256` records their actual bytes. The launcher's `--core` / inert
`--eval placeholder` fields let packaging readers inspect it; no Lisp executes.
`native_env.image_identity()` computes launcher/core/runtime hashes, with the
same actual launcher/core hashes exported under developer identity names.
The source label is `fn2-host-placeholder`, not a certification or source commit.
A supplied real host is preserved. Node, run, start and start_filed retain their
named NodeDead stub behavior; direct execution gets the shell refusal instead.

`named-placeholder` records a refusal found in full exception text, PIPE stderr,
or inherited stderr captured for that test/fixture. Original outcomes and first
exception lines are retained. Capturing never changes a subprocess result and
resets evidence between tests and fixtures. Successful assertions remain `ok`.
The explicit `intended-skips.json` table matches literal reason prefixes only for
its listed modules: measurement opt-ins (R measurements are published, not gated),
Linux prerequisites, external fixtures, and the live public-node opt-in.
Linux entries apply only off Linux. The checkpoint reasons mention an image,
but their decorators also require Linux; the image and functional opt-in are
provided, leaving only that platform predicate. Unlisted skips remain `other`.
Inventory retirement is reported separately from these categories.

This supersedes H4's absent-host digest sentinels and empty OpenSSL substitution.
The exact laptop sweep, counts, remaining non-adapter prerequisites and first
failure line for every `other` test are recorded in `build/REPORT-H4b.md`.
A placeholder is not a production-profile image or a published-source manifest;
those semantic checks remain observable. The raw-SBCL guard is unchanged.
