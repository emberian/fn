- The fn1 node runs on hbox, not the laptop. The laptop has no fn1 image and building one certifies the ~1,440-book closure (hours; the common brief puts anything over minutes on hbox). hbox holds the published image set /tank/fn/images/keyed/c14e9e8e29ef4e34765271d69885970751f516ba317e583774b9bb9d261a40c4 (TREE_SHA d377d4559, one commit below origin/dev 6521f18c4; the only differences are tools/hbox_native.sh and tools/test_budget.py, no node code). Codex writes and unit-tests on the laptop; the seat runs every fn1 verification on hbox under swarm-build with PID files.
- The natives are not edited. They run against the real `tests.native_harness` module, on which `shim.install(backend)` sets the declared patch points (HR); the adapter's fn1 backend is fn1's own Node, so a green fn1 run through the shim is evidence the adapter preserves behaviour, and the fn2 backend is the stub whose named failures are the list of what layer D owes.
- fn1 key `[resources] cold_*`/`output_*` -> fn2 `[profile]` (RELEASE-PLAN §1, the accepted key set): replaced by name, old names refused by name.

# H1b: the Node adapter and isolated runner

The adapter implements the seven inventory operations and preserves the remaining
fn1 Node methods. `Fn1Backend` subclasses `tests.native_harness.Node` as captured
at import (`node.ORIGINAL_NODE`). `Fn2Backend` inherits its exact constructor and scratch
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

There is one module: `tests.native_harness`, imported normally. `shim.PATCH_POINTS`
declares every name the adapter replaces on it, per backend (fn1: `Node`, `Client`;
fn2: those plus `native_image`, `executable`, `requires`, `run`, `start`,
`start_filed`, `installed_launcher`). `shim.install(backend)` sets them and
`shim.uninstall()` restores exactly the values present before; importing `shim`
changes nothing, and every runner installs before collecting a module and
uninstalls in `finally`. Because natives and helpers see the same module object,
`mock.patch` on any name reaches both, and fn1's own `Node.session()` builds the
installed `Client`, so observation covers clients created through a Node.

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
Skip is not pass (HR): a failure/error, or a served family that executed nothing,
exits 1; otherwise any selected test skipped for a reason other than an inventoried
retirement or an `intended-skips.json` entry exits 3 (NOT RUN, with counts and
reasons). `families.json` `serves` names what each target serves (fn1 all nine,
fn2 none until layer D declares them). S forms without a model are `owed`: listed
in every report as OWED, generating no test. Each family package has one
`load_tests` hook; reports count pass/fail per form beside the TestCase-call count. The parent and child drivers own exclusive PID files.

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

## H1c (superseded by HR)

H1c made a two-module shim transparent to module-level patching. HR removed the
second module (see "Imports and host selection"), which makes transparency a
property of the design rather than of forwarding code; the three H1c lifecycle
scenarios stay in `test_harness` as controls, run directly and through the adapter.

## Inventory data (HR)

The reviewed judgments are data: one JSON record per module under
`fn2/tests/harness/judgments/`, validated against `judgments.schema.json`.
`natives-inventory.json` and `natives.md` are build outputs under `build/natives/`
(`python3 -m fn2.tests.harness.inventory --out build/natives`; `inventory.load()`
regenerates them when an input's digest changes). The migration was checked byte
for byte against the last committed copies before they were removed.


## Open spec ambiguities handed to layer D (HS; recommendations, not rulings)

The H2d differential leaves three precedence questions the specs do not settle.
Astra's recommendation, which the seat endorses, beside the alternative; layer D
decides when it writes the command grammar, and the model follows that decision.

- **A13** (114 rows; malformed unknown keyword, fn1 answers 501): a token that
  fails RFC 3977 §9.8's keyword grammar gets 501, a well-formed unrecognised
  keyword 500; neither mutates. Alternative: 500 for every unrecognised token
  after framing (simpler dispatch, conflates malformed with unsupported).
- **A15** (6 rows; malformed UTF-8 TAKETHIS on a reader connection, fn1 502):
  framing and UTF-8 validation precede authorisation, so malformed arguments get
  501 and a well-formed transit command on a reader connection 502. Alternative:
  recognise the verb, refuse transit 502 before parsing arguments (bounds
  forbidden work, hides argument validation).
- **A16** (3 rows; empty Path plus an unnamed header): malformed header framing
  takes precedence and gets the generic syntax refusal; a structurally valid block
  with a bad Path gets the named Path refusal. Alternative: the named Path refusal
  whenever Path is recognisable (better diagnostics, needs a parse-past-defect
  policy and an order among named defects).
- **A14** (15 rows; malformed TAKETHIS answered by silence) is evidence, not
  precedence: `differential --takethis-probe` now records whether the server was
  awaiting the article body.

## HZ: the operator and store_ops S forms (live on fn1)

Both forms pass live against fn1 at the laptop cadence (hbox, image c14e9e8e,
TREE_SHA d377d4559): operator 5 examples in 173 s, store_ops 5 in 46 s. Before
the live runs the seat ran each family's fixed witnesses through a recording
probe (`build/coordinator/fn2/lanes/h-quests/witprobe2.py`; replies kept as
`wp2-operator.json`, 62 CLI calls, and `wp2-store_ops.json`, 42 calls) and
fixed what it found.

- **Reply shape.** A CLI reply is checked by its exit and, when the verb prints
  one, the tagged result line `WORD operator SUBJECT [REASON]` whose WORD names
  that exit (docs/operator.md:1232-1242; fn1 renders it in
  host/native/operator.lisp `fnn-operator-emit-status`, after any unterminated
  `Password:` prompt). A refusal's reason is a tag: the one `reason=X` key, else
  the tagged line's REASON (`(ADMINISTRATION X)` or the echoed `REFUSED X`), else
  a report line `refused X` (`operator_model.reason_word`). The first cut matched
  the expected word anywhere in the reply, and fn1's usage text (which names
  `refused while an owner runs`) satisfied or broke it by accident.
- **Tags where the docs name only the class.** The models carry fn1's observed
  tags: ARGV-MALFORMED, SYNTAX (a capacity that is not a u32 decimal; a malformed
  group name), ACCESS-PATTERN (a malformed wildmat), all usage 5;
  UNEXPECTED-ARGUMENTS (status, recover) and INVALID-STORE-COMMAND (`store`
  sub-verbs) for extra words. The draft's provisional exit-1 words for these were
  wrong. Tags no witness reaches stay provisional and are listed in each model's
  SPEC-MAP.
- **`moderation list` of an unmoderated or absent group** is accepted with
  `moderation group=G moderated=no` (the spec names no refusal; the draft
  invented `no-such-group`).
- **Import through the operator form.** `fn store S import ... --FIELD N`
  ignores the override; `operator CONFIG store import` (the documented form,
  docs/install.md:340-352) honours it. The target imports into the configured
  path and restores the owner's path after. The draft's lowered-field refusal
  witness (`max-history-octets` below the record bound) was cut: the docs say
  only "with any field raised" and fn1 accepts the lowered one.
- **O01, fn1-bug (the operator ADJUDICATIONS' one row, an effect row).** `group
  retire` is accepted and retires the group in the configuration (`group create`
  is then accepted and restores its description), but the reader wire keeps
  serving it: LIST ACTIVE lists it and GROUP answers 211, at once, after 3 s and
  after a restart; LIST NEWSGROUPS shows `(no description)`. docs/operator.md
  says retire stops serving the group. An effect row makes the model follow the
  recorded effect for fn1 only, so every later wire read checks it; the fake and
  fn2 get the documented retirement (the `retire-visible` mutation control still
  fails), and a fixed fn1 fails the next observation, so a stale row cannot hide.

## HZ3: the web S form (live on fn1)

The web face is checked as a translator of the one NNTP model (WEB-003/005: it decides nothing). A
browser session is an NntpModel connection opened by the sign-in's AUTHINFO; it pins its view and
listing and re-pins where the face selects a group (a group or article page, GROUP), or where its own
POST lands, as specs/nntp.md:465-475 and 1938-1945 state for any connection. The groups page is
LIST ACTIVE on the pinned view, so another session's post reaches it only after a selection; fn1 agrees.
A post's outcome is the model's POST decision, and the page names which one the node gave (Posted! / The
server said no, with the node's 441 line, which is committed as the observed reply); a removal is the
cancel (always filed in control.cancel) and STAT (Removed only for the author, SEC-006).

Where the docs name no status, the model carries fn1's (the crawl probe
`build/coordinator/fn2/lanes/h-quests/webprobe.py`, 153 requests, `webprobe.json`; listed in
web_model's SPEC-MAP). The fixed witnesses (138 requests) agree with fn1 on every reply
(`webwit.py`), and the live S run passes: 5 examples in 15 s at the laptop cadence.

- **W01, fn1-bug, outside the S profile (cross-family: nntp).** On a connection open across an
  `account access` change that narrows the login, fn1 applies the new rule to LIST ACTIVE at once
  (before any re-pin) but posts under the old one, even after GROUP re-pins: POST to the now-excluded
  group is 240, and the article is stored and served to other readers (GROUP 211, STAT 223); a fresh
  connection gets 441. The spec pins the rule with the listing each connection holds and re-pins it at
  GROUP/LISTGROUP (specs/nntp.md:1938-1945), so both halves deviate. Evidence:
  `h-quests/w01-micro.py` (NNTP) and the first `webwit.py` run (the web session). The S form tests
  access rules in sessions that begin after the rule; layer D's served path owes the pinned rule.

## HZ4: the peering and bp S forms (live on fn1)

Every family now has its S form. Both new ones were written from the docs and specs, run first through
the recording probe against fn1 (`h-quests/peerprobe.py` and `bpprobe.py` for the raw replies,
`pp.json`/`bpp.json`; then `witprobe2.py peering|bp` over the fixed witnesses, `wp2-peering.json` with 50
CLI calls and `wp2-bp.json` with 219), corrected, and then run live at the laptop cadence on hbox (image
c14e9e8e): peering 5 examples in 84 s, bp 5 examples in 322 s (per-step reads trimmed after that run).

- **Peering** (`peering_model`): the peer table (add, remove, list, set, feed pause/resume,
  distributions, budget, pull, pull-login, catch-up, login) composed with the one NNTP model. The wire
  effects are checked where they show: a source-address loopback record with an inbound half makes the
  test's own connection the peer (IHAVE/CHECK/TAKETHIS, scope = accept-groups and live: the new
  NntpModel seam `peer_accept`, specs/peering.md:146-153,756-765; fn1 agrees, a crosspost is filed in its
  in-scope group only); three scripted peers observe the outbound feed (CHECK/TAKETHIS after 203, IHAVE
  after a 500 or on a non-streaming record, on connections opened after the record's last edit; nothing
  posted during a pause reaches the peer before the resume was asked; distributions per RFC 5537 §3.6)
  and one NEWNEWS pull (only the listed articles with a name in accept-groups enter). The peer list is
  compared as a set (its order is unspecified). Tags where the docs name only the class are fn1's: the
  usage tags per verb (syntax, feed, distributions, budget, pull, pull-login, catch-up), `port`
  (`peer set --port 0`, refused) and `passwords-differ`; the universal argv preflight renders its tagged
  line with the subject `request`.
- **P01, fn1-bug (an effect row).** fn1 feeds a transferred article by its Newsgroups names, not by
  its local memberships: a pulled article with Newsgroups hz.peer,hz.test, filed in hz.peer only, was
  offered to both scripted peers whose feed-groups are hz.test,hz.other. specs/peering.md:150-152 says an
  article is fed when one of its *accepted local groups* matches feed-groups. For fn1 only the model
  queues such an article by its names (so a fixed fn1 fails the next feed check); fn2 and the fake get
  the specified rule.
- **Observed, outside the peering profile (cross-family: nntp).** A transit IHAVE of an article with two
  Path fields was accepted (235) by fn1; nntp_model refuses duplicated Path/Message-ID/Date fields
  (RFC 5536 §3.1). Not adjudicated here: the peering S form sends single-field articles; the nntp
  family's differential owns the question.
- **BP** (`bp_model`): `carry` list/inspect/pause/resume/drop/drop --abandon over one FNWF journal with
  no node running, `bp-obligation` undertake/status/request/receipt, `bp-boundary add` and `bp-route
  add|remove`. The invariant is read after every step: a Store pin moves only at undertake (no to yes)
  and at an accepted waiver (yes to no); a plain drop, an unsigned receipt, a refused request or a
  re-undertake of a waived work moves nothing. A request is refused before any attempt while paused,
  dropped or waived (`carry-dropped`) or unpinned (`forward-pin-not-durable`); otherwise its outcome
  follows the route table (`decision=no-route`, exit 1; a route to a current boundary queues the job and
  the contact that never connects is exit 7). `drop --abandon` on a work never dropped takes the waiver's
  words as its drop reason too (fn1 shows both; docs/operator.md:754 "also gives up the obligation").
  The producer's enqueues all come first: an enqueue needs no pending journal transaction and a fresh
  transaction id (books/bp-workflow.lisp `fn-bp-prepare-enqueue`).
- **Unit controls.** Each family has an independent fake node with mutation plants, every one caught by
  the fixed witnesses: peering 9 (pause ignored, scope ignored, distributions ignored, remove keeps the
  record, budget unrounded, pull out of scope, refused add applied, streaming peer offered by IHAVE,
  feed to the wrong groups); bp 9 (drop releases the pin, a second waiver accepted, a paused request
  attempted, resume of a dropped work, route ignored, an unsigned receipt releasing, the waiver hidden,
  a waived work re-pinned, an unshaped EID accepted).
- **Harness note.** A whole-suite surface.json at the hbox cadence is large (run-h5b's was 1.7 GB: the
  S forms' traces of every example); read it on hbox (`python3 -m fn2.tests.surface.nightly OUT`), never
  copy it to the laptop.
