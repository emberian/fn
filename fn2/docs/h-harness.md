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
- **B01, fn1-bug (an effect row; found by the first nightly smoke at the hbox cadence, 50 examples).**
  fn1 keeps `carry pause *` as one wildcard hold beside each work's own pause: `carry list` shows every
  open work `hold=paused`, but `carry resume WORK` of a work paused only by `*` is refused `not-paused`,
  and an accepted `resume WORK` under `*` leaves the work listed paused; `pause WORK` under `*` is
  `already-paused`; a second `pause *` is refused `already-paused` whatever the works hold; `resume *`
  clears the wildcard and every own pause; a request under `*` is refused `carry-paused`
  (`h-quests/b01-micro.py`). docs/operator.md:740-745 make `*` mean every work. For fn1 only the model
  carries the wildcard and records B01 wherever the per-work reading expects another reply or another
  listed hold; fn2 and the fake get the documented per-work hold.
- **Evidence is serialized as data.** A failing S test's evidence holds its traces, whose requests are
  model dataclasses; `run_surface` now writes `json_value(evidence)` (the first smoke's bp child died on
  a TypeError while recording its own failure; every family had the latent fault).

## The hbox nightly (`fn2/tests/harness/hbox_nightly.sh`)

`cd TREE && SWARM_MEM_MAX=64G setsid nohup swarm-build sh fn2/tests/harness/hbox_nightly.sh OUT > OUT.log
2>&1 < /dev/null &`, TREE an extracted tree of the commit under test, OUT a fresh directory. The script
refuses an existing OUT and an output filesystem under 60 GiB free, writes `OUT/nightly.pid` (its own PID;
`kill $(cat OUT/nightly.pid)` stops it and passes TERM to run_surface's own PID file), links the image set
into `TREE/build`, exports the production image (`FN_NATIVE_HOST`, its four identity variables) and the
developer image (`FN_NATIVE_DEVELOPER_HOST`, its identity under the `FN_NATIVE_DEVELOPER_` prefix: the web
and bp S forms and the natives that name it), the pinned OpenSSL wrapper, the durable tmp and the native
opt-ins (`FN2_NIGHTLY_OPT_INS`, default `FN_RUN_SLOW=1 FN_RUN_RELOCATION_E2E=1`), runs `run_surface --box
hbox` under the wall cap (`FN2_NIGHTLY_HOURS`, default 8), and renders `OUT/nightly.md` with
`fn2.tests.surface.nightly` against `fn2/tests/surface/known-fn1.json` (an unmatched non-ok row prints
`unclassified`: the morning's reading list). The last log line is `DONE`.

## Spec pins read by layer D (adjudications both sides apply)

| pin | spec line | the one answer | where each side reads it |
|---|---|---|---|
| P-UTF8-WS (H6, 2026-10-29) | specs/nntp.md:513-518 (NNT-003: "drain rejected input to a safe protocol boundary or close the connection"); RFC 3977 §3.1 | A command line that is not UTF-8 is **malformed** whatever else is wrong with it: the line is decoded before it has words, so surrounding whitespace on a bad-UTF-8 line does not make it a plain syntax error. The answer is `501`, then the connection closes. A valid-UTF-8 line with leading or trailing whitespace stays a plain `501` with the connection kept. | H: `fn2/tests/model/nntp_model.py` `_dispatch` (decode before the whitespace check), test `test_invalid_utf8_is_malformed_before_whitespace`. D: the grammar's `:malformed` class; `fn2/tests/grammar-fuzz-oracle.py`'s whitespace-order exception now counts 0 on the 4,416 cases (13,501 lines, 0 disagreements) and can be deleted. |

The model still accepts a malformed line's 501 *without* a close (EOF optional, the fn1 tolerance
`test_malformed_eof_is_optional_and_requires_observed_eof` records); for fn2 the pin is 501 and close, which is what D answers.

## H5c: the whole suite at the hbox cadence against fn1 (harvested in H6)

Run 05:16-09:19 hbox time on tree11 (dd05b20d6, HX), image set c14e9e8e (TREE_SHA d377d4559), `run_surface
--target fn1 --box hbox --all` under a 64 GiB swarm-build ceiling (mux's start line: `machine=65536 MB`). **The tree predates HY, HZ, HZ2, HZ3, HZ4 and
HZ5**: config_limits S fails on L01 (adjudicated by HY), and the operator, web, peering, bp and store_ops S forms
show OWED (each now implemented and passing live on fn1 at the laptop cadence; bp and peering also at 50
examples on hbox). Report rendered on hbox (`fn2.tests.surface.nightly`, HZ5's known-fn1.json; surface.json is
1.7 GB and stays there): exit 1; 175 tests, 87 executed, 74 ok, 13 not ok, 88 skipped (57 NOT RUN);
398,768 TestCase calls.

| family | status | tests | executed | ok | not ok | skip | NOT RUN | E | S | F | H | R |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| nntp | FAIL | 42 | 26 | 24 | 2 | 16 | 10 | FAIL 22/23 | FAIL 0/1 | PASS 1/1 | PASS 1/1 | NOT RUN |
| consumer | FAIL | 16 | 6 | 5 | 1 | 10 | 7 | FAIL 3/4 | PASS 1/1 | NOT RUN | PASS 1/1 | NOT RUN |
| operator | FAIL | 22 | 6 | 5 | 1 | 16 | 6 | FAIL 5/6 | OWED | NOT RUN | - | NOT RUN |
| web | NOT RUN | 4 | 1 | 1 | 0 | 3 | 3 | NOT RUN 1/1 | OWED | NOT RUN | - | NOT RUN |
| peering | NOT RUN | 18 | 8 | 8 | 0 | 10 | 9 | NOT RUN 8/8 | OWED | NOT RUN | NOT RUN | NOT RUN |
| bp | FAIL | 6 | 1 | 0 | 1 | 5 | 4 | FAIL 0/1 | OWED | NOT RUN | NOT RUN | NOT RUN |
| tls_auth | FAIL | 21 | 17 | 15 | 2 | 4 | 3 | FAIL 15/16 | FAIL 0/1 | NOT RUN | - | NOT RUN |
| config_limits | FAIL | 25 | 14 | 9 | 5 | 11 | 8 | FAIL 8/12 | FAIL 1/2 | NOT RUN | - | NOT RUN |
| store_ops | FAIL | 21 | 8 | 7 | 1 | 13 | 7 | FAIL 7/8 | OWED | NOT RUN | - | NOT RUN |

The 13 non-ok rows, each named:

| family | form | row | class | the reading |
|---|---|---|---|---|
| nntp | E | conformance | known fn1 red | wildcard listener (H1) |
| nntp | S | live_state_machine | **harness-side, fixed in H6** | 5,000 live examples at about 0.48 s each (H5a) is about 2,400 s, which is exactly the default TestCase limit. It timed out without a verdict. families.json now gives nntp's hbox cadence `s_timeout` 7200, and run_surface's `test_timeout` reads it (unit test `test_s_timeout_override_is_per_family_and_box`). |
| consumer | E | store_identity | unprovisioned | box-step `build/box/wire-grammar.json` absent |
| operator | E | status_live_posts | known fn1 red | times out run directly too (H1) |
| bp | E | decoded_custody | known fn1 red | (H1) |
| tls_auth | E | visibility_join | known fn1 red | `fn_client` import (H1) |
| tls_auth | S | live_state_machine | **harness-side (model bug), fixed in H6** | The sequence was USER, a refused XREDEEM exchange, then AUTHINFO PASS; fn1 answered `482 authentication commands issued out of sequence`. fn1 keeps one pending slot per connection for AUTHINFO USER's name, a SASL exchange and XREDEEM's code and login (books/nntp-auth.lisp, "The pending slot"). The model kept three. specs/nntp.md states each exchange alone, so the model now follows the book. The model and fake share the slot (`_pend`); the live form has a fixed witness and the unit tests a mutation control (`redeem-keeps-user`). Committed in 22de14c4d. |
| config_limits | E | bounds_join | known fn1 red | (H1) |
| config_limits | E | image_differential | **harness-side (provisioning), fixed in H6** | 13 tests fail on `build/fn-host.world-deps` absent: the seat's H5c script and hbox_nightly.sh linked a fixed file list that omitted the image set's three `*.world-deps`. The nightly now links every `fn-host*` file of the set. Rerun alone with them linked (h-quests/h6-imgdiff.sh): 20/20 ok. |
| config_limits | E | mux | known fn1 red | (H1) |
| config_limits | E | public_limits | known fn1 red | (H1) |
| config_limits | S | live_state_machine | fn1-bug L01 (adjudicated in HY) | The auth-failure 400 carries `; try again later`. The tree predates HY. |
| store_ops | E | served_crash_model | known fn1 red | (H1) |

None of the four harness-side rows was a stable red, so known-fn1.json is unchanged. NOT RUN by reason: perf
drivers owed for every family (30 rows); fixture drivers owed (nntp 2, consumer 2, bp, peering, tls_auth, web);
fuzz drivers owed for the eight families other than nntp; history drivers owed for peering and bp. Provisioning:
the prof developer image (dead_run), the 2 GiB wrapper (heap_from_profile), a source-matched topic image, the
combined E2/checkpoint developer image, FN_ACL2, FN_RUN_CONSUMER_E2E with a source-matched developer image, a
copied frozen image (relocation), FN_RUN_SLOW (peer_rows_growth), unprivileged user namespaces (refused on hbox).

## H6: control_across_peers and the memory ceiling (an adjudication, not an fn1 bug)

nightly-smoke2's one `unclassified` row was peering E `control_across_peers`. Both matrix tests' connections were
greeted with `400 too many connections; try again later`. That is fn1 keeping its declared capacity, not a
connection limit hit by load. Every fn1 node sizes its connection capacity C' at start from the memory equation
(books/admission-memory.lisp `fn-adm-capacity`). The limit there is the least memory ceiling the node observes:
physical memory, or the cgroup's memory.max up the hierarchy (host/native/heap.lisp
`fnn-heap-resident-observations`), less about 134 MB of pools. Each node prints the result as `memory capacity=C' of C`.

The test holds every connection open until cleanup. On nodes A and B it holds 31 at once, the configured cap
(`max-connections` 32, less one); H holds 25. The seat counted the held connections from the FN2_OBSERVE_DIR logs
(h-quests/conncount.py):

| run | ceiling | node's line | peak held | outcome |
|---|---|---|---|---|
| nightly-smoke2 | 16 GiB | `capacity=22 of 31 ... limit=16250 MB` | H's 23rd refused | fail (both matrix tests) |
| run-h5 (the first hbox suite run) | 32 GiB | `capacity=31 of 31 bound-by=configured ... limit=32634 MB` | A 31, B 31, H 25 | ok |
| H5c | 64 GiB | (no observation log kept) | - | ok, 4/4 |
| H6 alone, quiet hbox | 64 GiB | `capacity=31 of 31 ... limit=65402 MB` | A 31, B 31, H 25 | ok, 4/4 |
| H6 alone, quiet hbox | 96 GiB | `capacity=31 of 31 ... limit=98170 MB` | A 31, B 31, H 25 | ok, 4/4 |

In each row the limit plus the pools comes to exactly the ceiling, so the smoke was launched under a 16 GiB
swarm-build ceiling, not the documented 64G. fn1 refuses exactly at C'+1 with NNT-043's 400, which is the spec.
The fix is on the harness side. hbox_nightly.sh now prints the least memory ceiling and refuses one under
`FN2_NIGHTLY_MIN_MEM_GIB` (default 32). The test was run on hbox: 16 GiB is refused, and 64 GiB prints
`memory ceiling 64 GiB`. Nothing is added to known-fn1.json, because the row passes at every ceiling the nightly
now accepts. A note for layer D: the carried natives assume a node holds 31 connections, and an fn2 node that
sizes its capacity from memory the same way needs the same floor.
