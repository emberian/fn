# Surface suite (H4)

The nine families partition all 120 H1a native obligations. `families.json` maps
RELEASE-PLAN §1 rows and §2.2 forms to tests, future drivers, fixture paths,
performance rows and cadence. `rewrite-row` obligations stay in the partition;
`run_natives --retired-skip` removes only inventoried obsolete methods. The
manifest assigns a native to one primary family and preserves all its original
row links. A family count is an obligation count, not a coverage claim.

```sh
build/venv/bin/python -m fn2.tests.surface.run_surface --all --box laptop --target fn2 --out build/h4-empty
build/venv/bin/python -m fn2.tests.surface.run_surface --family nntp,consumer --box hbox --target fn1 --out build/surface-nightly --pid-file build/surface-nightly.pid
```

The seat launches fn1 on hbox under `swarm-build`, with real image/tool paths.
This runner does not build images or initiate a remote job. Family names accept
both `tls_auth` and `tls-auth` (likewise config/store). Omitted selection means all.
`--target` defaults to `FN2_SURFACE_TARGET`, or `fn2`. Direct unittest discovery
uses the same environment variable and the same shared `serving` decorator.
`families.json` declares the families each target `serves`: fn1 claims all nine;
fn2 claims none until layer D declares them. An unserved family skips before
invoking a driver, with `layer D/E not yet serving` followed by its relevant
first `node.Fn2Backend` execution requirement. These skips are **NOT RUN**, exit 3.

## Forms and scope

- **P** names the simulator workloads, seeded faults and process-death schedules
  in the manifest. The layer A–E simulator runs remain separate drivers; Python
  does not emulate those machines. There is no P test module.
- **S** takes live counts from each family’s per-box `model_examples`: NNTP
  200/5,000 (laptop/hbox), consumer 5/50, with 50 steps each; TLS/auth and
  config/limits and operator use 5/50 examples with 30 generated steps plus fixed
  witnesses; store_ops uses 5/50 with 20 generated steps plus fixed witnesses. H5a measured
  NNTP’s 200 examples at 96.016 seconds; consumer measured about 30 seconds
  per example. Fake model unit tests retain 200 examples. `live_model_settings`
  disables Hypothesis’s shrink phase: zero shrink executions. Failure replay
  and the failing example itself still take time; this is no wall-time promise.
  The helper uses `RUN['box']`, or `FN2_SURFACE_BOX` for direct discovery.
  `nntp/test_model_nntp.py` defines a live `RuleBasedStateMachine` using H2's
  `NntpModel` and the selected `Target`. It currently exercises empty-group
  selection, absent articles, reader/cursor commands and reconnects, comparing
  replies before applying model updates. Accepted POST projection, cancellation
  and nonempty pinned-view schedules are extensions, not covered by this machine.
  Consumer, TLS/auth, config/limits, operator and store_ops also have implemented
  live S machines. Operator covers the row 76 group/moderation/MOTD/capacity/
  retention verbs and row 77 account/principal login management; authority,
  subscribe-default, hashes and bindings remain outside this slice. Store_ops
  covers export/import, stopped-copy blessing, compact/checkpoint, inspect,
  recover and status, preserving Message-IDs, group numbers and bodies through
  the single NNTP model. Reclaim and its RSS measurement remain outside this slice.
  Both HZ machines use independent fake targets and mutation controls, record
  mismatches before asserting, and leave their adjudication tables empty until
  the seat records fn1 replies. Each example targets roughly 30 seconds nominal;
  live timing is unmeasured here, and the child supervisor remains the hard bound.
  The remaining S forms are `owed` in the manifest, with their required model module.
  They appear in reports but generate no test and are not counted as run.
- **F** uses H2b through its public CLI for NNTP, without importing driver
  internals: `python3 -m fn2.tests.model.differential --target fn1 --seeds 0..199
  --mode reader,node,peer --steps 50 --seconds SHARE_MINUS_MARGIN
  --minimize-seconds 5 --out DIR`. Its independent model comparison
  is a carried seed driver; D2's grammar generators and mutation controls remain
  owed. Other families expose argv-producing driver hooks below.
- **H** runs H3's `from_observe.adapt` and consumer/durable checkers on per-test
  JSONL records collected by E natives. It records unmapped evidence explicitly
  and skips when no relevant mapped operation exists. NNTP's per-version Elle
  projection, peering/BP convergence, and crash schedule generation remain owed.
  `FN2_SURFACE_HISTORY_NNTP` / `FN2_SURFACE_HISTORY_CONSUMER` may name another
  observation directory. TLS, web, operator, config and store have H dashes in
  §2.2 and no H modules. Connection-policy F is also a dash; the combined
  config/limits family's F module is specifically for config parsing.
- **E** creates one test per carried native. Each runs an isolated
  `run_natives.child`, with its backend set to fn1 after the shared fn2 gate,
  and checks every collected outcome. Manifest `budget.native_timeout` is 300
  seconds on laptop and 2,400 on hbox. `native_timeout_overrides` gives
  `open_depth`, `over_pins`, `over_window` 2,400 seconds on both boxes; H1b
  durations for other modules are unavailable here and must extend that table
  when supplied. Native skips remain skips in the surface
  report: inventoried retirements and `harness/intended-skips.json` entries are
  permitted; other skips make the run NOT RUN. Empty results and timeouts fail.
  Fixture hooks name concrete
  corpus paths or explicitly owed paths. Merely finding a fixture is never a pass.
  RFC fixtures require live setup (e.g. an issued watermark of 3999), so their
  full live replay adapter remains owed rather than replaying them against the
  model and calling that server conformance. INN's witness is
  `NativePeerPullTests.test_pull_from_inn` inside the carried `peer_pull` module.
- **R** has one test per named performance row, selected on hbox only. Drivers
  supply measurements with a unit and profile. No comparison to a numeric bar
  occurs in these tests. Existing native assertions retain their original
  outcomes; the surface wrapper does not suppress them.

The laptop selects E/S/F/H of the requested families; hbox adds R. Hbox `--all`
selects all 120 natives. NNTP H2b seeds are `0..199` / `0..4999`. The serial fuzz
hooks reserve equal shares of a 600-second laptop or 3,600-second hbox wall
budget among the selected applicable F forms, before any family executes.
Missing drivers keep their reserved share; execution order cannot starve later
families. Every command receives `--seconds` with its share minus a margin of
60 seconds or half the share, whichever is smaller. NNTP minimization receives
at most 5 seconds (also bounded to a quarter of the margin). Budget exhaustion
reported by a self-stopping driver is completion. Exceeding the supervisor’s
full share remains an error; it reaps only the recorded process group. H5 still owes the
CPU allocation within §2.5's aggregate 30 CPU-minute per-commit budget: a wall
cap is not a measurement of total child CPU. The runner does not claim the
simulator, layer READY gates or weekly soak ran.

NNTP mismatches use [`../model/adjudications.json`](../model/adjudications.json),
the source of truth derived from the H2c/H2d markdown groups and their observed
bytes. Schema 2 keeps exact `rule`, `detail` and observed `reply_patterns`.
Groups with structural classes use a named `match` predicate and preserve the
original command as `command_example`; other groups retain exact
`command_pattern`. A13 recognizes a malformed first keyword token, A15 requires
reader mode and a malformed transit argument, and H2d closure predicates require
the relevant command sequence and transport evidence. Missing causal context
is new evidence. A changed reply remains new even when the command class matches.
H2d takes
precedence over overlapping H2c groups. fn1 accepts recorded observations of
all adjudicated classes; fn2 accepts only `spec-ambiguity`. Fake targets accept
none. Reports list each mismatch’s group/class and count recorded versus new;
new mismatches fail. Driver setup errors, interruption, missing/inconsistent
summary evidence, unexpected exit status and supervisor timeouts still fail.
Use fresh output directories so an old mismatch file cannot excuse a new run.

## Process and example lifetimes (HX)

Every served E/S/F/H TestCase runs in its own interpreter. The child writes
`OUT/<family>/children/<form>/<test-id>/result.json`, with its own original
TestCase outcome, evidence and assertion count; `request.json` records the
selection and cadence, and `driver.log` retains diagnostics. `driver.pid` is
exclusive while the child lives and is removed after reaping. Native environment
plans travel in the child's environment, never in these JSON artifacts.
A dead child, exhausted descriptor table, invalid/missing result or timeout is
an error for that selected test; later tests and families still run. E retains
its existing per-native child inside this supervisor. Unserved families only
execute their skip gates in the parent.

S and H use the manifest's 300-second laptop / 2,400-second hbox timeout per
TestCase. E native wrappers allow their native timeout plus 30 seconds; F
allows its reserved share plus 30 seconds so its inner driver supervisor can
record its own timeout. These are wall limits, separate from Hypothesis counts.
Use a fresh output directory; an existing child request/result is refused.

The descriptor leak was `tools.ports.reserve`'s process-lifetime port-lock
files: every fresh `Node` holds another lock descriptor, even after
`Node.stop_all` and all streams close. Implicit TLS reserves a second one.
The surface `owned_ports` adapter records the exact `(port, fd)` acquired by
its construction thread and releases only those leases after the node and
socket cleanups. Concurrent decorated constructors are serialized; another
thread's ordinary reservations stay process-owned. This applies to the shared
Target (NNTP/consumer), TLS/auth, config/limits and its fixed config witnesses,
operator and store_ops.
Tests retain all fake-machine instances after every teardown, exercise real
port-lock files with only the TCP-bind probe replaced, and compare `/proc/self/fd`
or `/dev/fd` before/after all five examples of each machine. Constructor failure
also preserves unrelated leases and releases owned ports after node cleanup.

Design note for Astra: isolation per TestCase gives the smallest useful fault
boundary and keeps an original outcome visible, while family isolation would
lose later tests in the failed family. The shared port allocator would ideally
return an explicit releasable lease. HX leaves its process-lifetime API intact
and confines the adaptation to surface constructors; no resource is recovered
by guessing from all global descriptors or waiting for garbage collection.

## Provisioning and driver hooks

For fn1 natives the runner plans selected modules once using `native_env.py`.
Set `FN2_SURFACE_IMAGES` to override the default six image names
`developer,production,dtn,dtn-developer,reference,developer-stripped`.
`FN_TEST_OPENSSL_BIN` and `FN_FIXTURES_DIR` supply the plan's box substitutions.
`FN2_SURFACE_IDENTITY=IMAGE` and `FN2_SURFACE_SOURCE=SHA` must be supplied together
to compute all four identity values. Existing parent identity/manual opt-in
variables also carry through. No availability skips are silently approved.

Optional hook names have the shape `FN2_SURFACE_<FORM>_<FAMILY>=module:callable`:
`FUZZ`, `FIXTURE`, `HISTORY`, `PERF`; family uses uppercase underscores.
The callable receives keyword arguments `case`, `target`, `family`, `out`, plus:

| form | inputs | result / responsibility |
|---|---|---|
| FUZZ | `seconds`, `corpus` | Return a nonempty argv list. The runner launches it in a recorded session with its reserved share as timeout, supplies `--seconds`, and asserts exit 0 (NNTP mismatches use the ledger below). It must implement the grammar oracle and mutation controls. |
| FIXTURE | `path`, `contract` | Replay the fixture against the live target and assert the contract using `case`. |
| HISTORY | `checkers` | Generate/check eligible histories, record observation gaps, and assert findings using `case`. |
| PERF | `row` | Return `{value, unit, profile}`; extra metadata is retained. Never assert a numeric threshold. |

Missing hooks raise named skips under fn1. Drivers should put their detailed
results in `out`; successful invocation alone is not evidence for unimplemented
assertions. To try H2b's independent smoke target separately:
`python3 -m fn2.tests.model.differential --target fake --seeds 0..199 --mode reader,node,peer --steps 50 --seconds SHARE_MINUS_MARGIN
  --minimize-seconds 5 --out DIR`.
The surface runner itself accepts only fn1/fn2.

Each family package has one `load_tests` hook backed by the shared form generator.
Implemented forms keep their prior unittest IDs. The substantive NNTP model
module remains; other per-form discovery wrapper files are unnecessary. The
runner explicitly installs the selected native adapter before collection and
uninstalls it in `finally`; importing surface modules does not install an adapter.

## Reports

`OUT/surface.json` contains the profile, budget, family/form selection, individual
outcomes and evidence, skip reasons, native records, pass/fail counts, and
**TestCase-call count**. `OUT/<family>.md` contains each form's status and totals,
owed forms, and a separate performance table
headed **published, not a gate**. Native subprocess counts are added once to
wrapper assertions. The metric counts `TestCase.assert*/fail*` calls including
delegation; it does not count Python `assert` or assertions inside external fuzz
drivers (whose detailed output remains beside the report).

A run exits 1 for a failure/error (including malformed drivers and timeouts),
or when a served family executes zero tests (`served family ran nothing`).
Otherwise, any selected test skipped without an inventoried retirement or
intended-skips entry gives exit 3, with a **NOT RUN** count and reasons. Failures
take precedence over NOT RUN. Only passing tests and explicitly permitted skips
give exit 0. Skipped forms still show **NOT RUN**, even when their skips are
permitted; owed forms show **OWED**. A performance value is never a gate.
The parent PID file is exclusive and
removed on completion; by default it is `OUT/surface.pid`. Driver PID files are
also exclusive. An existing PID file stops the launch; no process is selected by
name or pattern. Per-family JSON reporting is checkpointed after each family.
