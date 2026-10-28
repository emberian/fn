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
Every fn2 test skips before invoking a driver, with `layer D/E not yet serving`
followed by its relevant first `node.Fn2Backend` execution requirement.

## Forms and scope

- **P** names the simulator workloads, seeded faults and process-death schedules
  in the manifest. The layer A–E simulator runs remain separate drivers; Python
  does not emulate those machines. There is no P test module.
- **S** runs Hypothesis at 200 examples on laptop, 5,000 on hbox, 50 steps each.
  `nntp/test_model_nntp.py` defines a live `RuleBasedStateMachine` using H2's
  `NntpModel` and the selected `Target`. It currently exercises empty-group
  selection, absent articles, reader/cursor commands and reconnects, comparing
  replies before applying model updates. Accepted POST projection, cancellation
  and nonempty pinned-view schedules are extensions, not covered by this machine.
  Other S modules name their future model and skip until its adapter exists.
- **F** uses H2b through its public CLI for NNTP, without importing driver
  internals: `python3 -m fn2.tests.model.differential --target fn1 --seeds 0..199
  --mode reader,node,peer --steps 50 --out DIR`. Its independent model comparison
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
  and asserts every collected outcome is ok or an explicitly intended retirement.
  Empty results, timeouts and unintended skips fail. Fixture hooks name concrete
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
hooks share one 600-second laptop wall budget or one 3,600-second hbox budget;
each child gets the remaining allowance and its own PID file. An over-budget
child is an error and its recorded process group is reaped. H5 still owes the
CPU allocation within §2.5's aggregate 30 CPU-minute per-commit budget: a wall
cap is not a measurement of total child CPU. The runner does not claim the
simulator, layer READY gates or weekly soak ran.

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
| FUZZ | `seconds`, `corpus` | Return a nonempty argv list. The runner launches it in a recorded session with the remaining aggregate timeout and asserts exit 0. It must implement the grammar oracle and mutation controls. |
| FIXTURE | `path`, `contract` | Replay the fixture against the live target and assert the contract using `case`. |
| HISTORY | `checkers` | Generate/check eligible histories, record observation gaps, and assert findings using `case`. |
| PERF | `row` | Return `{value, unit, profile}`; extra metadata is retained. Never assert a numeric threshold. |

Missing hooks raise named skips under fn1. Drivers should put their detailed
results in `out`; successful invocation alone is not evidence for unimplemented
assertions. To try H2b's independent smoke target separately:
`python3 -m fn2.tests.model.differential --target fake --seeds 0..199 --mode reader,node,peer --steps 50 --out DIR`.
The surface runner itself accepts only fn1/fn2.

## Reports

`OUT/surface.json` contains the profile, budget, family/form selection, individual
outcomes and evidence, skip reasons, native records, and executed assertion-call
counts. `OUT/<family>.md` contains form totals and a separate performance table
headed **published, not a gate**. Native subprocess counts are added once to
wrapper assertions. The metric counts `TestCase.assert*/fail*` calls including
delegation; it does not count Python `assert` or assertions inside external fuzz
drivers (whose detailed output remains beside the report).

A run exits nonzero for a failure/error (including malformed drivers and timeouts),
never for a skip or a performance value. The parent PID file is exclusive and
removed on completion; by default it is `OUT/surface.pid`. Driver PID files are
also exclusive. An existing PID file stops the launch; no process is selected by
name or pattern. Per-family JSON reporting is checkpointed after each family.
