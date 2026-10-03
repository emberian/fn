# Empirical scenarios deputy — GPT-6.1-Sol

Tree: `/Users/ember/dev/fn/build/lanes/codex-sol-empirical`
Branch: `codex/sol-empirical-20261003`
Starting source: dev `4479f2acff971292096ebe4a8c44854666d12736`.
Coordinator: `/root/deputy_groundwork`; expensive run/image scheduler and sole dev
writer: `/root/deputy_integration`. Strategic root spawns this worker.

## Owned deliverable and consumer

Own sustained comprehensive native scenario/simulation and empirical performance/
resilience work, beginning with an executable smoke for the first combined image.
Design a workload/coverage matrix from actual contracts and existing scenarios,
connect ACL2-produced labels/oracles to real image holds/faults, and expand until
important mixed workloads can be replayed from seed plus exact event trace.
The consumer is Integration's current immutable fn image, not a Python server or
an independent model that never drives it. Groundwork owns model/custody design
and proofs; this deputy owns empirical execution/harness.

First mixed workload: concurrent posts, cold/slow readers, checkpoint/reclaim.
Then supported peer interruption/recovery and fault/late-completion schedules.
Keep accepted/refused/uncertain/fault distinct. Record latency percentiles,
throughput, bounded progress/fairness, peak resident/disk/FD, recovery and exact
correctness outcomes. Pair baseline/perturbation on matched image/host/profile,
with deterministic seed and replayable event/fault trace; preserve exact image
digest/source, host/runtime and profile coordinates. Use 1k->100k curves, no1M.
Do not run giant suites each cut; start runnable smoke, expand discriminate cases.

## Existing tools to reuse and inspect

- `tests/native_harness.py`, `tools/hbox_native.sh` and `tools/native_box.sh`: actual
  scratch image/service harness and build coordination; Integration owns builds.
- `tools/resilience/scenario.py`, `contract.py`, `checker.py`, `journal.py`,
  `schedule_points.py`: replay schema, bounded verdicts, witness requirements.
- Native adapters `page_io.py`, `response_holds.py`, `reclaim_hold.py`,
  `native_cuts.py`, `bp_node.py`, `bp_slice_observer.py` in
  `tools/resilience/adapters/`; reclaim-hold already uses real OVER response
  quantum capture/settlement and competing reclaim. Reuse actual holders.
- `tools/run_simulator.py` has ACL2-produced acceptance traces but currently only
  acceptance-durable/world. `typed_window_frozen/` and source adapters are exact
  historical fixtures, not current-image assurance. Assess/reconnect useful work.
- `tools/scale_curve.py`, `tools/fixtures.py`, `tools/synth_log_store.py`: current
  matched fixture/profile curve machinery; preserve mode/heap/cache conditions.
- `tools/hostile_campaign.py`, `tests/campaign/native_cuts.py`, native NNTP/
  production kill probes and `planning/design-resilience-framework-2026-09-29.md`.
  Some per-file block-fault scenarios are explicitly retired; do not count their
  helper/mock checks as record-log resilience.
- Groundwork is repairing `books/host-model-machine.lisp` and direct read schedule
  witnesses (cancel/retire/late-return/fd/CID/worker reuse). Ask for ready source
  or exact label contract before turning it into the native schedule consumer.
- Runtime has actual actor latch/post-create failure/failed join/held cleanup and
  inbox native raw schedules. Foundations+Runtime are wiring the typed owner
  worker draw; first actual funding consumer is syncer custody, full user banks
  still unconnected. Capture that distinction in empirical results.

## Authority and workflow

Read AGENTS and core docs/current/plan; no shared-tree mutation/stash/reset, no
other-session file/cache deletion. Isolated test nodes only; never live node,
deployment/publication or outward human messages. Ordinary local commits are
authorized; send READY to Groundwork+Integration and follow failures through dev.
Integrator coordinates hbox swarm-build and scarce scopejobs; ACL2 laptop only
slot wrappers. Narrow checks, no lane --closure. Archive/index evidence with
existing tools; test source stays in tools/tests. Claim new registry IDs first.

Periodic advisory `kimi`/`grok`/ZAI CLI reviews are explicitly authorized for
meaningful batches/early design; no every-change ritual, vote or approval gate.
Use minimal relevant project code, no secrets/personal files, disable editing/
tools/subagents/web where supported, verify/rebut findings. Never print keys.

## Reporting

Keep compact state here: runnable cases, source/image and matched coordinates,
checks, uncovered scenarios, next consumer and genuine obstructions. Send routine
issues/READY directly to Groundwork+Integration. Root receives material decisions
and user outcomes. You own workload design and harness wiring, not only test runs.

## Result slice, 2026-10-03 06:30 UTC

SCN-1083 claimed and added. Native mixed runner now drives an actual image,
not Python semantics. Historical image45e05c7f (core a043eb247eb9a7406abfaa30b36cfa00a9bec555c422e23ff6a494b2e5946cb1)
on hbox, SBCL2.6.8, approved24G scope. Matched seed19/profile T8192/H32MiB/R196608/A32768/G16/K8192.
Both cases24mixed POSTs accepted,36reads matched, all48acknowledged articles
exact served hashes and local numbers survived checkpoint+restart. Quiet
reclaim refused by name deferred-credit (estimate16,680,640): correctness passes,
maintenance coverage incomplete. No current-source/image qualification claim.

Report and sealed plan/journal/summary/manifest/owner streams:
planning/evidence/native-mixed-45e05c7f-2026-10-03/report.md and run-4/{baseline,slow}/.
Source/tools in tools/native_mixed_workload.py; promise-history negative controls
in tests/test_native_mixed_history.py (7passed), existing reclaim/page-I/O/scenario
observer checks22passed. Coverage and actual consumer debts in planning/empirical-workloads.md.
Final executed edit→first verdict5.15s, paired10.75s; setup+seed1.355/1.650s,
mixed0.577/1.136s, restart+exact checks0.187/0.192s. No image build required.

Next: Integration's current combined image smoke; actual HM shared-label
bridge830c23c9c (Groundwork) for observed cancel/physical return/owner settlement;
Runtime funded syncer job after typed producer wiring. Sparse NEWNEWS/tombstones
under concurrent work is Served's next command consumer. No additional scarce
run started while archiving; ask Integration to budget selected1k→100k curves.
Kimi tools[]/subagents[] isolated review partial output then180s timeout,
not a completed review; useful verified metric clarifications queued.
