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

## Follow-up source slice, 2026-10-03

Developer-only `FN_NATIVE_PAGE_IO_HOLD` observations now record actual
file/fd/dev/inode installation, direct admission (previous counter and full
worker row), fd capture, read count with explicit injection flag, stored job
condition/literal verdict, actual job activation return, owner direct-settle
verdict/answer, and successful fd close. No private vector is printed and no
Python cancellation/settlement semantics are introduced. Existing native
PageIO success, cancel/retire/late-return, and late fault scenarios consume the
observations; source observers refuse missing return events or substituted
tokens. Integration must execute these on the next developer image: source
checks are not native execution. Full certified HM replay remains unavailable
until actual lock/pin observations and model/native dependency hashes align.
Groundwork is told native short verdict is literal `:READ`, not `:SHORT`.

Mixed runner follow-up splits resource samples by PID, timestamps sampler
errors and lifecycle durations, records UTC run bounds, names the phase-rate
metric explicitly, and adds `--check-run` for sealed promise-history checks.
Offline checking preserves the recorded incomplete maintenance verdict; it
reports promise history only. Both historical journals rechecked successfully.
These new instrumentation bytes have not been transferred onto the historical
image result's exact executed input hash.

Checks: 13 image-free PageIO/history tests pass; host shape check reports zero
findings (raw native files excluded); extent's 111 top-level forms balance
under the source tokenizer. Narrow actual-image run pending Integration.

## Sparse command result slice, 2026-10-03 07:15 UTC

SCN-1085 claimed; `tools/native_sparse_newnews.py` executes actual native
24-row sparse discovery, two offline expiry tombstones, four concurrent
nonmatching posts, eight retained reads, eight competing NEWNEWS requests,
and complete reopen. Historical image 45e05c7f: all 10 discovery blocks exact,
all 28 posts accepted, 26 retained exact source comparisons and two persistent
tombstones on reopen. Live reclaim refused credit (estimate 8,098,624), while
offline expiry accepted exactly two. Per-command payload-I/O attribution
unavailable; new Served cursor/current image still owed. Report and 79-event
sealed journal archived under native-sparse-newnews-45e05c7f-2026-10-03.
Final native workload through reopen 17.042 s, total including artifacts/cleanup
35.425 s, last edit to complete verdict 38.327 s. Three sampled owner PIDs,
100 successful samples; offline-control processes excluded. No further scarce
run started. Extent observer review fix ee142a184 gates job-only classification
before developer selection; Integration queues e76+ee142 for next source batch.

## Selected repeated recovery result, 2026-10-03

Historical 45e05c7f actual log-written death then recover-barrier-1 owner-open
death: existing checker consistent, prior and candidate exact source reads,
both candidate memberships visible after recovery, duplicate retry with two
records retained. Atomic-memberships explicitly pending. Wall 7.54s, healing
1.776s, GNU time child-command max RSS 571724KiB; FD/disk peaks unmeasured.
Long-path first attempt native CONTROL-PATH-TOO-LONG refusal before faults,
preserved separately. Sixteen archived objects indexed under
native-recovery-45e05c7f-2026-10-03. Executed adapter exact 2e2d101a6; latest
10e342872 initial POST uncertainty branch unit-only. EOF completeness and
literal uncertainty transport fixes plus early selected-cut construction
are committed and READY. No speedup inference without matched baseline.

Runtime offers actual section-envelope acquire/release primitive callback and
reserved native actor identity; Groundwork supplied exact admitted vocabulary.
Extent fd/job fixture consumer exists; wait concrete seam source before wiring,
then preserve actual issue tuple and compare only complete grounded traces.
New combined image qualification still pending; Integration solely schedules.

Extent admission diagnostics now include actual cid/inc/eoff/elen/trailer
arguments passed to fn-pio-direct-admit. Existing native handoff fixture
requires the complete literal tuple; it cannot reconstruct missing inputs
from the token. Seven image-free transport checks pass. Native execution
requires an image including this source; no certified replay claim yet.

## Peer preflight source and refusal, 2026-10-03

3716a9926 reuses existing same-source native NNTP producer for BP fixture;
fa9e9ef19 separates native exit classes instead of every nonzero becoming
lost; 5afc1e275 corrects shared bp_producer bytes MID CLI transport. Three
focused control/transport tests pass. Final historical production+DTN45e
fixture accepted POST240 and generated stored source/ADU through ACL2, then
actual bp-obligation undertake rc1 canonical Store refused retention event.
No peer nodes or fault reached; no custody/recovery result. Historical retries
stopped.26objects archived native-bp-preflight-45e05c7f-2026-10-03. Groundwork
owns retention producer follow-through, Tools command consumer; no user gate.

First current image1a946 source/core6f5bf888 now available and Integration's
raw/counterpart POST+duplicate+readback passed. One approved baseline mixed
completed correctness, all48acknowledged content/numbers reopen,24mixedposts
accepted and36reads; quiet reclaim credit-refused remainsincomplete. Sparse
current schedule executing sequentially under approved24Gscope; nohook/funding
claim because image excludes these later sources. Evidence filing follows.
Runtime d4/0fa observer activation/source ready; generic E seam requested
before extent collection/executorwrapping. FullPageIO remains unavailable.


## Extent observer consumer, 2026-10-03

Dependency packet Runtime d4cb69168/0fa276f82 + shared early io seam
8b777bf9f/e60d9f0d2/09c7e72a3 (assembled 983f199/ad0f1666f). This lane
owns extent only: actual executor thunk captures native identity; direct
fd-open/issue/io-begin/literal io-complete/cancel/physical-return/settle/close
inputs enter the bounded collector. Observer arguments are unevaluated when
absent. Forty finite E mutex regions observe actual acquire/release; the two
condition-wait regions are deliberately unobserved. Conditions and unexpected
worker death are not converted or reordered into literal :error completion.

Native raw transport composition passed using deployed io/owner forms from
those dependencies plus this extent macro and a real SBCL thread/mutex;
no fn semantic decisions are mocked. Eight image-free transport checks pass.
The actual normal held-read image selector now consumes post-cleanup NATIVE-HM,
checks complete collector prefix plus direct labels, and explicitly reports
full PageIO comparison unavailable. COMPLETE is never full physical coverage.
Matching image execution remains pending Integration's next source batch;
1a946 current image excludes this packet. Full replay still owes actual wait,
pin and remaining owner edges, literal condition boundary and exact dependency
coordinates. No mux/owner/io edits in this lane.


## Current image results filed, 2026-10-03

Image1a946582c/core6f5bf888, immutable earlier catalog, sequential isolated
24GiB scope: baseline mixed4.198s total (0.314s mixed phase),24concurrent posts
accepted/36exact reads/all48acknowledged hashes and numbers after reopen.
Actual checkpoint/reseating observed; quiet reclaim still credit-refused
estimate16,680,640. Current sparse4.829s, ten exact four-ID discovery blocks,
eight exact reads/four competing accepted POSTs, offline expiry/reclaim2accepted,
26retained+2tombstones after reopen; live reclaim credit-refused8,098,624.
Report coordinates native-mixed-1a946582c-2026-10-03 and
native-sparse-1a946582c-2026-10-03 in archived evidence. This image excludes
later funding/cursor/extent hooks; no performance improvement or whole-image
qualification inference. Exact config/input hashes and sampler errors retained.
Mixed used copied native_cuts2e2; sparse updated to10e bytes before execution;
manifest input hashes govern, supplied driver revision is not whole-tree identity.

Observer b4f03503c + follow-up0d0eee69a exclude both staged window/PWZ tokens
from direct return labels. Eight transport checks + exact deployed raw macro/
collector SBCL thread/mutex composition0.099s passed; five evidence objects
native-extent-observer-b4f03503c-2026-10-03. Actual held-success image pending
next Integration assembly. No active native runs; current repaired BP or normal
held-read next when Integration supplies matching image/scope. Curves still held
until existing fixture152da/native-n7 compatibility is actually established.
