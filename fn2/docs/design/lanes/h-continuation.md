# fn2 layer H continuation (present state, rewritten whole; 2026-10-29, third monitor)

Seat: Opus monitor for layer H (the surface test harness). Brief: `build/coordinator/briefs/FN2-LAYER-H-HARNESS.md`
over `FN2-SEAT-COMMON.md`; design `fn2/RELEASE-PLAN.md` §1-2 (esp. §2.2-2.6) and §5.5's H row (H4 tools/load at B READY,
H5 per-commit budget benchmark + nightly driver at D READY); review `fn2/REVIEW-SINS-20261028.md` §5 (H1-H5).
Touches nothing under fn2/books, fn2/sim, fn2/host. Reports to main only READY/RED/BLOCKED (SendMessage to "main"),
ONE READY LINE PER LANDED QUEST with its sha (coordinator, 10-29).

## NOW (third monitor, 2026-10-29)
- HX landed dd05b20d6, HY landed 287655a40 (READY sent for both).
- config_limits S live PASS on fn1 (hbox tree12, hy-live.sh -> run-hy/): 2 tests ok, 5 ex, 48 s, with L01-L06 recorded.
  Probe scripts on hbox (scratch tree tree11p): keyprobe.sh, setprobe.sh (copy h-quests/hy-setprobe.py); evidence <wt>/build/hy-evidence/.
- H5c RUNNING on hbox (tree11 = dd05b20d6; h5c-surface-fn1.sh -> run-h5c/out; PID h5c-surface-fn1.pid; 8 h cap; launched 05:16 hbox).
  Its config_limits S fails on L01 (known, fixed by HY after the tree was cut). Harvest per family when DONE; READY with counts.
- HZ RUNNING (Codex 01a18703-969d-7eb3-88fb-ccb9197a582e; h-quests/HZ.{prompt,log,pid}): operator S (rows 76-77) +
  store_ops S (rows 73-75, line-84 subset) as two sub-agent pieces; ADJUDICATIONS start empty, wired as limits_model.
- Coordinator 10-29: main merged fn2/h-harness at 287655a40. After H5c lands: rebase fn2/h-harness onto the new fn2/main
  (the worktree must be clean: do it after HZ is committed), then keep merging main forward into the branch on every READY;
  main fast-forwards from the branch when it contains main.
- Review notes kept: OperatorExpectation needs the refusal as a whole word; init passes --max-record-octets 24 MiB.
- Laptop unit acceptance: `build/venv/bin/python -m unittest fn2.tests.harness.test_harness fn2.tests.history.test_history
  fn2.tests.model.test_nntp_model fn2.tests.model.test_differential fn2.tests.model.test_consumer_model
  fn2.tests.model.test_limits_model fn2.tests.surface.test_run_surface fn2.tests.surface.tls_auth.test_model_tls_auth_unit
  fn2.tests.surface.test_adjudications fn2.tests.surface.test_live_evidence` (~60 s, 310 OK at 287655a40) and the empty fn2 run (exit 3).

## Where things are
- Worktree `/Users/ember/dev/fn/build/lanes/fn2/h-harness`, branch `fn2/h-harness`, pushed head 287655a40 (HY). Rebased on fn2/main 9cc09f2bf on 10-29 (zero diff vs main in fn2/books, sim, host); shas of H1a-H2d in the
  table are pre-rebase. READY sent for HR, HS, HT, HU, HV, HW, HX, HY.
- Quest files: `build/coordinator/fn2/lanes/h-quests/<Q>.{prompt,log,pid,last.md,REPORT.md,commitmsg,repair.msg}`.
- Venv with hypothesis 6.170.13 (py3.11): `<wt>/build/venv`. Native inventory: `inventory.load()` (build/natives/).
- Evidence copied from hbox into the worktree's build/: h5a-fn1/ (H5a surface.json + own_cancel logs), hs-live-fn1/ (probe runs).
- Layer D/E are not serving; fn2 serves no family (families.json serves.fn2 = []).

## Decision: the fn1 node runs on hbox, not the laptop
hbox image set `/tank/fn/images/keyed/c14e9e8e29ef4e34765271d69885970751f516ba317e583774b9bb9d261a40c4/` (TREE_SHA d377d4559);
recorded at the top of `fn2/docs/h-harness.md`. hbox scratch: `/tank/fn/scratch/fn2-h-harness/` (trees tree..tree10, run-*/).

## hbox recipe (works)
- Ship: `git archive --prefix=tree/ HEAD | gzip -1 | ssh hbox 'cd /tank/fn/scratch/fn2-h-harness && rm -rf tree && tar xzf -'` (commit first).
- The full-fidelity fn1 run: `/tank/fn/scratch/fn2-h-harness/h1b-fn1.sh` (copy: h-quests/h1b-fn1.sh;
  description if lost): symlinks every image file into `tree/build/`, writes the openssl-test wrapper, exports FN_TEST_OPENSSL_BIN,
  FN_OPENSSL_PREFIX, FN_TEST_DURABLE_TMP=$B/tmp, FN_FIXTURES_DIR=/tank/fn/scratch/fixtures, `native_env.py identity` of build/fn-host
  with source = the image's TREE_SHA, then `native_env.py plan --allow-skips --images developer,production,dtn,dtn-developer,reference,developer-stripped`
  for the 120 modules and runs each line as `env <assignments> python3 -m fn2.tests.harness.run_natives --backend fn1 --modules M --timeout 2400 --out run-h1b/out/M`
  with `xargs -P 4`. Launched as `SWARM_MEM_MAX=64G nohup swarm-build sh h1b-fn1.sh > h1b-fn1.log 2>&1 < /dev/null & echo $! > h1b-fn1.pid`
  (the ssh call hangs until the job ends: run it with run_in_background, check with a second ssh).
- Results: `/tank/fn/scratch/fn2-h-harness/run-h1b/out/<module>/<module>.json`; aggregate them with a short python over `*/*.json`.
- Live S forms on fn1: `h-quests/hu-live.sh` (on hbox as hu-live.sh): env HU_TREE (tree dir), HU_FAMILIES (space list);
  runs each family's S test at the laptop cadence with /usr/bin/python3 + PYTHONPATH=venv site-packages.
- Whole suite: `h-quests/h5b-surface-fn1.sh` (hbox cadence: --box hbox; tree7/run-h5b): copy with a new tree/out for H5c.

## Quests
| quest | state | commit |
|---|---|---|
| H1a native dependency inventory | accepted, pushed | 9520c3b8b |
| H1b Node adapter, shim, runner | accepted, pushed | 84565e40d |
| H1c shim transparent to module-level patching (the one adapter fault the fn1 run found) | accepted, pushed; verified on hbox: harness 31/31 through the adapter | 5913ba326 |
| H2a NNTP reference model | accepted, pushed | cb0d074c5 |
| H2b differential driver | accepted, pushed | 91cc6b747 |
| H2c adjudicate run 1 + driver robustness | accepted, pushed | 5e3e49488 |
| H2d adjudicate run 2 + close attribution (resumed H2c session) | accepted, pushed | 5b641fc0a |
| HR review remedies 17 (skip is not pass, S form on fn1, load_tests) and 18 (JUDGMENTS to data, generated inventories out of tree, shim one module + explicit patch points) | accepted, pushed; seat git-rm'd natives-inventory.json + docs/natives.md, fixed the stale generated preamble, rewrote h-harness.md's shim/skip sections | b8fb91b05 |
| H3 history model + checkers | accepted, pushed | e3c55d792 |
| H3b observer enrichment | accepted, pushed | 53371e6d4 |
| H4 surface skeleton + run_surface + --env-plan | accepted, pushed; empty fn2 run 150/150 skipped "layer D/E not yet serving", exit 0 | 8669c4d6a |
| H4b placeholder fn2 host + intended-skips table | accepted, pushed; fn2 sweep 588 named node-dead, 20 named placeholder, 104 retired, 39 intended, 21 other (each with reason) | 605e87bbf |
| HS consumer S form (consumer_model + live machine + to_h3 morphism to H3) and H2d driver rows (TLS close_notify transport, --takethis-probe) | accepted, pushed; seat fixes: live `more` no longer fabricated, TLS control TCP branch needs 127.0.0.2 (absent on macOS); A13/A15/A16 recommendations recorded in fn2/docs/h-harness.md | ac885b5ce |
| HU tls_auth S form over nntp_model (fixed witnesses + 30 generated steps, independent fake, 5 mutation controls) | accepted, pushed; 232 unit tests OK | 016c15cc3 |
| HV the COMPRESS ruling (480 before auth; label optional before auth; seat widened unauthenticated bad-argument to 480-or-503/501, dropping Codex's HV-01 fn1-bug); H2d-08's 24 rows are model-bug (layer D's advertise-while-inactive obligation withdrawn); replay 183/139 and 21/33; NOT RUN reason nit fixed | accepted, pushed; 236 unit tests OK | 095433a9f |
| HW config_limits S form (limits_model composed into nntp_model via `limits`; fixed wire witnesses + 30 generated sets; 6 controls) | accepted, pushed; 251 unit tests OK | 859f433c9 |
| HT repair from the fn1 runs: A runner budgets (per-box native timeout + overrides, F split + --seconds + adjudications.json ledger, live S examples, no live shrink); B history: cancel authority per SEC-006 (sent back once: the first cut treated any 240 cancel as a withdrawal); C nntp_model A14 (TAKETHIS article always follows; replay 159/163, was 144/178); D consumer adjudication table (C01 repeated unregister) | accepted, pushed; 218 unit tests OK on the laptop | 2beebb84c |
| H5a whole suite, laptop cadence vs fn1 (tree b8fb91b05) | DONE exit 1: known fn1 reds + 28 NOT RUN (fuzz budget, owed drivers, provisioning); harness-side findings fixed in HT | - |
| HS/HU/HW live S runs on fn1 | consumer PASS (5 ex, 330 s, C01 adjudicated); tls_auth PASS (5 ex, 23 s); config_limits fixture failures -> HX D | - |
| H5b whole suite, hbox cadence vs fn1 (tree7 = 2beebb84c) | DONE but poisoned by consumer S fd leak (EMFILE) -> HX A; nntp S 5000 ex lost its failure to a diverging replay -> HX B; nntp F 3 new A13-class rows -> HX C | - |
| HX isolation + fd leak (tools.ports lock per Node), live failure capture (s-failure.json), predicate adjudication (schema 2), config_limits fixture | accepted, pushed; diff read whole; seat applied B's hooks + an end-to-end control; 304 unit tests OK | dd05b20d6 |
| HY config_limits adjudications L01-L06 from the seat's 152-pair fn1 probe + live greeting (fn1-bug L01/L02/L04, spec-ambiguity L03/L05/L06) | accepted, pushed; 310 unit tests OK; config_limits S live PASS on fn1 (5 ex, 48 s) | 287655a40 |

## Next (after HX lands)
1. H5c (whole suite, hbox cadence) and config_limits S live; READY with the counts per family.
2. H5 (plan): hbox nightly provisioning of the opt-ins (FN_RUN_SLOW for peer_rows_growth, a 2 GiB memory wrapper for
   heap_from_profile, prof and source-matched developer images for dead_run, protected_peering, consumer_e2, topic_local,
   checkpoint if hbox has them under /tank/fn/images/keyed/*, FN_RUN_RELOCATION_E2E), the nightly driver + report table
   (build/coordinator/fn2/nightly/<date>.md), and the per-commit budget from measured per-driver timings (30 CPU-min, §2.5).
   Still to look at from H5a: peer_hostile_feed and image_differential (LISTENING not seen in 180 s) under the new timeouts.
3. The remaining S forms: operator, store_ops, web, peering, bp (owed) in the consumer/tls_auth/config_limits pattern
   (one model per protocol, composed; fixed witnesses + generated steps; independent fake + mutation controls; adjudicate
   only from recorded fn1 replies). Each live run finds model-vs-fn1 differences: consumer found 2, tls_auth 1 (COMPRESS), config 2.
4. Owed E fixture drivers (FN2_SURFACE_FIXTURE_* for nntp, consumer, web, peering, bp, tls_auth) and H history drivers
   (peering, bp) and R perf drivers: currently NOT RUN by design.
5. Review H4 (nntp_model's command table from layer D's defgrammar) waits for D. When D serves: serves.fn2 gains the family.

## Known fn1 reds (not harness): agent_wait, control, bounds_join, conformance, decoded_custody, live_reconfiguration,
mux (x2), owner (x2), public_limits (x2), served_crash_model, store_identity, visibility_join, status_live_posts (timeout);
H2d fn1-bugs: TAKETHIS 436 without Message-ID (13). (COMPRESS not advertised, 24, was the model's: HV.)

## fn1 evidence (hbox, image c14e9e8e, TREE_SHA d377d4559) -- H1's acceptance, FINAL
- 120 modules through the adapter (fn1 backend; pass 1 + pass 2 with /usr/bin/python3 + H1c's harness rerun):
  794 tests: 742 ok, 37 skip, 12 fail, 3 error; 107 modules all ok; 1 module timeout (status_live_posts, also times out run
  directly); 296,430 executed TestCase assertion calls. Every non-ok test is identical run directly without the adapter
  (pass 2 compared adapter vs direct per test; the one adapter fault, harness, was fixed by H1c: 31/31).
- fn1's own reds: agent_wait, control (source-text asserts vs books/), bounds_join, conformance (wildcard listener),
  decoded_custody, live_reconfiguration, mux (x2), owner (x2), public_limits (x2), served_crash_model, store_identity
  (box-step wire-grammar.json absent), visibility_join (fn_client import), status_live_posts (timeout).
- H3 native acceptance: the six consumer natives with FN2_OBSERVE_DIR (34 logs) through from_observe and both checkers:
  ZERO anomalies. Checked ops: 23 register, 40 ack, 18 post, 10 crash, 69 recover; 50 polls and 13 positions are
  observed-only (fn1's poll output lacks `more`, as H3b predicted), no reads mapped, so C2-C4/C6 and D1 are not exercised
  natively yet. Logs: <wt>/build/h3-observe/.
- H2 differential (H2d final): run 2 42 seeds, 370 sessions, 7,455 compared, 7,133 matched, 322 rows: 37 fn1-bug (COMPRESS
  not advertised; TAKETHIS 436 without Message-ID), 144 model-bug fixed with spec lines, 3 driver-bug, 138 open A13-A16.

## Review record
- HR: read the whole diff (surface runner/init/manifest/README, shim, node, run_natives, inventory head+loader, test_harness,
  judgments schema + sample). Regenerated inventories byte-identical to the committed copies before git rm. 145 unit tests OK;
  empty fn2 surface run exit 3 (142 NOT RUN, 8 OWED); fn2 natives spot check (compress, harness, consumer_exchange, web, mux)
  tuples identical to build/h4-fn2-seat. Seat fixes: orphan comments, generated preamble now states the present truth.
  Note, accepted: owed S forms generate no test, so a family with E green and S owed exits 0 (OWED shown in every report).
- H1a: generator read whole; JUDGMENTS sampled against source; --check and determinism re-run. Accepted.
- H1b: read node.py (278), shim.py (92), run_natives.py (356), test_harness.py (255), docs whole; ran the 14 unit tests (OK).
  Accepted as the adapter. The fn2 laptop sweep: 120 modules, 798 tests: 400 named node-dead, 104 intended retirements,
  248 skips + 21 errors at the modules' own pre-node gates (image env vars, opt-ins, identity hashes, install-native.sh),
  25 non-node passes. Codex's "universal acceptance unmet" is that residue: it is environment provisioning (the runner
  should give each module tools/native_env.py plan's assignments, as hbox_native.sh does), assigned to H4. Codex's
  safety miss: its first sweep ran tls_transport's four raw SBCL tests; now refused by an audit hook under fn2.
  Notes, not refusals: shim._host relies on `Path` copied from fn1's globals; Fn1Backend.session returns the shim Client.

- H2a: read nntp_model.py (1,230) whole, framing.py, the state machine and mutation controls; 51 tests OK. The stateful machine
  computes GROUP's expected rows partly via the model's own _available (watermarks are independent): self-consistency; the
  differential (H2b) is the real oracle test. Accepted.
- H3: read MODEL.md, history/consumer/durable/synthetic/from_observe/tests whole; 31 tests OK; nine injected kinds 100/100. Accepted.
- H3b: read the node/shim/from_observe diff and tests whole; 50 tests OK. Zero work when FN2_OBSERVE_DIR is unset (tested with traps).
  Still open: fn1 poll output lacks `more`; visibility unobservable; subprocesses bypassing Node unobserved.
- H2b: read differential.py (616) and tests whole; 9 tests OK. Codex hit an OpenAI "cybersecurity" flag mid-session (fuzzing);
  resumed with a message framing it as conformance testing of our own server on loopback: worked.
- HS: read consumer_model.py, test_model_consumer.py, test_consumer_model.py (fake + controls) and the differential/test
  diffs whole. 192 unit tests OK on the laptop after the seat's two fixes; empty fn2 surface run exit 3, consumer S NOT RUN.
  Live (hbox): TLS TCP branch OK; A14 probe 15/15 awaited-body + 439; consumer S found binding-survives-unregister
  (model fixed) and repeated-unregister `scope` (adjudicated C01 in HT).
- HT: read all four pieces' diffs whole; sent piece B back for SEC-006 authority (now: same observed account locally,
  origin authority or RFC 8315 key/lock on peers, unknown auth = info). 218 unit tests OK (laptop, TCP included).
  Accepted trade-off: adjudications.json matches exact command+reply bytes, so a new byte variant of a known class is
  `new` (fails on fn1); widen per group only with a reason.
  Notes, accepted: the model's waiter-capacity refusal is reachable only on the fake (serial live profile); rebase is
  fake-only (no CLI carrier in request codes 0..10); bind/unbind are operator verbs the fixture drives.
- HU/HV/HW: read whole. HV seat widened unauthenticated bad-argument COMPRESS to 480-or-503/501 (no invented precedence) and
  dropped Codex's HV-01 fn1-bug. HW: the seat's prompt invented `policy show` (fn1 has none); removed via a repair message.

## Commands that work
- Launch: `cd build/coordinator/fn2/lanes/h-quests && nohup codex exec -C <wt> --skip-git-repo-check --sandbox workspace-write
  -c sandbox_workspace_write.network_access=false --output-last-message $PWD/<Q>.last.md "$(cat <Q>.prompt)" < /dev/null > <Q>.log 2>&1 & echo $! > <Q>.pid`
- Waiter: `while kill -0 $(cat <Q>.pid); do sleep 30; done` in a background call.
- Capacity/auth errors: `resume-retry.sh <Q> <session id>` (uses build/REPORT-<Q>.md); a seat message to a finished session: `resume-msg.sh <Q> <session id> <msgfile>` (retries capacity errors).
- Commit: message to `h-quests/<Q>.commitmsg`, `git add <named files>`, `git commit --no-gpg-sign -F`, `python3 tools/secrets_check.py`, push.
- hbox launch without hanging: `ssh hbox 'cd /tank/fn/scratch/fn2-h-harness && (VARS SWARM_MEM_MAX=8G setsid nohup swarm-build sh X.sh > X.log 2>&1 < /dev/null & echo $! > X.pid)'`;
  wait with a background `until ssh hbox 'grep -q "^DONE" .../X.log'; do sleep 60; done`.
- Ship a tree: `git archive --prefix=treeN/ HEAD | gzip -1 | ssh hbox 'cd /tank/fn/scratch/fn2-h-harness && rm -rf treeN && tar xzf -'`.

## Coordinator rulings in force
- Prewrite prompts; disjoint quests run in parallel; every diff still read whole.
- Codex multi-agent is on (`features.multi_agent`, max_depth 2): a prompt with two or more disjoint pieces tells the top-level Astra to
  spawn one sub-agent per piece and report per piece (H4's per-family skeleton is the example); never for pieces sharing files.

## Pitfalls hit
- hbox: venv has hypothesis but no cryptography, /usr/bin/python3 the reverse (both 3.12.7): run /usr/bin/python3 with
  PYTHONPATH=$B/venv/lib/python3.12/site-packages.
- The inventory JSON is now a build output: `inventory.load()` (or `python3 -m fn2.tests.harness.inventory --out build/natives`),
  never `fn2/tests/harness/natives-inventory.json` (h1b-fn1.sh's MODS line reads the old path: use inventory.load()).
- The hbox venv has no system site-packages: natives needing `cryptography` must run with /usr/bin/python3.
- Codex content flag on fuzzing: rephrase as conformance testing of our own server; resume by session id.
- zsh: `echo =====` is a glob error; use `---`.
- `native_env.py plan` without `--allow-skips` refuses opt-in-gated modules (exit 2, empty output).
- Parallel Codex sessions share build/REPORT.md unless each prompt names its own file.
- The differential's reader sessions bind source 127.0.0.2: absent on macOS (EADDRNOTAVAIL), present on Linux.
- Codex's sandbox denies loopback bind: tests needing TCP run on the seat (laptop or hbox), never trusted from Codex alone.
- Launch on hbox without hanging: `ssh hbox 'cd DIR && (SWARM_MEM_MAX=..G setsid nohup swarm-build sh X.sh > X.log 2>&1 < /dev/null & echo $! > X.pid)'`.
- Old note: plain nohup ssh launches of swarm-build hang until the job ends: launch with run_in_background, poll with `until ssh ... grep -q DONE`.
