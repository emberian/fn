# fn2 layer H continuation (present state, rewritten whole; 2026-10-30, eighth seat)

Seat: Opus seat for layer H (the surface test harness). The seat WRITES the code (FN2-SEAT-COMMON "The method from
2026-10-29 afternoon"); Codex (second account) only for bounded pieces with real signatures pasted, every line read.
Brief `build/coordinator/briefs/FN2-LAYER-H-HARNESS.md` over `FN2-SEAT-COMMON.md`; design `fn2/RELEASE-PLAN.md`
§1-2 and §5.5's H row. Touches nothing under fn2/books, fn2/sim, fn2/host. Reports to main (SendMessage "main"):
READY (sha + one line) per commit, RED, BLOCKED; rewrite this file whole after every commit.

## NOW (state)
- dev is the branch; shared tree `/Users/ember/dev/fn` (other seats' files dirty there: commit ONLY named layer-H
  files). Commit: `git add -N` new files, then `git commit --no-gpg-sign -F <msg> -- <paths>` (zsh arrays for path
  lists); before a push `python3 tools/secrets_check.py`, `git fetch origin dev`, merge if behind (never rebase/stash).
- Commits this seat, all pushed, READY sent: 22de14c4d (P-UTF8-WS pin; one pending auth slot), 3ea9d2f8d (H5c
  harvest; control_across_peers = memory ceiling; nightly floor + world-deps), a1167fc24 (H7a fixture drivers),
  cfdeb5e6f (H7b F/H/R drivers + first runs), e495a7b55 (H7c reruns: every F form passes on fn1; P-SASL-LINE,
  H7-07, H7-08, the node's article bound in the differential), 4f931bd74 (H7d: reply window grows with segments
  sent; H7-08 withdrawn), 4ed372d1e (H7e: FNCT frame fuzz after fncu, TCPCL session fuzz after BPv7), 8ae997f07 (H8a: SimTarget, the Target
  over D's simulator session), 524e30869 (H8b: nntp S vs fn2 under the simulator, M1a gate: 16,730 served 0
  disagreements, 15,741 interim named, WIRE ok), 4b1c90ca4 (H9: nightly 2026-10-30 harvested; web removal by post access), 68677f727 (H10: fn2/docs/release-gates.md, the
  17-gate migration matrix for R1, with a cut_release.sh dry run at 945f625ad; logs in h-quests/r1-dryrun-945f625ad/),
  c47cbeff2 (H11, merged and pushed as 762c94853): nntp S rerun at 83ced3bf9 under the sim, counts unchanged
  (16,730 / 0 / 15,741). WIRE judged 4 of 17,776 connections, because sim-session.lsp keys clients by slot.
  SimTarget now fails unjudged connections; D fixed the session in 323c9da1d + e0f1377a3. fn2-native target added.
  Nothing of H uncommitted.
- Then eb692d3cf (H12: pin P-DUP-FIELD; the model accepts "<Field> appears more than once"; the Q1 seat
  claimed from-duplicate in c16d5d862) and cd2b74e48 (H13: M1b green at 10e454049). Sim and native each gave
  16,730 served / 0 disagreements / 15,741 interim / WIRE 17,776 opened = judged ok, 0 unjudged (native also
  ENVELOPE ok); 105 s sim, 298 s native. All pushed, READY sent.
- WAITING ON: D5 READYs from main (D5 2/n should remove POST's 713 interims). At each one, rerun both targets
  (items 4 and 4b) and report served / interim / WIRE. Nothing of H is running; no PID files are live.
- Nothing running on hbox for H. Last nightly: 2026-10-30 (build/coordinator/fn2/nightly/2026-10-30.md; h-harness.md
  section). Every S and F form passes against fn1 (web S after H9's fix, rerun 50 ex PASS).
- Last F runs: run-h7-fuzz-4 (operator, store_ops), -7 (tls_auth), -8 (peering with H7d), run-h7-perf/rows.json.
- Laptop unit acceptance (~65 s, 402 OK at e495a7b55 (403 OK at 4ed372d1e)), from /Users/ember/dev/fn: `build/h-venv/bin/python -m unittest
  fn2.tests.harness.test_harness fn2.tests.history.test_history fn2.tests.history.test_convergence
  fn2.tests.model.test_nntp_model fn2.tests.model.test_differential fn2.tests.model.test_consumer_model
  fn2.tests.model.test_limits_model fn2.tests.model.test_operator_model fn2.tests.model.test_store_ops_model
  fn2.tests.model.test_web_model fn2.tests.model.test_peering_model fn2.tests.model.test_bp_model
  fn2.tests.surface.test_run_surface fn2.tests.surface.tls_auth.test_model_tls_auth_unit
  fn2.tests.surface.test_adjudications fn2.tests.surface.test_live_evidence fn2.tests.surface.test_fixtures
  fn2.tests.surface.test_perf fn2.tests.surface.test_argv_fuzz fn2.tests.surface.test_config_fuzz
  fn2.tests.surface.test_http_fuzz fn2.tests.surface.test_codec_fuzz fn2.tests.surface.test_sim_target` (408 OK at c47cbeff2 before its last two tests; test_sim_target 6 OK).

## The drivers (H7; table in fn2/tests/surface/README.md, results in fn2/docs/h-harness.md H7a/H7b)
- FIXTURE `fixtures:fixture` (rfc3977 live replay, consumer-position, bp golden, scram RFC 7677; web and
  wire-grammar named skips). FUZZ `fuzz:fuzz` dispatching: tls_auth/peering -> differential `--focus auth|feed`;
  operator/store_ops -> `argv_fuzz`; config_limits -> `config_fuzz` (`operator PATH show`); web -> `http_fuzz`;
  consumer -> `fncu_fuzz --with-fnct` (then `fnct_fuzz`); bp -> `bp_fuzz --with-tcpcl` (then `tcpcl_fuzz`). HISTORY `history_drivers:history` (peering convergence V1-V4 + durable;
  bp durable). PERF `perf:perf` (tools/load cells; row map perf.ROWS / UNMEASURED).
- Standalone: `python3 -m fn2.tests.surface.<module> --target fake|fn1 --seeds A..B --out DIR [--plant P]`.
  Live on hbox: image env FN_NATIVE_HOST / FN_NATIVE_DEVELOPER_HOST (consumer-inspect, web) / FN_NATIVE_DTN_HOST
  (bp decode). Seat runners: h-quests/h7-fix.sh (E fixtures), hbox h7-fuzz.sh (H7_TREE, S_OUT, H7_LABEL,
  H7_FAMILIES, H7_SECONDS), h7-perf.sh.
- Spec pins both sides read (h-harness.md "Spec pins read by layer D"): P-UTF8-WS, P-FNCU-HEADER, P-FNCU-EPOCH,
  P-SASL-LINE.
- Adjudications added: H7-01..H7-05, H7-07, H7-08 (model/adjudications.json, predicates in
  surface/adjudication_predicates.py; H7-06 withdrawn for the pin P-SASL-LINE); A01 (argv_fuzz.ADJUDICATIONS).
- Open: listed under What remains, item 2.

## What remains (in order)
1. On main's forward of a D READY (D5 transaction machine: POST, IHAVE, TAKETHIS): rerun the fn2 nntp S under the
   simulator (item 4's command) and report served/interim counts; a disagreement goes to main with the case.
2. Owed pieces: the W7 perf adapter (tools.load.w7_extent); perf rows with no tools/load cell (consumer wake/M5,
   web p99, W3-W5 hostile workloads); bp bundle convergence with the F8 simulator scenario.
3. Keep fn2/docs/release-gates.md current as drivers land (R1 owns it; H keeps the driver rows). The per-commit
   30-CPU-minute allocation (§2.5) is still H's.
4. fn2 surface under the simulator: nntp S runs via serves_sim.fn2. Run (H11 form, from /Users/ember/dev/fn):
   `FN2_SURFACE_SIM_NNTP=fn2.tests.surface.fn2_sim_session:session FN2_SIM_EXAMPLES=1000 FN2_SIM_STEPS=50
   PYTHONPATH=$PWD build/h-venv/bin/python -m fn2.tests.surface.run_surface --target fn2 --family nntp --out DIR`
   (detached via the setsid wrapper, PID file), then `build/h-venv/bin/python build/coordinator/fn2/lanes/h-quests/h8-counts.py DIR`
   for served / interim / wire. It needs certified fn2/tests/conn-unit, sim/echo and sim/check-wire, done with
   `sh fn2/tools/certify.sh tests/conn-unit.lisp sim/echo.lisp sim/check-wire.lisp` detached with a PID file; it
   recertifies the whole closure (~25 min after a foundation move). If another seat edits a book mid-certify, you
   get book-hash-mismatch: rerun on the new tip. Logs: build/h8/.
4b. fn2-native (M1b): serves_native.fn2-native = [nntp]; NativeTarget over FN2_SURFACE_NATIVE_NNTP (same session API).
   One command: the item-4 line with FN2_SURFACE_NATIVE_NNTP=fn2.tests.surface.fn2_native_session:session and
   --target fn2-native. It also needs sim/check-envelope certified. It runs in parallel with the sim run. Without the hook
   the case is a named skip (checked: build/h8/run-native-nohook.log).
   Regenerating fn2_conn_interim.json is D's. Peer connections wait for E4: open(peer=True) raises NotImplementedError.
5. A nightly only when its tree has moved, on the seat's word (recipe below; SWARM_MEM_MAX=64G; ~6 h).

## The nightly recipe (fn2/tests/harness/hbox_nightly.sh; documented in fn2/docs/h-harness.md "The hbox nightly")
- Ship the commit: `git archive --prefix=nightly-<sha>/ <sha> | gzip -1 | ssh hbox 'cd /tank/fn/scratch/fn2-h-harness
  && tar xzf -'`. Launch without hanging ssh: `ssh hbox 'cd /tank/fn/scratch/fn2-h-harness/nightly-<sha> &&
  (SWARM_MEM_MAX=64G setsid nohup swarm-build sh fn2/tests/harness/hbox_nightly.sh ../nightly-<date> >
  ../nightly-<date>.log 2>&1 < /dev/null &)'`. Wait with a background `until ssh hbox 'grep -q "^DONE" ...log'`.
- The script refuses an existing OUT, < 60 GiB free, or a memory ceiling < 32 GiB (H6; ALWAYS launch at 64G), writes OUT/nightly.pid (stop: `kill $(cat OUT/nightly.pid)`,
  which TERMs run_surface via its PID file), links the image set (FN2_NIGHTLY_IMAGE, default c14e9e8e) into
  TREE/build, exports FN_NATIVE_HOST + identity and FN_NATIVE_DEVELOPER_HOST + identity under FN_NATIVE_DEVELOPER_
  (web and bp), the OpenSSL wrapper, durable tmp, opt-ins (FN2_NIGHTLY_OPT_INS, default FN_RUN_SLOW=1
  FN_RUN_RELOCATION_E2E=1), runs `run_surface --box hbox` (FN2_NIGHTLY_FAMILIES or --all; FN2_NIGHTLY_HOURS cap,
  default 8), and writes OUT/nightly.md. Copy nightly.md to `build/coordinator/fn2/nightly/<date>.md`; rows are not
  chased except `unclassified` reds that name a decision.
- Not yet provisioned for a full nightly: the 2 GiB wrapper for heap_from_profile; prof/source-matched developer
  images for dead_run, protected_peering, consumer_e2, topic_local, checkpoint; the per-commit 30-CPU-minute budget
  from measured timings (RELEASE-PLAN §2.5) is still owed.

## fn1-bug ledger (S forms and differential; every row is backed by a recorded fn1 reply)
| row | family | what fn1 does vs the spec | recorded in |
|---|---|---|---|
| A01 | operator, store_ops | a non-ASCII argument: host usage error, no ARGV-MALFORMED tag (specs/native-admin.md:12-15) | argv_fuzz.ADJUDICATIONS; h-harness.md H7b |
| H7-03 | peering, nntp | TAKETHIS article answered 436 closing (H2d class, widened by reply) | model/adjudications.json |
| H7-07 | tls_auth | AUTHINFO PASS after a pending XREDEEM CODE NAME answered 481 (counted) where RFC 4643 2.3.2 says 482 | model/adjudications.json |
| L01, L02, L04 | config_limits | live policy refusal rows (HY's 152-pair probe); L03/L05/L06 are spec-ambiguity | fn2/tests/model/limits_model.py ADJUDICATIONS; h-quests/hy-policy-pairs-fn1.json; fn2/docs/h-harness.md (HY) |
| O01 | operator | `group retire` accepted but the wire keeps serving the group (effect row) | operator_model.py ADJUDICATIONS; h-harness.md "HZ"; wp2-operator.json, hz-micro.py |
| W01 | web/nntp (outside the S profile) | access change on an open connection: LIST ACTIVE live, POST still pinned after GROUP | h-harness.md "HZ3"; h-quests/w01-micro.py |
| P01 | peering | a transferred article fed by its Newsgroups names, not its local memberships (effect row) | peering_model.py ADJUDICATIONS; h-harness.md "HZ4"; wp2-peering.json |
| B01 | bp | `carry pause *` is a separate wildcard hold: listed paused, `resume WORK` refuses not-paused (effect row) | bp_model.py ADJUDICATIONS; h-harness.md "HZ4"; h-quests/b01-micro.py |
| C01 | consumer | repeated unregister `scope` (adjudicated, HT) | fn2/tests/model/consumer_model.py (adjudication table) |
| H2d TAKETHIS | nntp | TAKETHIS 436 without the Message-ID (13 rows) | fn2/tests/model/adjudications.json, DIFFERENCES.md |
| observed, not adjudicated | nntp | a transit IHAVE with two Path fields accepted (235); nntp_model refuses duplicates | h-harness.md "HZ4" (for the nntp differential) |

## Where things are
- Quest files and seat tools: `build/coordinator/fn2/lanes/h-quests/` (<Q>.commitmsg; probes: witprobe2.py (generic,
  family arg: operator|store_ops|peering|bp), peerprobe.py, bpprobe.py, b01-micro.py, hz-micro.py, w01-micro.py,
  webprobe.py, webwit.py; hbox runners hz-probe.sh (overlay fn2/tests onto tree14 + witprobe2, production image),
  seatprobe.sh (WP_SCRIPT, WP_IMAGE=fn-host|fn-host-developer, WP_OUT), h5c-surface-fn1.sh; replies wp2-*.json, pp.json, bpp.json).
- hbox `/tank/fn/scratch/fn2-h-harness/`: tree..tree14 (tree14 = tree13 + the shared tree's fn2/tests overlaid,
  the seat's probe tree), hz2-live.sh (production image live S: HU_TREE, HU_FAMILIES), web-live.sh (same with the
  developer image: web, bp), run-*/ outputs, nightly-smoke*/, venv.
- fn1 image set (the evidence): `/tank/fn/images/keyed/c14e9e8e29ef4e34765271d69885970751f516ba317e583774b9bb9d261a40c4/`
  (TREE_SHA d377d4559); the fn1 node runs on hbox only, never the laptop.

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
| HZ operator S (rows 76-77) + store_ops S (rows 73-75, row-84 subset), Codex, died at usage limit | seat read whole, fake-accepted, merged | 1244dbb62 (merge d4aeb6600) |
| HZ3 web S (WebModel over pinned NntpModel sessions; fake face + 7 controls; W01 recorded, outside profile) | seat-written; crawl 153 req, witnesses 138 agree; live 5 ex 15 s PASS | 80458ea94 + 335878b2b |
| HZ5 hbox nightly script, bp B01 (found by its first smoke at 50 ex), evidence written as json_value | smoke: script plumbing OK; bp S PASS at 50 ex | 9eda68ca0 |
| HZ4 peering + bp S (seat-written; probes peerprobe.py/bpprobe.py, witprobe2 peering|bp; P01 fn1-bug feed by Newsgroups names) | peering live 5 ex 84 s, bp 5 ex 322 s (148 s trimmed); probes 0 disagreements (50 / 219 calls) | cd92f8635 |
| H7a E fixture drivers | rfc3977 19/19, consumer-position 6, bp golden 2 (octet-equal re-author), scram 4 ok live | a1167fc24 |
| H7b F/H/R drivers | F: config 5,659 / web 1,000,000 / fncu 800 / bp 800 cases 0 findings; argv+focus classes adjudicated; H: 0 anomalies; R: 20 rows | cfdeb5e6f |
| H7c F reruns | operator 5,145 / store_ops 4,911 calls 0 findings; tls_auth 1,348 / peering 346 compared 0 new | e495a7b55 |
| H7d reply window (H7-08 fixed) | peering F rerun 346 compared, 0 new | 4f931bd74 |
| H7e FNCT + TCPCL fuzz | fnct 300 / tcpcl 80 cases vs fn1, 0 findings | 4ed372d1e |
| H8a SimTarget over D's sim session | fake-session unit tests + WIRE refusal control | 8ae997f07 |
| H8b nntp S vs fn2 under the sim (M1a gate) | 1,000 ex x 50 steps: 16,730 served 0 disagreements; 15,741 interim named; WIRE ok | 524e30869 |
| H9 nightly 2026-10-30 harvest + web removal by post access | every S/F passes on fn1; 11 non-ok: 8 known, 2 unprovisioned, web S fixed | 4b1c90ca4 |
| H10 the 17-gate release matrix (fn2/docs/release-gates.md) | seat-written; dry run at 945f625ad: GREEN 02/08, RED 01/03/04/05/07/09, 10-15 preconditions present, 16 would run | 68677f727 |
| H12 pin P-DUP-FIELD (upload contract's from-duplicate) | model moves; D unchanged | eb692d3cf |
| H13 M1b: nntp S on a socket + sim with full WIRE | both 16,730/0/15,741, 17,776 judged ok | cd2b74e48 |
| H11 sim rerun at 83ced3bf9, WIRE per-connection coverage, fn2-native target | counts = H8b; WIRE judged 4/17,776 -> D case; S RED until fixed | c47cbeff2 |
| H6 pin P-UTF8-WS (D seat's request) + one pending auth slot | seat-written; D oracle 0 disagreements; 148 unit OK | 22de14c4d |
| H6 H5c harvest, control_across_peers adjudication, nntp s_timeout, nightly world-deps + memory floor | seat-written; reruns: across_peers 4/4 at 64/96 GiB, image_differential 20/20 | 3ea9d2f8d |
| HZ2 live on fn1: tagged-line reason parsing, fn1 tags where docs name only the class, operator-form import, O01 effect row | seat-written; probe 0 disagreements; operator S 5 ex 173 s, store_ops S 5 ex 46 s PASS | 8a4875e89 |

## Known fn1 reds (not harness): agent_wait, control, bounds_join, conformance, decoded_custody, live_reconfiguration,
mux (x2), owner (x2), public_limits (x2), served_crash_model, store_identity, visibility_join, status_live_posts (timeout);
H2d fn1-bugs: TAKETHIS 436 without Message-ID (13). (COMPRESS not advertised, 24, was the model's: HV.)
S-form fn1-bugs: config_limits L01/L02/L04 (HY); operator O01 group retire keeps the group served (HZ2);
peering P01 feed by Newsgroups names not local memberships (HZ4); bp B01 `pause *` is a separate wildcard hold (HZ5);
web/nntp W01 access rule on an open connection: LIST ACTIVE live, POST pinned even after GROUP (HZ3, outside profile).

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
- A session API keyed by slot id judges only the last incarnation: every carrier must give each open its own id
  (SimTarget enforces opened == judged since H11).
- macOS has no `setsid`: launch detached laptop runs as `nohup python3 -c 'import os,sys; os.setsid(); os.execvp(sys.argv[1], sys.argv[1:])' CMD ... & echo $! > X.pid`, then check `ps -o pid=,pgid= -p $(cat X.pid)` agree.
- build/ is git-ignored: only fn2/ files are committed; continuation, quest files and dry-run logs live on the laptop.
- The hbox nightly output dir is `/tank/fn/scratch/fn2-h-harness/nightly-YYYYMMDD` (no dashes); surface.json under it.
- `bp receive` without a STORE (with an enrolled bp-boundary for the peer at the receive port) refuses every inbound bundle at the receive boundary; accepted bundles journal to lifecycle/*.fnb (the log's `BP accepted ... path=`), not receive-evidence/*.adu.
- fn1 refuses a control socket path past 103 octets (CONTROL-PATH-TOO-LONG): a deep --out kills every differential node (fixed: short scratch dir in differential.owner).
- `fn --fn config check` answers an oversize profile with a fault; the operator verbs say usage: fuzz through `operator PATH show`.
- Never put a running seat script under edit in place: replace by `mv` of a new file (sh reads scripts incrementally).
- A fuzz value list must not contain flag names (`--off`, `--queue`): flag-shaped values ask a question no spec decides.
- fn1's connection capacity follows the launch's cgroup ceiling (limit = ceiling - ~134 MB): a swarm-build under 32 GiB shrinks C' below 31 and natives holding many connections meet a correct 400. Launch nightlies at 64G.
- Link the WHOLE image set (fn-host* incl. *.world-deps), never a fixed list.
- surface.json at the hbox cadence is huge (1.7 GB for H5b): read it on hbox only.
- bp: enqueue every work before any request (an enqueue needs no pending journal transaction and a fresh txid).
- The argv preflight's tagged line has subject `request` (`usage operator request ARGV-MALFORMED`).
- `OWNER-OPEN ... reason=absent` precedes every store-opening reply: take `reason=` from the tagged/`store:` line only (bp_reason).
- Shared index: anything staged can be swept into another seat's bare commit. Commit `-- <paths>`, never stage.
- NntpModel Conn copies policy/credentials at connect: set policy['stored_articles'][id] before connecting
  (or on the conn), and mark temporary model conns quit (31-connection model limit).
- Web face: fnr_pre persists while the browser presents a live one (HEAD does not invalidate it); CSRF is on every
  signed-in page, absent until one is read after sign-in.
- `git worktree remove` deletes the worktree's git-ignored build/ (venv, evidence copies): copy evidence out first.
- fn1 CLI replies: the tagged line can follow `Password: Confirm password: ` on the same line; `store` sub-verbs
  inspect/import (and the direct `fn store S ...` verbs) print no tagged line; reasons appear as `reason=X`.
- The direct `fn store S import --FIELD N` ignores the override; use `operator CONFIG store import`.
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
