# The release gates: the 17-gate migration matrix (RELEASE-PLAN §5.1-5.2, §5.6 R1)

Layer H wrote this early so the release quests start from a matrix. It covers every gate of
`tools/cut_release.sh` (and the checklist's 15a). For each gate it gives:

- the contract the gate keeps on fn2's swapped tree;
- the driver that evidences it, named down to the module;
- what the evidence reads (the provenance rule below);
- what the gate depends on, whether it is required, and who owns the driver;
- the negative control that shows the gate can go red;
- its disposition today, on fn1 and on fn2.

R1 (main) owns the matrix and `planning/release-v5.1.1.md`. H keeps the driver rows current until R1
takes them.

## Rules the matrix applies

**Provenance** (§5.2, *[Astra]*). A piece of evidence names the closure it ran on:

- the source sha;
- the profile (the node's `fn.toml` preset, or the simulator's `tiny`/`concrete` profile);
- the seed range, or the example count and step bound;
- the toolchain: the ACL2 8.7 launcher identity as `tools/acl2` reports it (record toolchain
  `8aeb1bea1896` on hbox; forge's equals hbox's), SBCL, Python with Hypothesis (laptop: 3.11.16 with
  6.170.13), OpenSSL;
- the image set, by its key, when an image ran.

Evidence counts at the cut only when that closure is the release closure, or differs from it only in
paths the evidence does not read. Dates establish nothing. Every "today" below names its sha for that
reason.

**Dispositions.**

- **MET on fn1**: a run of this gate's own driver on fn1 went green, at the named sha.
- **RED on fn1**: the 2026-10-30 dry run at dev `945f625ad` reports this gate red.
- **NOT RUN on fn2**: the driver exists, but it has not run on fn2.
- **owed**: the driver or its fn2 rewrite does not exist yet. The quest that owes it is named.

No fn1 release was ever cut. No v6.6.0 run reached `VERDICT GREEN`, and gates 09-15 never ran on one
closure.

**Performance is published, never a gate.** The one exception is W13's guardrail (VmHWM ≤ 249 MB), the
one resource row that gates (§5.2).

## The matrix

| gate | contract on fn2 | driver (fn2) | req. | owner | fn1 today | fn2 today |
|---|---|---|---|---|---|---|
| 01 version | `VERSION` is `5.1.1`, the sequence's next entry; the tag is free or at REV | `tools/release_sequence.py cut-check` (unchanged) | yes | main | RED by design (`5.1.1-pre`) | same driver; NOT RUN (pre-cut) |
| 02 tree | HEAD is REV, no tracked change | `cut_release.sh` g_tree (unchanged) | yes | main | GREEN at 945f625ad | same |
| 03 fundamentals | every F-row of `planning/release-v5.1.1.md` MET **on the release closure** | g_fundamentals rewritten: each MET row carries its evidence's closure identity | yes | R1 | RED: no checklist | owed (R1) |
| 04 changelog | `CHANGELOG.md` is what `tools/changelog.py --rev REV` writes, byte-stable across its own commit | g_changelog (unchanged) | yes | main | RED: stale (regenerated at the cut) | same; NOT RUN |
| 05 closure | every served book certifies or its failure is recorded; the closure audit (T1) green; OWED.md regenerated with teeth | `fn2/tools/certify.sh` (forge: `forge-certify.sh`), `fn2/tools/owed-export.lsp`, `certify-times.py` | yes (info + audit) | A-E, R2 | RED: 726 of 2,481 books uncertified at their keys | NOT RUN as a gate |
| 06 check | the §2.5 per-commit set | below: unit books, simulator, grammar fuzz, H's laptop set | yes | A-E, H | DRY (not run) | parts exist; NOT RUN as one set |
| 06b simulator (proposed) | eleven checkers; scenarios 1-20, F6, F8 and the fuzz scenarios: tiny exhaustive, then 100,000 concrete seeds on hbox | `fn2/sim/check-*.lisp`, `fn2/tests/sim-layer-*.lsp` | yes | A-E | n/a | 8 of 11 checkers exist; owed |
| 07 docs | every command the docs name exists as named | `tools/docs_check.py --check` on the swapped tree | yes | R3 | RED: specs/nntp.md's command table vs protocol-table.lisp | owed (R3) |
| 08 runpath | every process site in `host/` is listed; no Python in the shipped packaging | `tools/runpath_check.py` rewritten for fn2's host | yes | E8, R0 | GREEN at 945f625ad | owed (R0 rewrite) |
| 09 native | the carried natives on fn2's images through `Node`; S at 5,000 examples; the history hour | `run_surface --all --box hbox --target fn2` (E, S, H) | yes | H | RED (dry run refused); nightly: 109 ok / 11 not | NOT RUN (fn2 serves no family on a socket) |
| 10 throughput | the quiet cell and the drain-20261009 matrix published; red only on W13 | `tools/throughput_gate.py`, H's `perf:perf` (tools/load cells) | W13 only | H, R3 | runs exist, none quiet on a release closure | NOT RUN |
| 11 hostile | the native hostile workloads **plus** the four fuzzers | `tools/hostile_campaign.py`, H's `fuzz:fuzz`, the simulator's fuzz scenarios | yes | H, D2 | one family run (tls); every H F form PASS | NOT RUN |
| 12 tarball-linux | built from `git archive REV`, installed fresh, `test_release_tarball` OK with no skip, Debian 12 prints `fn 5.1.1 (REV12)` | `packaging/release-tarball.sh` (fn2's), `tests/test_release_tarball.py` | yes | E8 | never run | owed (E8) |
| 13 tarball-openbsd | the same in `cutbld`, plus `openbsd_smoke.sh` | as fn1 | per D1 | E8 | **MET on fn1 at af4fcb4d7** | owed (E8; D1) |
| 14 power-loss | backend barrier behaviour on the real file system, on the installed tarball | `tools/power_loss.py` on fn2's launcher | yes (or claim narrowed) | B, R4 | reproduction only, not on a release image | owed |
| 15 friends | the friend's node from the tarball | `tests/test_native_friends_feed` with `FN_FRIEND_FN` | yes | H, E8 | never run as a gate | owed (needs 12) |
| 15a witnesses | the image- and ACL2-needing `tests/*.sh` | `tools/witness_check.py` classes | carried ones | H, R0 | never run as a gate | rewrite or retire (R0) |
| 16 extract | `make extract-check` when REV's Makefile has it | `tools/extract/gate.py` | decide (R1) | R1 | **would run**: the target exists at 945f625ad | fn1's extraction; R1 retires it or names fn2's |
| 17 tag | print `git tag -a v5.1.1 ...` for ember's hand | g_tag | yes | ember | prints | same |

## The gates, one by one

### 01 version
Contract unchanged. `VERSION` reads `5.1.1-pre` until the cut commit sets `5.1.1` (§5.3).
- **Reads:** REV's `VERSION`, `planning/release-sequence.json`, and the `v*` tags (v1.0.0-v5.0.0 are
  prehistory).
- **Negative control:** `tests/test_release_sequence.py`.
- **Today:** RED by design. The dry run says "VERSION 5.1.1-pre is a pre-release of 5.1.1, never cut".
- **fn2:** the same driver. Separately, `fn --version` must print `fn 5.1.1 (REV12)`; gate 12 checks
  that.

### 02 tree
Unchanged.
- **Negative control:** `tests/test_cut_release.py`, which plants a tracked change.
- **Today:** GREEN at 945f625ad, in a scratch worktree.

### 03 fundamentals: the surface table proven
`planning/release-v5.1.1.md` has the shape of release-v6.6.0.md. Its rows are §1.1's assertions, split
into F-rows by R1.
- **What R1 changes:** g_fundamentals reads one more column, the evidence's closure identity (sha,
  profile, seeds, toolchain). A row is MET only when that closure is REV's for the paths the row reads.
- **The drivers behind the F-rows** are the rest of this matrix:
  - surface rows: H's run reports, `surface.json` beside `nightly.md`, with per-test outcome and family;
  - simulator rows: the 06b run's logs;
  - packaging rows: gates 12-15.
- **Reads:** REV's checklist and each row's evidence file.
- **Negative control (owed, R1):** a planted MET row whose evidence closure is another sha must turn the
  gate red. Today the gate checks only that the evidence path exists.
- **Today:** RED, "no planning/release-v5.1.1-pre.md". R1 writes it. The dry run looked for `-pre`
  because `VERSION` still reads that.

### 04 changelog
Unchanged.
- **Negative control:** `tests/test_changelog.py`.
- **Today:** RED, stale. It is regenerated in the cut commit (§5.3).

### 05 closure, and the assurance start
- **fn1's gate:** `tools/green_check.py --strict`. Every fn1 book is green at its digest.
- **fn2's contract** (§5.6 R1, §5.2 "the assurance start"):
  - every served book certifies, or its failure is recorded (certify is information);
  - the closure audit is green;
  - T5 is proved, or recorded unproved with diagnostics;
  - `fn2/docs/OWED.md` is complete for B-E with teeth.
- **Drivers:**
  - `fn2/tools/certify.sh` over the served closure plus every `fn2/tests/*-unit.lisp` (the foundation
    gate in FN2-SEAT-COMMON);
  - on forge, `fn2/tools/forge-certify.sh`, whose whole closure ran fresh in 175 s at -j 8;
  - `fn2/tools/owed-export.lsp`, which regenerates OWED.md;
  - `fn2/tools/certify-times.py`, for the one-minute rule's table.
- **Reads:** REV, the toolchain identity, and the box (forge or hbox; their toolchain identities are
  equal).
- **Negative control:** a book broken on purpose fails `certify.sh` by name. For the audit, a planted
  `(coerce ... 'list)` on a served path is red (owed with T1's audit tool).
- **Today, fn1:** RED. 726 of 2,481 books are not certified at their closure key on record toolchain
  8aeb1bea1896.
- **Today, fn2:** NOT RUN as a gate. The last export PASS on forge is the one recorded in 945f625ad's
  commit message. The release closure does not exist yet.

### 06 check: the per-commit set (§2.5)
fn1's `make check` is replaced by fn2's per-commit set. Its parts, each a driver:

| part | driver | reads | negative control |
|---|---|---|---|
| layer unit asserts | `fn2/tests/*-unit.lisp` via `fn2/tools/certify.sh` | REV, toolchain | the units' own teeth, e.g. `layout-teeth-unit.lisp` |
| tiny profile at its exhaustive bounds; 1,000 concrete seeds | `fn2/tests/sim-layer-a.lisp`, `-b.lsp`, `-c-sweep.lsp`, `-d.lsp` | REV, profile, seed range | `sim-fault-controls.lisp`, `sim-replay-controls.lisp`, `work-controls.lisp`, `liveness-controls.lsp` |
| grammar fuzz under the simulator (F) | `fn2/tests/grammar-fuzz.lisp` with `grammar-fuzz-oracle.py`; `grammar-gen.lisp` | REV, seeds | §2.4's wrong-parser controls (owed with D2's generator per wire) |
| H's harness units | the 23 laptop `unittest` modules in `h-continuation.md` (406 OK at 524e30869) | REV, Python + Hypothesis | the model mutation controls inside those modules |
| S forms of the touched families at 200 examples | `run_surface --family F --box laptop --target fn2` (nntp also under the simulator: `serves_sim.fn2`) | REV, examples × steps, `FN2_SIM_*` | each family's fake with its planted bugs |
| natives of the touched rows | `run_surface ... ` E form | REV, image | `run_surface`'s rules: a skip outside `intended-skips.json` is NOT RUN; a dead node fails by name |

- **Budget:** §2.5 sets an aggregate of 30 CPU-minutes. Allocating it from measured timings is still
  owed by H.
- **Today, fn1:** DRY (not run).
- **Today, fn2:** every part exists except the per-wire wrong-parser controls. They have not run as one
  set on one sha.

### 06b the simulator's release run (proposed: §5.2's simulator bullet has no gate of its own)
- **Contract:** all eleven checkers of ROUND2 §F.1. The twenty scenarios of §F.2, plus F6, F8 and the
  §2.4 fuzz scenarios, green in the tiny profile at their declared exhaustive bounds, and at 100,000
  concrete seeds on hbox, on the release closure.
- **R1 decides** whether this is gate 06's hbox half or a gate of its own.
- **The checkers behind the layer gates:**

| layer gate | checker | file | today |
|---|---|---|---|
| A | TRACE | `fn2/sim/check-trace.lisp` | exists |
| A | WORK | `fn2/sim/check-work.lisp` | exists |
| A | OWN | `fn2/sim/check-own.lisp` | exists |
| B | HISTORY | `fn2/sim/check-history.lisp` | exists |
| B | RECOVERY | `check-recovery.lisp` (b-durability.md §1: owed); `sim-recovery.lisp` is the recovery driver, not the checker | **owed (B)** |
| B | RECLAIM | `fn2/sim/check-reclaim.lisp` | exists |
| C | IDENTITY | `fn2/sim/check-identity.lisp` | exists |
| D | WIRE | `fn2/sim/check-wire.lisp` | exists (M1a uses it) |
| D | ACCOUNT | `fn2/sim/check-account.lisp` | exists (D7 3/n) |
| D | FAIR | joins with D7 4/n (d-machines-nntp.md) | **owed (D)** |
| E (D8) | CONSUMER | none yet | **owed (D8/E3)** |

`check-deadlock.lisp` is test logic for the PV geometry. It is not one of the eleven.

- **Scenarios per gate:**
  - A: 10, 12, 19;
  - B: 13-17;
  - C: the identity parts of 13, 17 and 19;
  - D: 1-6, 11, 18, 20;
  - E: 7-9 and F8.
- **Where scenario state lives:** in the owning layer's doc. This matrix names the gate, not the
  scenario's state.
- **Reads:** REV, profile (`tiny` or `concrete`), seed range, toolchain.
- **Negative controls:** the replay and fault controls above. A run that the mutation controls do not
  turn red is smoke.
- **Today:** 8 of 11 checkers exist. The 100,000-seed release run is owed.
- **What H has judged fn2 on so far:** M1a, the nntp S form under the simulator at dev 524e30869.
  1,000 examples × 50 steps gave 16,730 served replies with 0 disagreements and 15,741 interim replies,
  each named by its quest. WIRE then judged only 4 of the run's 17,776 connections: the session keyed
  its records by slot (H11). Laptop, Python 3.11.16, Hypothesis 6.170.13.
- **At dev 10e454049 (H13), both carriers, the same 1,000 × 50 run:**

  | carrier | target | served | disagreements | interim (POST D5 / D6) | WIRE opened / judged ok | time |
  |---|---|---|---|---|---|---|
  | simulator | `fn2` | 16,730 | 0 | 15,741 (713 / 15,028) | 17,776 / 17,776 | 105 s |
  | loopback TCP (M1b) | `fn2-native` | 16,730 | 0 | 15,741 (713 / 15,028) | 17,776 / 17,776, ENVELOPE ok | 298 s |

  Every opened connection has its own id and verdict: 0 refused, 0 unjudged. The A5r seat's laptop run at
  424f3f9ef gave the same native line.
- **The whole nntp family against the served node (H14, `--target fn2-native`, f794c78f3):**
  - **S:** PASS, as above.
  - **E:** 30 tests, 0 failures. 24 natives are owed host contracts, named (`init` with groups until D6;
    `store init`; the FNCT control socket; developer verbs). 3 intended skips, 1 opt-in skip, and the rfc3977
    fixture's hook is unset.
  - **F:** owed (the differential needs an fn2 owner with groups and a login).
  - **H:** owed (no observed nntp operations).
  - The run exits 3 (NOT RUN): there are no reds, but most of the family waits on D6.

### 07 docs
- **Contract:** `tools/docs_check.py --check` on the swapped tree, against the docs R3 rewrites.
- **Negative control:** `tests/test_docs_check.py`.
- **Today, fn1:** RED, "specs/nntp.md's served command table is not what books/protocol-table.lisp says
  now". fn2's command table comes from D2's grammar export (`fn2/tests/grammar-export.lsp`), so the
  check's source moves with R0.
- **Today, fn2:** owed (R3).

### 08 runpath
- **Contract:** every process site in fn2's `host/` is listed, and the shipped packaging has no Python.
- **Negative control:** `tests/test_runpath_check.py`.
- **Today, fn1:** GREEN at 945f625ad.
- **Today, fn2:** the R0 manifest rewrites the tool for fn2's host tree; owed.

### 09 native: the carried natives, the S forms at 5,000, the history hour
- **Contract (§5.2):**
  - the 87 black-box modules and the socket halves of the 33, run through the `Node` adapter on the
    release images (fn2's matrix: one image plus the DTN configuration), with executed assertions and
    skips reported;
  - retired modules listed with their replacement evidence;
  - `test_model_*` at 5,000 examples;
  - the history checkers' hour.
- **Driver:** `python -m fn2.tests.surface.run_surface --all --box hbox --target fn2` under `swarm-build`
  (the nightly script `fn2/tests/harness/hbox_nightly.sh`). It runs:
  - E: one test per carried native through `fn2/tests/harness/node.py`, plus the fixture hook
    `fixtures:fixture`;
  - S: every family's live state machine at the hbox cadence;
  - H: `history_drivers:history`, peering and bp convergence, and the consumer checkers over
    `from_observe`.

  F goes to gate 11 and R to gate 10.
- **Reads:** REV, the image set key, opt-ins, examples × steps, seeds, the memory ceiling (launch at
  64 GiB: fn1's connection capacity follows the cgroup), Python + Hypothesis.
- **Negative controls:**
  - `run_surface`'s rules, tested in `test_run_surface`: an unlisted skip is NOT RUN; an empty or
    timed-out result fails;
  - per family, the S fakes' planted bugs.
- **Today, fn1:**
  - The gate's dry run at 945f625ad was refused. Three modules' opt-ins are missing from
    `planning/release-native-gate.txt`:
    - bounds_join needs `FN_SPAN_REFERENCE_HOST`;
    - image_heap needs `FN_RUN_IMAGE_HEAP`;
    - reclaim_walk needs `FN_RUN_RECLAIM_RSS`.

    255 modules are listed.
  - Through H's adapter, the nightly of 2026-10-30 ran image set c14e9e8e (TREE_SHA d377d4559) with
    harness tree e495a7b55. 120 natives executed: 109 ok and 11 not. The 11 are 8 known fn1 reds,
    2 unprovisioned, and web S, harness-side and fixed in H9. Every S and F form passed, nntp S at
    5,000 examples. Not MET.
- **Today, fn2:** NOT RUN. `families.json` `serves.fn2` is empty; every family skips "layer D/E not yet
  serving". The nntp S form runs through the simulator (06b) until D9 serves a socket.

### 10 throughput (published; W13 gates)
- **Contract:** `tools/throughput_gate.py run` on a quiet box, on REV's image, and the drain-20261009
  matrix through tools/load, published as GAUNTLET's fn2 column.
  - A regression against `planning/throughput-baseline.json` is published, not red. That changes fn1's
    `check`, and R1 records the change.
  - W13's VmHWM ≤ 249 MB is red.
- **Drivers:** `tools/throughput_gate.py`, and H's `perf:perf` (`fn2/tests/surface/perf.py`: `ROWS`
  maps rows to tools/load cells, `UNMEASURED` names the rest).
- **Reads:** REV, the image, the box's quiet window (`--wait-quiet 1800`), the profile.
- **Negative controls:** `tests/test_throughput_gate.py`. For W13, a planted VmHWM over the bar.
- **Today, fn1:**
  - Throughput runs exist at f370581bf (2026-09-27), `quiet: false`. The baseline's release revision
    is bbf52159d.
  - H7b's R rows on image set c14e9e8e (`run-h7-perf/rows.json`).
  - None ran quiet on a release closure.
- **Owed by H, the rows with no tools/load cell:**
  - W7: an adapter to `tools.load.w7_extent`;
  - M5: bytes per isolated ack, with E3;
  - consumer wake p50/p95;
  - web per-page p99, with E7;
  - W3, W4, W5: the hostile connection-flood, auth-failure and slow-sender workloads.
- **Today, fn2:** NOT RUN.

### 11 hostile: the native hostile workloads plus the four fuzzers
- **Contract (§5.6 R1, §5.2):** `tools/hostile_campaign.py`, every family (malformed, header, body,
  connection, pipelining, transit, tls, bp), plus the grammar fuzzers. Fuzzers do not replace the
  hostile workloads.
- **Drivers:**
  - `tools/hostile_campaign.py`;
  - H's `fuzz:fuzz` dispatcher:
    - nntp: `fn2.tests.model.differential` (`--focus auth|feed` for tls_auth and peering);
    - operator and store_ops: `argv_fuzz`;
    - config_limits: `config_fuzz`;
    - web: `http_fuzz`;
    - consumer: `fncu_fuzz --with-fnct`, then `fnct_fuzz`;
    - bp: `bp_fuzz --with-tcpcl`, then `tcpcl_fuzz`;
  - the simulator's `fuzz-nntp`, `fuzz-fnct`, `fuzz-http`, `fuzz-tcpcl` scenarios (`grammar-fuzz.lisp`;
    D2 owns the generators).
- **Reads:** REV, the image, seeds and `--seconds` (600 s laptop, 3,600 s hbox, shared equally), and
  the corpus: fn1's nine reproducer sets.
- **Negative controls:**
  - every H fuzz driver takes `--plant P`, a planted defect the run must catch;
  - `hostile_campaign`'s oracle (a clean probe after the abuse);
  - §2.4's wrong-parser controls (owed per wire).
- **Today, fn1:**
  - The hostile campaign ran one family, tls, on image 6701d5753 (2026-09-26): 0 defects.
  - The other families never ran on one closure.
  - Every H F form passed on c14e9e8e in the 2026-10-30 nightly. H7c reran operator (5,145 calls),
    store_ops (4,911), tls_auth (1,348 compared) and peering (346 compared) with 0 new findings.
- **Today, fn2:** NOT RUN.

### 12 tarball-linux
- **Contract:** as fn1's, on fn2's packaging, rewritten by E8 and R0. `fn --version` on Debian 12
  prints `fn 5.1.1 (REV12)`.
- **Negative control:** `tests/test_release_tarball.py`. It refuses a tarball whose `--version`
  differs.
- **Preconditions on hbox today:** the glibc-floor runtime `sbcl-floor-runtime-2.6.8` is present.
- **Today, fn1:** never run; no cut directory on hbox has a `release/`.
- **Today, fn2:** owed (E8).

### 13 tarball-openbsd (per decision D1)
- **Today, fn1: MET at af4fcb4d7ac3** (VERSION 6.6.0, 2026-09-27; hbox
  `/tank/fn/scratch/cut-6.6.0-af4fcb4d7ac3/openbsd/out`). `test_release_tarball` gave OK
  (skipped=1, the glibc-floor case), and `openbsd_smoke: OK datasize=4194304 KiB`. This is the only
  gate 09-15 that went green on fn1, and its closure is not any fn2 closure.
- **Preconditions on hbox today:** `cutbld` is provisioned and stopped.
- **Today, fn2:** owed (E8). D1 decides whether the gate is optional. A kqueue backend is the likely cost.

### 14 power-loss: backend validation, kept distinct
- **Contract (§5.2):** one of three kinds of crash evidence, and the three are not mixed:
  - the model's crash-cut enumeration: scenarios 13-17 under the simulator's block device, gate 06b;
  - native process death: the kill sweep on the real host, A5's adapter with death cuts around
    acknowledge, execute, post and harvest (a-pool-host-sim.md, the A5 re-do item), run inside gate 09;
  - this gate: barrier behaviour observed on the real file system, on the installed tarball.

  If the backend evidence is deferred, the release claim is narrowed in the notes.
- **Driver:** `tools/power_loss.py` (rig, workload, index, cuts, summary) on fn2's launcher.
- **Negative control:** the gate requires `controls caught > 0` and 0 harness errors.
- **Preconditions on hbox today:** `sudo -n` works.
- **Today, fn1:** only the reproduction campaign ran (2026-09-26, hbox
  `/tank/fn/scratch/power-loss/summary.md`). Its `main` campaign had 0 violations, and its control
  campaigns caught their planted faults: the `all` row's 93 violations come from the no-barrier
  controls. The gate's own plan on an installed release image never ran.
- **Today, fn2:** owed.

### 15 friends
- **Contract:** `tests.test_native_friends_feed`, with `FN_FRIEND_FN` set to the fresh install's
  `bin/fn`, OK with no skip.
- **Driver:** the module is in H's peering E set (`families.json`), and the gate adds the tarball's
  `bin/fn`.
- **Today, fn1:** ok as a native in the 2026-10-30 nightly (peering E 10/10). It has never run from a
  tarball.
- **Today, fn2:** owed (needs 12).

### 15a witnesses (in the v6.6.0 checklist, not in `cut_release.sh`)
- **The `tests/*.sh` witnesses that need an image or ACL2:** cli_launcher, distribution, deploy_fresh,
  owner_feed_connection_host, and seven ACL2-world raw harnesses.
- **For fn2:**
  - the raw harnesses load fn1's books, so they retire in the natives record with their replacement
    evidence;
  - the launcher, distribution and deploy witnesses carry with the packaging.
- **Owner:** R0's manifest. R1 decides whether 15a gets a slot in the script.

### 16 extract
- **Today, fn1:** the Makefile at 945f625ad **has** `extract-check`. The gate would run
  `make extract-check`, not report SKIPPED.
- **The gate as written:** it checks fn1's extraction (`tools/extract/gate.py`, the N-version
  differential of fn1's books).
- **R1 decides:** retire the gate with fn1's tree at the root swap, or name fn2's counterpart.
- **Recommendation:** retire. fn2 has no extraction quest, and a gate that would run fn1's books
  against fn2's tree is red for the wrong reason.

### 17 tag
Unchanged: it prints the command, and ember tags.

## The 2026-10-30 dry run

The run: `tools/cut_release.sh --dry-run` from a detached scratch worktree at dev `945f625ad`, on the
laptop with hbox for the preconditions, 2026-10-30T12:03-12:09Z. The verdict line was
`VERDICT DRY-RUN v5.1.1-pre 945f625ad...: first red 01 version`.

| verdict | gates |
|---|---|
| GREEN | 02, 08 |
| RED | 01 (by design), 03 (no checklist), 04 (stale, by design), 05 (726 uncertified fn1 books), 07 (specs/nntp.md table), 09 (three opt-ins missing from the native gate file) |
| DRY with preconditions present | 10-15 |
| would run | 16 (target present) |
| printed | 17 |

Logs are kept on the laptop in `build/coordinator/fn2/lanes/h-quests/r1-dryrun-945f625ad/`.

This measures the fn1 path the script still drives. It is not fn2's readiness. That is the right-hand
column of the matrix, and it moves with D9 (the first socket), E8 (packaging) and R0 (the swap).
