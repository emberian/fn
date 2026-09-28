# Python diet, 2026-09-28: inventory, classification and tranches

Ember (2026-09-28 00:06Z): "i wish we could delete more of the python :)
like maybe 1/3-1/2 of it overall.... shortening up ... tidying tightening
metaprogramming ... moving things to lisp."  This is phase 1: an inventory,
a class for every file, a plan in tranches, and T1 executed.  Lane
`python-diet`, base `batch/ay` at 9fd3e3c36.

Coordinates: the inventory is `tools/py_inventory.py`, run on hbox over a
`git ls-files`/`git log` dump of batch/ay 9fd3e3c36 and the 201
`build/lanes/*/LANEDUMP.md` files present at 2026-09-27 23:40Z; its outputs
and the class rules are in
[`evidence/python-diet-2026-09-28/`](evidence/python-diet-2026-09-28/)
(`inventory.csv` one row per file with every caller column, `inventory.md`
the tables, `classes.json` the rules).  Rerun:

    git ls-files > D/files.txt
    git log --format='@@%h|%cs|%s' --name-only -- '*.py' > D/log.txt
    python3 tools/py_inventory.py --dump D --csv OUT.csv --md OUT.md \
        --classes planning/evidence/python-diet-2026-09-28/classes.json

## 1. The inventory

194,153 lines in 675 tracked `.py` files on batch/ay:

| category | files | lines | what it is |
|---|---:|---:|---|
| tests | 231 | 73,939 | `tests/test_*.py`; 125 of them (41,983 lines) are image-gated native modules |
| other tools | 67 | 36,805 | gates, labs, bridges, measurement drivers |
| evidence | 243 | 21,320 | scripts already archived under `planning/evidence/` |
| lints | 33 | 19,533 | `make check`'s static checks and the registries |
| instruments | 70 | 18,620 | non-`test_` files under `tests/`: fuzzers, campaign, labs, fakes, children |
| build | 19 | 11,084 | certify, farm, proof_repl, certs, slots, test_budget |
| clients | 7 | 7,339 | fn_reader, fn_web, fn_client, fn_agent, fn_consumer, fn_verify, nntp_session |
| store | 4 | 5,074 | run_store, run_owner, checkpoint, synth_log_store |
| docs | 1 | 439 | site/build_site.py |

The brief's "other tools 57,111 in 313 files" is these tools plus the 243
evidence scripts.  Per file the CSV gives lines, category, callers by kind
(Makefile, shell, packaging, CI, Python import, Python path or subprocess
string, tests, Lisp, a whole directory named as an overlay, docs, planning,
evidence, lane dumps), last commit, date and lane (the subject's prefix),
first date, and reach: the closure of code-caller edges from `make check`'s
recipe, the native modules (cut_release's rule), `make test`'s discovery,
the release scripts and the Makefile.  Comments are dropped before a Python
file counts as a caller; strings are kept, because subprocess calls are
strings.  Reach is generous on purpose: a reached file may never execute,
but an unreached file with no caller is executed by nothing in the tree.

Two things the inventory alone found:
- **The retired Python host is still load-bearing.**  `tools/run_store.py`
  is imported by 18 tools and 60 test files, and 7 native modules still
  take something from it: the exit constants (`EXIT_OK` 28 uses,
  `EXIT_FAULT` 8, `EXIT_REFUSED` 6, `EXIT_UNCERTAIN` 3), the ACL2 output
  parsers (`acl2_*`, 18) and `metadata` (6, a content identity derived
  through a Python-bridge ACL2 session).  The same three exit numbers are
  also written out by hand in 7 other files.
- **Nineteen files have no code caller and are not discovered tests**:
  the five T1 files below, and fourteen measurement or one-shot rewrite
  tools that lane dumps still name (T1b).

## 2. Classification

Rendered by `--classes`; per tranche, with what each removes (an ARCHIVE
moves a file and removes nothing):

| tranche | class | files | lines | removed |
|---|---|---:|---:|---:|
| T1 | DELETE | 2 | 716 | 716 |
| T1 | ARCHIVE | 3 | 307 | 0 |
| T1b | ARCHIVE | 14 | 2,530 | 0 |
| T2 | MERGE (native modules, harness) | 121 | 38,955 | est. 3,950 |
| T2 | KEEP (twonode_gate, re-plumbed) | 1 | 2,239 | 0 |
| T2b | RETIRE-WITH-DEPENDENCY (v0 matrix) | 6 | 9,896 | 9,609 |
| T3 | RETIRE-WITH-DEPENDENCY (web clients) | 6 | 7,094 | 6,696 |
| T3 | MOVE (to Mini/DREGG) | 4 | 1,399 | 1,399 |
| T4 | MOVE-TO-LISP | 24 | 15,904 | 10,985 |
| T5 | RETIRE-WITH-DEPENDENCY (Python host) | 97 | 30,242 | 25,588 |
| - | KEEP | 397 | 84,871 | 0 |

### DELETE and ARCHIVE (T1, T1b)
Each T1 claim cites the file that preserves what the tool established:

| file | lines | class | preserved by |
|---|---:|---|---|
| tools/live_service.py | 576 | DELETE | evidence/live-52eb0db-2026-09-20.md (its one run, unit in full); superseded per evidence/release-product-2026-09-26.md:158 |
| tests/index_measure.py | 140 | DELETE | nothing to preserve: lanes/HANDOFF-w3-index-cache.md:198 records it NOT RUN; it times the Python bridge |
| tests/identity_differential.py | 97 | ARCHIVE | lanes/HANDOFF-w9-digest.md:141 (100 cases equal) |
| tests/perf/native_consumer_poll_cost.py | 105 | ARCHIVE | evidence/native-consumer-poll-cost/b074-v4.md |
| tools/log_barrier_probe.py | 105 | ARCHIVE | evidence/w6-log-core-2026-09-27.md:107 |

T1b, archived when the lanes naming them have closed (their dumps name
them today): heap_peak_measure, owner_post_measure, repl_census,
lift_stobj_tests, thread_stobj, mux_measure, scale_probe,
power_loss_openbsd_{reclaim,reopen,tally}, profile/{control_quanta,
prof_control}, rep_measure, msgid_measure (its fixture half first: fixtures
and two tests import it).

The two named questions:
- **`tools/v0_matrix.py` and `tests/test_native_v0_matrix.py` are the
  2026-09-24 v0 scoreboard's driver** (planning/v0-scoreboard.md,
  planning/v0-matrix.json).  Not a T1 delete: `tools/check_scaffold.py`
  imports its validator, so `make check` reaches it, and 3 tools and 5
  tests name it.  It is superseded by `tools/fundamentals.py` (F1 to F8
  on one image), which is on `lane/release-machinery` and not on batch/ay.
  T2b: when fundamentals lands, drop check_scaffold's import, retire the
  matrix, its two tests, `native_peering_matrix_slice` and its test, and
  half of `reader_clients_phase` (9,609 lines).
- **`tools/inn_lab.py` is not retired.**  Its evidence is under
  `planning/evidence/inn-lab-*` and `inn-reader-*`, but it last ran on
  2026-09-26 against the native image (inn-lab-b4b343d51-2026-09-26.md),
  `tools/labs.py` runs it, and it names no Python-host tool.  It is the
  INN interop instrument: KEEP.

### MERGE (T2): one native harness
121 image-gated modules, 38,955 lines.  66 start a process with their own
`subprocess.Popen`; 46 use `tests/native_process.py` (bounded stop and
announcement only).  Besides those, three tools start nodes their own way:
`tools/v0_matrix.py` (452 lines of harness-shaped definitions),
`tools/deploy_gate.py` (136), `tools/twonode_gate.py` (115); plus
`tests/test_bp_node_native.py` `start_node` (179) and
`tests/test_native_v0_matrix.py` `start_node` (31).  Measured by function
(the CSV's `harness_def_lines`: definitions named start/stop/launch/spawn/
wait_for/connect/client/send/command/reply/port/env/store-init/setUp/
tearDown...): 4,854 lines across the 121 modules.  The largest:
test_bp_fragment_node_native 293, test_native_peer_pull 225,
test_fn_web_native 224, test_bp_node_native 179, test_native_hybrid_author
126, test_native_operator_verbs 125, test_native_peering 124.

`tests/native_harness.py` (replacing native_process.py, the node half of
native_env.py and native_profile_fixture.py), about 900 lines:
- `Node(image, profile, env)`: `store init` through the image (the native
  store makes the fixture), start in its own process group, record the PID,
  `announcement()` bounded as native_process does today, `stop()` returning
  the exit status, `kill(cut)` setting the fault variable for a model cut
  point and asserting the process died at it.
- `pair(a, b)`: two peered nodes (peering, consumer exchange, twonode_gate).
- `session()`: one NNTP client over `nntp_session`, bounded reads.
- `Outcome.ACCEPTED/REFUSED/UNCERTAIN/FAULT`: the exit statuses in one
  place, named from the native host's table, replacing run_store's
  constants and the 7 hand copies; `assert_outcome(result, outcome)` never
  collapses uncertain into refused.
- `acl2_value(text)`: the one parser of the image's printed values (today
  run_store's `acl2_*`), so no native module imports run_store.
- `identity(msgid, payload)`: asked of the image; if the image has no verb
  for it, that is an open registry item, not a Python function.
Requirements other lanes' obstructions add (their LANEDUMPs, 2026-09-28
00:20Z): drain stdout and stderr from start (feed-queue: the peering
harness's undrained PIPEs blocked a node past ~1,000 transits), print the
node's stderr when startup fails (feed-queue: an owner refusal visible only
on stderr), export the announcement grammar including the TLS line
(fitness: `LISTENING` with no space hung a driver), and named test
profiles whose reservation fits the test scope (feed-queue, fitness).
Estimate: 4,854 - 900 = **about 3,950 lines** removed, by function; inline
setup code not in a named definition is not counted, so this is a floor.
Conversion in groups of 10 modules, each group's natives re-run on hbox
through `tools/hbox_native.sh`.

### MOVE-TO-LISP (T4)
- **The ledger's non-evaluating Lisp reader** (`tools/ledger.py` Reader,
  `read_forms`, `analyze_book`, `load_tree`) has 14 reusers:
  harness_check, host_shape_check, host_translate_check,
  payload_kind_check, proof_profile, session_depth (subclasses it),
  teeth_check (Reader); certified_claims, check_scaffold, current_view,
  spec_cite_check, teeth_check, harness_check (load_tree); certify_books,
  certs, labs (analyze_book).  Three more tools carry their own reader:
  reach_check (`read_sexp`), native_program_check (`tokenize`),
  frame_bridge (`read_form`), and tests/fuzz_nntp.py has a fourth.  Beyond
  reading, ledger re-implements ACL2 (beta reduction, `cond` expansion,
  `defrecord` expansion, a literal decider, theory membership).  The
  replacement is a world dump from the image (theorem formulas, event
  books, macro expansions, theories) that the counts read; ~60% of
  ledger.py goes.
- **Lints the generators make structural**: defkeystone (lane/defkeystone)
  retires must_fail_check, reach_check, teeth_check and their tests, and
  shrinks current_view; defprotocol (lane/defprotocol) retires
  session_depth, the fuzzer's grammar and reader, and docs_check's command
  half; definterface (G7) then extraction (G2) retire payload_kind_check,
  host_shape_check, host_defun_check, host_macro_order_check,
  build_lists_check and harness_check's acl2-arity half.  10,985 lines.
- **Python deciding what ACL2 owns** (AGENTS.md forbids it outright):
  1. `tools/synth_log_store.py:87-93` recomputes subject and obligation
     identities (labels, length prefixes, SHA-256) and writes FNLG frames
     with SHA-256 trailers and CBOR, reimplementing books/identity.lisp
     and books/store-log.lisp (it checks itself against templates, which
     is a differential, not ownership).  A fixture generator: T4, into an
     ACL2 program the image runs.
  2. `tools/run_owner.py:230`: `fn-owner-config-generation + 1` is the
     staged generation, computed in Python.
  3. `tools/run_store.py:1007` frames the anchor record (prefix plus
     SHA-256 trailer) and `:989` splits the trailer to compare; integrity
     trailers are ACL2's.
  4. `tools/scheduler.py:207` frames decision records the same way.
  5. `tools/fn9p.py:134-273` frames 9P messages in Python for a served
     view (experimental).
  6. `tools/bundle_bridge.py:61` derives the staging and duplicate key as
     SHA-256 of the identity octets; `tools/media.py:122,127` names files
     by SHA-256 of a bundle id (a transport name, stated as not an
     identity; listed because the duplicate key is compared).
  2 to 6 are in the Python host and go with T5; 1 is T4.  Not violations:
  `tools/fn_verify.py` (an independent verifier by design) and
  `tools/roughtime.py` (a client of an external protocol that hands the
  fields to ACL2).

### RETIRE-WITH-DEPENDENCY (T5): the Python host
The 2026-09-19 direction was "retire the Python host"; what remains is 20
host tools (run_store, run_owner, frame_bridge, bridge_image, run_reader,
run_bp_ingress, run_bp_receive, checkpoint, scheduler, workflow_journal,
workflow_bridge, receipt_journal, receipt_bridge, bundle_bridge, feed_wire,
stx, fn9p, fn_native, auth_secret, media), the gates that drive it
(deploy_gate and scale_gate name no native image) with their fakes and
tests, tests/bench, transcribe_check, and 38 test modules that import a
host tool and name no native image (test_store*, test_owner, test_post,
test_reader*, test_feed*, test_workflow*, test_receipt*, test_scheduler,
test_checkpoint, test_media, test_fn9p, test_stx, test_bp_receive*,
test_acl2_bridge, test_host_boundary, test_index_cache, test_anchor,
test_provenance, test_served_differential ...).  25,588 lines.  What each
dependent needs, and its replacement:
- `tools/transcribe_check.py` reads the Python host's Store methods (its
  "store initialize" entry still uses `Store.initialize` as the model,
  flip-cleanup P9, log-leftovers P2).  `tools/native_program_check.py`
  already transcribes the native host's programs; transcribe_check
  retires with run_store, and the make check step goes.
- The 7 native modules: exit constants, `acl2_*` and `metadata` move to
  the harness (T2), so T2 lands first.
- Fixtures: the native store makes them (`store init` and POST through
  the image); synth_log_store is the one fixture that bypasses the owner
  and is T4.
- The model: the ACL2 model IS the model; the Python host is not a
  reference for anything the ACL2 test books do not already check.
- Interop labs stay and are ported, counted at 30%: tests/bp-dtn7,
  tests/ltp, test_bpa_dtn7 (their run_bp_ingress driver half goes), and
  tests/campaign/campaign.py, child.py, model_images.py (the Python-host
  arm goes; native_cuts and native_production_kill carry the campaign;
  model_images is split).
- `host/store-host.lisp` and the other bridge host files lose their last
  callers here; that is a host-Lisp deletion for the same lane.

### KEEP
Instruments that refute claims: the fuzzers (tests/fuzz_nntp.py less its
grammar), power_loss and power_loss_openbsd, twonode_gate (re-plumbed on
the harness), hostile_campaign, the differentials (image, served, source
corpus), the interop labs (inn_lab, tcpcl_lab, the dtn7 and ION labs),
proof_repl, farm, certify_books, certs, acl2_slots, test_budget,
fixtures, codec_golden (the control G1's codec seams will need), fn_client,
fn_verify, nntp_session, node_probe, runpath_check, cut_release's tools,
the registries (ledger's counts, next_id, merge_registry), and the 243
archived evidence scripts.  gate_reap has no caller but its own test; it
is an operator tool (docs/proofs.md), kept unless ember says otherwise.

## 3. The tranches

| tranche | what | depends on | removed |
|---|---|---|---:|
| T1 | no-caller deletes and archives, one commit per file | nothing | 716 |
| T1b | 14 measurement tools archived | their lanes closing | 0 (moved) |
| T2 | tests/native_harness.py, then 121 modules in groups of 10 | nothing | ~3,950 |
| T2b | the v0 matrix | fundamentals.py landing (lane/release-machinery) | 9,609 |
| T3 | fn_reader, fn_web and their tests; fn_agent, fn_consumer to Mini/DREGG with Astra's packet reply | lane web-native; Astra | 8,095 |
| T4 | lints shrink as defkeystone/defprotocol/definterface land; the Lisp reader becomes a world dump; synth_log_store into ACL2 | lane/defkeystone, lane/defprotocol, G7 | 11,203 |
| T5 | the Python host, its gates, benches and tests; transcribe_check | T2 (the native modules' imports) | 25,588 |
| | **total** | | **~59,160** |

59,160 of 194,153 is **30.5%**: short of ember's third (64,718) by about
5,500 lines, far from half (97,077).  T2 is a floor and T4's fractions are
estimates; T5 and T2b are whole files.  What would close the gap, for
ember to decide:
- **Evidence scripts by commit, not by copy** (21,320 lines, 243 files):
  an evidence record already names its commit; the script is recoverable
  as `git show REV:path`.  Taken together with the plan: 80,480, 41.5%.
- **Test modules as generated instances**: after defkeystone the Python
  side of a keystone test is a registry row, and the 58 kept non-native
  test modules shrink with the lints they test.  Not estimated here.
- fundamentals.py itself adds Python (tools/fundamentals/*.py); count it
  against T2b when it lands.

## 4. T1, executed

One commit per file on lane/python-diet, each quoting the file's
inventory row; nothing a live lane's worktree or unmerged branch uses
(checked: the 31 lane branches ahead of batch/ay and touched in the last
30 hours name none of the five in code; no worktree has them modified):

| commit | file | lines |
|---|---|---:|
| 722071e34 | delete tools/live_service.py | 576 |
| f5a34904d | delete tests/index_measure.py | 140 |
| fa9c723fe | archive tests/identity_differential.py to evidence/w9-digest-2026-09-20/ | 97 |
| 98055933b | archive tests/perf/native_consumer_poll_cost.py to evidence/native-consumer-poll-cost/ (performance-2026-09-26.md:310 updated) | 105 |
| 6ceb99459 | archive tools/log_barrier_probe.py to evidence/w6-log-core-2026-09-27/ | 105 |

`make check-lane` on hbox (swarm-build, git clones of batch-ay's
repository with the lane fetched from a bundle): base 9fd3e3c36
(`/tank/fn/scratch/python-diet/check-base.log`) and the T1 head plus
this plan, 4c6264472 (`check-lane.log`), each 36 steps, 35 ok. The one
red in both is `host_check --load` NOT RUN (exit 2, no FN_ACL2 in the
shell), so the step table is identical before and after.  The lane-head
timings are longer because hbox was at load 66 to 78 during that run.

## 5. Tool obstructions other lanes named (rows of this inventory)

Collected from the `## Obstructions and asks` sections present at
2026-09-28 00:20Z; each is a Python tool in the table above:
- `tools/next_id.py`: `claim` exists only on lane/tooling-leftovers, and an
  unknown subcommand prints the listing and claims nothing (arena-store-2,
  feed-queue).
- `tools/certify_books.py` and `tools/proof_repl.py` read "HARD ACL2 ERROR"
  anywhere in a log as failure, so an `er hard` inside a passing must-fail
  is a false red (defkeystone).
- ledger, teeth_check, must_fail_check and reach_check re-analyse the whole
  tree in separate processes, about 8 minutes a snapshot on hbox, and
  `FN_LEDGER_TREE_CACHE` is keyed by module name (defkeystone);
  defprotocol asks for a call graph through macros over the same reader.
  Both are T4's case for one world dump instead of four readers.
- `tests.test_reach_check.SubjectRuleTests` has 2 failures on batch/ay
  (defkeystone).
- proof_repl: `send-range --no-sync` runs the remote copy after a local
  edit (defprotocol); `send-range` skips top-level `local` forms silently
  and `:ubt!` resync is unreliable (web-native); `--host` forces the
  toolchain ACL2 with no `--acl2` (extract-2); `--source-deps` leaks local
  theory into step counts (feed-queue).
- fixtures: postmeasure does not check `store init`'s exit, and the
  registered syn100k-2k/syn1m-2k recipes cannot initialize on batch/ay
  (extract-2, fitness); ask: `fixtures.py check` in the batch routine.
- `tools/wait_for.sh --host hbox` fails where plain ssh works (feed-queue);
  `tools/remote_check.sh` is named by closeout-common and exists on no base
  (arena-store-2, openbsd-datasize, this lane).
- `tests/test_cut_release` needs a git identity on a box without one
  (openbsd-datasize).
