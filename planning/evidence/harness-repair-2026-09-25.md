# Harness repair (lane harness-repair, 2026-09-25, PKT-176 to PKT-179)

Base: dev 483987b1 (baseline run in a detached copy of it). Laptop: darwin,
Homebrew ACL2 8.7_6 on SBCL 2.6.8, Python 3.14.7, every ACL2 through the
pool (six slots, 8,000 MB). hbox: the deployed image's gate
`/tank/fn/gates/qual-bbf52159-20260925` (image bbf52159), this lane's tree at
`/tank/fn/scratch/harness-repair/tree`, under `systemd-run --user --scope -p
MemoryMax=24G`. No book changed (host files and Python only): no farm run, no
PRF. The live node was not touched.

## Result

Every laptop test module at the lane head runs through `tools/test_budget.py`
in under three minutes: 154 modules, 807 s in all (dev: 153 modules, 1,552 s,
four killed at the budget and ten failing). The longest module is
test_store_fault_matrix, 51.4 s; the longest test after the split below is
5.7 s in test_bp_receive_process_crash (it was 24.1 s as one loop).
Two modules fail for a named reason only: test_ledger and test_current_view
report `planning/ledger.*` and `planning/current.md` stale, the generated
files this lane may not write (the deputy regenerates on merge; regenerated
here, both pass, then restored).

| module | dev s | dev | lane s | lane |
|---|---|---|---|---|
| test_anchor | 6.2 | FAILED 1 | 6.9 | ok |
| test_auth | 180.0 | killed at 180 s | 10.7 | ok |
| test_owner | 180.0 | killed at 180 s | 24.6 | ok |
| test_post | 180.1 | killed at 180 s | 15.4 | ok |
| test_triage | 180.0 | killed at 180 s | 1.4 | ok |
| test_deploy_gate | 28.9 | FAILED 1 | 28.8 | ok |
| test_feed_fence | 0.2 | FAILED 1+2 | 0.1 | ok |
| test_fn_cli | 0.6 | FAILED 6 | 9.1 | ok |
| test_native_bp_app_clock | 0.1 | FAILED 1 | 0.1 | ok |
| test_native_bp_channel_admission | 0.1 | FAILED 1 | 0.1 | ok |
| test_native_live_reconfiguration | 0.1 | FAILED 1 | 0.1 | ok |
| test_native_raw_scripts | 0.5 | FAILED 2 (C13) | 0.5 | ok |
| test_scale_gate | 18.1 | ERROR (class) | 21.1 | ok |
| test_twonode_gate | 34.9 | FAILED 1 | 33.4 | ok |
| test_bp_receive_process_crash | 23.3 | ok (one 23 s test) | 25.0 | ok, five tests, max 5.7 s |
| test_index_cache | 3.9 | ok forward, FAILED reversed | 3.7 | ok both orders |
| test_acl2_launchers | - | new | 1.1 | ok |

Full tables: `harness-repair-2026-09-25/laptop-before.txt`, `laptop-after.txt`
(and `.json`). The after table predates the process-crash split and the
index-cache fix, both rerun alone above.

hbox, native modules through the budget runner on the bbf52159 images
(`hbox-native.sh`, log `hbox-native-test_budget.log` `c4ac92170a0ec190`):
raw_scripts 9/9 (C13 retired), bp_app_clock, bp_channel_admission,
auth_admin_fidelity, owner 18/18, operator_verbs 22/22 ok; live_reconfiguration
10/11 and control 13/14 fail on C3 and C4 of qual-bbf52159 (a live `peer list`
answered; `operator post` with a supplied Path accepted under D32), unchanged
behaviour classified there, not a harness defect and not this lane's.

## What was wrong, classified

1. **Owner bridge (harness, PKT-176).** host/owner-host.lisp called
   fn-rcon-ocfg-io, fn-rclb-existing-action and the fn-octets stobj; only
   host/native/build.lisp included their books, so the bridge boot
   (tools/bridge_image.OWNER_FORMS) failed at `fn-owner-io`. The file now
   includes the three books itself (every loader gets the same world, no copy
   of the native list), and tools/build_lists_check.py `bridge_findings`
   applies its `included` rule to every bridge load list; its tooth is the
   pre-fix tree (three findings). Behind the boot, three more harness defects
   in the Python owner: `prov_post` read the store bridge's
   `fn-store-cfg`, never installed in an owner (NIL, every intent refused,
   every POST 441), now `fn-owner-prov-post` as the native owner calls;
   `feed_filename_decode` passed an octet list to the symbol reader (every
   restart with a journal died); a Message-ID conflict answered `refused`
   where the native owner passes `conflict` (the D25 line). Why dev hung
   instead of failing: the failed boot wrote an 81 KiB transcript to an
   undrained stderr pipe; the owner blocked, test_owner waited 300 s. The
   OwnerProcess stderr is a file now, and a failed image build raises its
   ACL2 error paragraphs, bounded.
2. **C13 (harness).** native_live_config_cache_raw loads the deployed
   fnn-owner-live-reconfigure-locked (peer-invite moved the body there);
   native_owner_bound_commit_raw stubs ACL2's file-first gate and gains the
   gate-refusal and malformed-answer cases.
3. **test_anchor's cryptography rule.** Its intent: the host has one Ed25519
   entry point, tools/crypto_host.py. tools/fn_verify.py is the independent
   verifier that must use other libraries and import nothing of fn's, so the
   rule was fixed, not the tool: it parses imports (v0_matrix only said the
   word), exempts fn_verify by name, and a new test holds the exemption's
   condition (nothing in tools/ imports it, it imports nothing of fn's).
4. **Launchers (PKT-162 completed, PKT-177).** Eleven launchers started a bare
   ACL2 (auth_secret, stx, run_reader, host_check, run_simulator, cert_alists,
   proof_artifacts, campaign model bridge, owner feed-connection check,
   feed-journal BookBridge, auth-admin fidelity) and interop_cbor took no
   slot. tools/acl2_slots.py is the one path (acl2_environment, the per-tree
   slot moved from run_store and held once per process however imported,
   run, popen, tree_slot). tests/test_acl2_launchers.py reads the code for any
   subprocess launch of an ACL2 program outside it (make check), with teeth
   over the eleven dev spellings and the launch path tested against a fake
   ACL2 (slot held and released, heap cap, certification environment). Blind
   spot: a program held in a variable not spelled `acl2`. Native images are
   outside the rule (hbox cgroup).
5. **C14** is retired by lane consumer-e2 at 95eeee4c (fixed in the
   generator); tests/test_native_consumer_e2.py was not touched here.
6. **Isolation and budgets (PKT-178).** test_budget.py: 180 s a module (was
   300), a test over 20 s makes its module over budget and is named, exit
   codes unchanged in meaning (a slow test in a failing module is 3);
   `--order reverse` runs each module last to first. Reversed, 25 laptop
   modules with class-level or process-wide worlds: test_index_cache's post
   test contaminated the shared store (fixed: it posts into a copy);
   test_proof_repl's SessionTests is a declared sequence (test_1..3 over one
   live session), recorded, not changed. Found separately: the machine's git
   configuration (commit.gpgsign) leaked into synthetic repositories
   (test_triage, test_evidence_manifests); frame_bridge's process-wide
   session is read only for stateless framing plus `publication_verdict`,
   which every caller passes its own bridge.
7. **Other stale harnesses at dev** (all assertions older than the
   behaviour; none changes an expected answer about fn's behaviour):
   bin/fn init lacked `profile` (python-store-f8), test_fn_cli's peer-list
   format (docs/operator.md), test_feed_fence's hand-built Owner,
   live_reconfiguration's `-deltas-over` source text, the two BP raw
   harnesses' arities (7281e76f, ec35b0d5), scale_gate's removed CERTPICK,
   deploy_gate and twonode_gate inheriting the farm host's ACL2 path.

## make check cost (PKT-179)

Measured step by step (`check-before.tsv`, `check-after.tsv`): 141.5 s to
100.7 s, outputs byte-identical to 483987b1's where compared. teeth_check
33 s to 12 s (ledger.load_tree built five times per process; now cached on
the bytes of every input); proof_cost 14.1 s to 4.9 s (closure edges
re-resolved 246,535 times; drift as a subset test); cite_check 17 s to 6 s
(one resolve per distinct token instead of 2.5 million stats);
harness_check 15 s to 11 s (one tree). What still dominates: every checker
process analyses the tree once (~5 s x six processes). Open: a cross-process
cache keyed by content.

## Not done

- No reverse-order sweep of the native modules; the qualification should
  add `--order reverse` for modules with class worlds.
- The deploy-gate dry run's fake run_store overlay lacks run_owner's newer
  imports, so its owner step falls back to the reader (the test tolerates
  it; the evidence says `violated`).
- ledger.* / current.md stale by construction (generated).
