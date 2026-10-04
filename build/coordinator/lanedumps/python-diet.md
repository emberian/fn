# LANEDUMP python-diet (python-diet-4, wave 0/1, 2026-10-04) — agent a42811be0be2d3d44

Base origin/integrate/20261004@ec2c1b3da. Branch lane/python-diet (pushed).

## Landed on the branch
| sha | what |
|---|---|
| 0941b0a2f | build/coordinator/python-inventory-20261004.tsv: 180 units, 111,598 lines at d4e53323c; 168 keep / 9 dead / 2 superseded / 1 merge-into |
| b8bcae032 | 11 dead/superseded tools deleted (+6 own tests, 1 fixture, 1 baseline), host_defun_check folded into harness_check duplicate-defun (defstruct accessors; 2013 -> 2727 definitions, 0 findings); Makefile step + TOOLING_TEST_MODULES entry dropped; planning/retired-paths.json +20 |
| 4ab93f6c2 | merge lane/runtime-floor@8ac70017a (22 files, 1,418 lines, 74 Python), 0 conflicts |
| 93426404c | tools/runbooks/README.md names native_source_world, image_anatomy/, runtime_floor/ (the three tools with no in-tree doc) |
| fd4335285 | build/coordinator/queue/python-diet/t5-image-verb.md: T5 brief stub (not small) |

## Numbers (tools/*.py lines, git ls-files)
ec2c1b3da 111,718 -> 109,862 at fd4335285 (-1,856, -1.7%; -1,930 before runtime_floor's +74).
All tools/ files: 129,963 -> 129,479. **Target (-25%, ~27,900) NOT met**: every remaining unit
has a caller or a document; what is left needs decisions, below.

## Steps run (only those touched)
runpath_check --quiet: OK. cite_check --summary --strict: 0 load-bearing, exit 0.
secrets_check: 0. harness_check: duplicate-defun 0, signatures 0 (126,771 calls), raw-arity 0,
acl2-arity 0; entry-guards 22, test-stubs 4, waivers 2 are the base's (lints this change does not
touch). unittest tests.test_harness_check.DuplicateDefunTests: 9 OK. tooling-test (TOOLING_TEST_MODULES)
NOT run: the change only removes tests.test_process_supervisor from the list.

## The rest of the quarter needs decisions (lines; owner)
- T4 lints, waiting on generators (defkeystone 2 forms, defprotocol 1, def-entry 0): teeth_check 1,748,
  reach_check 1,438 (testing-setup), session_depth 600, host_shape_check 544, build_lists_check 426,
  payload_kind_check 300, must_fail_check 178, host_macro_order_check 117, ledger reader ~3,000 → ~8.4k.
- Measurement apparatus cited by planning/release-v6.6.0.md (keep until the release checklist drops
  them, or "evidence scripts by commit"): fundamentals 1,901, scale_curve 1,249, fixtures 952,
  throughput_gate 832, cost_gate 825, service_envelope 657, runtime_image 621, mux/msgid/rep_measure 989 → ~8.0k.
- tools/resilience/ 7,468 (ember: is the framework the test model going forward?).
- Labs kept by the python-diet-2 guardrails: inn_lab 2,961, deploy_gate 1,439, tcpcl_lab 645, labs 422 → 5.5k.
- Reader-client fitness: fitness 1,726, reader_clients 688, reader_clients_phase 697, thunderbird_drive 449 → 3.6k.
- T3 to Mini/DREGG (apps lane): fn_consumer 1,223, fn_agent 265, fn_client 921.
- D35: tools/extract/chicken.py 1,205 if the extracted build is plain SBCL only.

## Not done / handed off
- witness_check / test_roots_check / native_source_check: left separate on testing-setup's word.
- harness_check comments :1861/:1867 name native_bp_session_bank_raw.lisp / native_web_reactor_raw.lisp,
  renamed *_raw-mock.lisp on lane/testing-setup (not on my base); fix after that merge.
- depth_check/raw_depth_check already share code; cite_check/spec_cite_check answer different questions: not merged.

## Continuation
Next slice, if wanted: none mechanical left in tools/ without the decisions above.
