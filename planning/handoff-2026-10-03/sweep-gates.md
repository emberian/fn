# SWEEP-GATES continuation (2026-10-03, wind-down)

## Branches (all pushed; the runner has all three)
1. lane/sweep-gates-prereq @ b0e1250b6: S009/S056/S127 (green_check `standing`) + S055 (check_steps: inputs changed during the run, hazards, git timeouts). Verified: tests.test_green_check + test_certified_claims + test_check_steps 65 OK on persvati; ledger --check 0.
2. lane/sweep-gates @ 35995846f (contains #1): S057/S063/S142, S061/S139, S062, S064/S140 (+ the deploy_fresh `--fn` fix), S058/S059/S060/S129, S126, S128, S130-S137, X10.
   Verified: test_image_set, test_build_native_host, test_install_script (Linux, persvati), test_native_distribution.sh; test_deploy_fresh.sh 40/40 on hbox with /tank/fn/scratch/operability-review/release/fn-6.6.0+f286c02041f1-linux-x86_64.tar.gz; production kill on hbox image set 77b7d258d, seed 3, judge 0 failures; reach --strict 0; native_program_check PASS; the two edited ACL2 test books load whole in proof_repl.
   Unverified: test_native_operator_campaign after the conflict-wording fix in 41c942bf8 (the rest of the module was green on hbox); S130/S131/S133/S134/S135/S136 native modules (they need a dev image; for the runner's batch).
3. lane/sweep-gates-checklane @ 24676b5d4 (base 355a5c843): CL19 (71910b6c5), CL03/CL06/CL07 (0da9b5753: 7 deleted host files + planning/host-parked.json with 85 parked), CL02 (e76f0e023), CL18 (76f611047), CL22, CL23, CL16/CL17, CL11 (WIP).

## In flight (harvest, do not rerun)
- CL11: proof_repl loads of tests/acl2/{bp-native-app-replay-bridge,raw-guarded-interface,store-config-generation}-tests on hbox after the must-fail-checked conversion. Local task output: /private/tmp/claude-501/-Users-ember-dev-fn/adb603dc-e723-4892-b9cd-9db2dc0e97a0/tasks/bzaphgmkk.output (sessions mf-<book>; stop them: `tools/proof_repl.py --host hbox stop mf-<book>`). If a body does not translate, fix the tooth (do not revert the conversion).
- Full check-lane at 0da9b5753 on persvati: log persvati:~/fn-gates/sweep-gates-checklane-check.log, or `tools/remote_check.sh attach persvati` from the checklane worktree. It predates CL02/18/22/23/16/17/11.
- check_scaffold local run (CL04), output .../tasks/besiy8c1g.output.

## Ledger (owner sweep-gates)
Ready: S009 S055 S056 S127 S057 S058 S059 S060 S061 S062 S063 S064 S126 S128 S129 S130 S131 S133 S134 S135 S136 S137 S139 S140 S142 X10 CL02 CL03 CL06 CL07 CL16 CL17 CL18 CL19 CL22 CL23. CL05 is a duplicate (the runner's world fix). CL11 in progress.
Open: S132 (a design item: the fixed 10 s control deadline; propose an expectedFailure plus a registry row), S138 (build-dtn.lisp: wrap the startup in fnn-native-startup like build.lisp), S141 (the second ld of host/page-read-host in build.lisp:365 / build-dtn.lisp:256, plus a build_lists_check duplicate refusal), CL01, CL04, CL08/CL09, CL10, CL12, CL13-CL15, CL20, CL21 (keystone_emit belongs to GENERATORS: coordinate), CL24, CL25, X17, X19.
Filed for others: X10A/X10B (reclaim-retention, ION workflow failures on dev's image).

## Next steps, in order
1. After the runner's merge, base on origin/dev. Run `make check-lane` once on a box and take the red list from that run.
2. CL11: harvest the REPL loads and fix any tooth whose body does not translate.
3. CL01 resource_contract: not a proof repair. Six books are RED from certify-20261001T100041Z-2748639 (owner-served-bound, public-exposure, consumer-wait and three more), and heap-reservation, connection-read-quantum, owner-obligation-state, deflate-inflate and owner-checkpoint-writer have no green at these bytes. One farm certify of those books at the current bytes, with its manifest archived (`tools/farm.py submit hbox --affected-by ...`, then `evidence_manifests.py add`).
4. CL08/09 witness_check: tests/test_native_payload_lifecycle_raw.sh needs a scenario-catalog row, or move it / retire it with a reason.
5. CL20 spec_cite: undefined names in specs/recovery-refinement.md:352 and allocation-turns.md:83-91 (parked F11/allocation names): re-cite them or mark them retired.
6. CL04, CL10, CL12, CL24, CL25: run each tool, take its first finding, and decide real vs stale.
7. CL13-CL15 depth: COMPLETE-BEFORE L12 owns these; coordinate, do not duplicate.
8. X17: profile ledger --write/--check (~10 min) and reach --baseline/--strict (~11 min). reach builds its Graph several times (each tests class builds one, ~40 s); cache the graph by content.
9. X19: route books/productive-transfer.lisp:30's raw clock compare through the clock-unit function.
10. S138, S141, S132.
Lessons: install.sh exits are two digits in the health header (`health exit=00`). FN_NATIVE_POST_FAULT has no `stop` action (SWEEP-STORE was asked). Never run `find` over /tank/fn/scratch.

## Harvested after wind-down
- CL11 REPL result: at least one converted book STOPPED at a must-fail-checked (raw-guarded-interface-tests: the DEFINTERFACE RG-KIND tooth's make-event body is refused by must-fail-checked). The conversion at 24676b5d4 therefore makes that book red on dev: fix forward by declaring `; must-fail-ok: <reason>` on teeth whose failure is an event-level error (not a translation), or by rewriting them; see .../tasks/bzaphgmkk.output.
- The check-lane at 0da9b5753 on persvati finished; its table is in build/lanes/sweep-gates-checklane/build/remote-check/persvati-check-lane.log.
