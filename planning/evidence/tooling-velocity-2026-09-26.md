# tooling-velocity (2026-09-26): lanes stop losing runs to the tools

Brief: build/coordinator/queue/done/w4-tooling-velocity.txt (wave 4, lane 14;
mandate section 14). Branch lane/tooling-velocity from dev 17ff24aa. Ids:
PKT-445, PKT-446. No PRF, requirement or scenario: this is harness work; no
ACL2 decision moved. The one book byte change is two comment lines in
tests/acl2/store-checkpoint-reader-tests.lisp (item 9), certified on persvati:
run-20260926T102720Z-3f5b, certify-20260926T102757Z-359145 (1 certified, 21
installed from the cache, no book over 10 s).

Evidence directory: tooling-velocity-2026-09-26/.

## What landed, by leverage

1. **PKT-306, DTN images through hbox_native.sh** (c085b45a). `--images`
   takes developer, production, dtn, dtn-developer; each image gets
   tools/runbooks/hbox-image-build.sh's (profile, session script, image)
   triple. A DTN image adds the dtn profile's roots to the certified set
   (books/records-concrete is a dtn root and not a default one) and runs
   `proof_artifacts.py acquire/validate --profile dtn` before the build.
   `--env NAME=VALUE` exports for the test modules; with dtn-developer built
   and dtn not, FN_NATIVE_BP_HOST defaults to the dtn-developer image.
   Dry run: `hbox-native-dry-run-dtn-developer.txt`. Real run on hbox,
   commit c085b45a, `--images dtn-developer`,
   tests.test_bp_service_native (17 tests OK) and tests.test_bp_contact_native
   (2 OK), status 0 (`hbox-native-dtn-developer-run.txt`):
   fn-host-dtn-developer `46fffc84...`, core `70bbd4b6...`,
   native-build-dtn-developer.log `93ae7958...`,
   test_bp_service_native.log `e4063a9c...`, test_bp_contact_native.log
   `e75c52d9...` (all sums in that file). The brief's
   `tests.test_native_bp_node` does not exist; `tests.test_bp_node_native`
   runs on the non-DTN developer image, so the two DTN-image modules ran.
   Test: tests/test_hbox_native.py (dry-run, no ssh).
2. **PKT-346, sessions belong to a lane; a slot wait names its holders**
   (9b929a55, bfac424d, 49e24731). proof_repl: `--lane` (default $FN_LANE,
   build/lanes/NAME, or persvati's ~/fn-gates/NAME-repl), `--idle-seconds`
   (default 7200 s: longer than a 3400 s farm wait or a 5400 s hbox_native
   run between two sends, so a working lane is never cut; an abandoned
   session frees its slot within two hours), the ACL2 group in state;
   `list` (lane, age, idle, deadline; `--root TREE` for other trees);
   `reap [--lane NAME | --older-than S] [--root ...] [--dry-run]`: the
   session's own stop first, then only the server PID and ACL2 group its
   state names, each checked to still be that session's process.
   acl2_slots: `FN_ACL2_SLOT_WAIT` / `wait_seconds` / `tools/acl2
   --wait-seconds` (exit 75) refuses naming every holder; the minute line
   names them; unset stays unbounded. Tests: tests/test_acl2_slots.py (new),
   tests/test_proof_repl.py OwnershipTests.
   **persvati** (list over all 146 ~/fn-gates trees,
   `persvati-proof-repl-list.txt`): 24 non-dead sessions. Reaped 16 whose
   lanes are merged on dev (consumer-e2-2 45ab031c, k0-corollaries a361b6a8,
   marker-required 5cfd0519, operator-walk 4a3f88d6, peer-keys e13ece8e,
   peer-pull 009c250f, reclaim-d13 c8211574, reclaim-lifecycle 8a9fa487 and
   3ba3f9c6, rep-wave-c eeaf759a, status-join fbbb6622): cra, k0c, bsf
   (stale socket), owfc, ownop, ks2, pull, na, nr, rr, sr, rclp,
   store-reclaim-pack, store-reclaim-pack-tests, shb, sj
   (`persvati-proof-repl-reap.txt`; all stopped through their own socket).
   Left for the deputy (live lanes in WAVE-STATE): keys-and-accounts-repl
   ka-ks, ka-nop, ka-pcb, ka-pinv; peer-feeds-repl pfpull; reader-2-repl
   r2enr; fa-cfg (slot-015, appeared after the list); opv-mirror2 osb and
   ovlog (stale sockets, lane not identified; left).
3. **PKT-345, an unbalanced form is located** (a5f7717e). parse_at raises
   `unbalanced: FILE:LINE, form starting at FILE:LINE never closes`; texts
   carry their file (a joined model text reports the book).
   `--balance FILE...` is the lane-side reader check (with the first
   column-0 form inside the unclosed one); `farm.py submit` runs it over
   books/, host/, tests/acl2/ (1,026 files, 1.6 s) before any rsync. Two
   reader defects fixed on the way: a string `"("` compared equal to the
   parenthesis token, and an unterminated `|symbol|` looped from offset 0.
4. **PKT-305, tooling-test** (351121ff). Examined, not raised: 29 modules
   take 170 s on the laptop (`tooling-test-budget.txt`); the cost is
   real-tree reads (certify_runner 39 s over 49 fake-ACL2 runs, green_check
   34 s with four command-line runs over every manifest at 6-7 s each,
   ledger 16 s with a cold tree analysis, reach_check 12 s). The target now
   runs tools/test_budget.py (per-module process, 180 s a module, 20 s a
   test, distinct exits) over all 29, the four missing modules included.
   tests/test_build_native_host.py: each of the four markers refuses the
   build, naming the line; a clean log builds.
5. **PKT-312, spec citations** (65900773). tools/spec_cite_check.py in
   make check: every backquoted single `fn...-...` name in specs/*.md and
   docs/*.md resolves in tools/ledger.py's tree. Visible rules: templates,
   one-segment names (prefixes, magics, programs), `-vN` tags. At 17ff24aa:
   5,074 citations, 4,541 defined, 184 by rule, **349 unresolved citations
   of 254 names**, more than this lane could repair: each is listed by name
   and file under PKT-446 in tools/spec_cite_exemptions.json (no silent
   baseline: the summary counts them, `--strict` fails on a new one or an
   entry no longer cited). PKT-312's four `fn-bpn-limits-compose` citations
   were already repaired (6e6acb1f).
6. **PKT-117, examined** (da9defed). No book or test book `ld`s a host
   file. Six test books `(include-book "../../host/X")`, which
   certs.closure() already follows (bp-node-host-tests' key lists
   host/bp-node-host); provenance-tests names host/store-host.lisp only in a
   comment. store-host.lisp is `ld`ed by the store bridge, whose image key
   (tools/bridge_image.py) follows `ld` and is tested. **Consequence: the
   certification key is unchanged; no cached certificate is invalidated and
   no recertification is owed.** A test pins the behaviour.
7. **PKT-285.** `make check-lane` already runs
   `tools/evidence_manifests.py check` (it is `make check` under
   FN_LANE_CHECK, which only redirects the generated ledger files). Proposed
   for build/coordinator/merge_lane.sh (not edited), before the merge:
       (cd "$W" && python3 tools/evidence_manifests.py check) || { echo "EVIDENCE: a cited run has no committed manifest in $W"; exit 4; }
       ssh persvati "python3 ~/fn-gates/tooling-velocity-tool/tools/proof_repl.py reap --lane $L --root ~/fn-gates/$L-repl" || true
   (the second needs a persvati tree holding this lane's proof_repl.py;
   ~/fn-gates/tooling-velocity-tool/tools/ holds it now.)
   `farm.py certify-in-place` (design, not built): `farm.py certify-in-place
   hbox --remote-root R --roots-profile default|dtn` runs, in an existing
   gate root, `certs.py install-partial` then `certify_books.py
   --incremental` over `proof_artifacts.py roots --profile P` under
   swarm-build, writes the run's farm record (run id, status, log) like
   `submit`, and `wait` harvests the manifest into
   planning/evidence/manifests/. The operator-walk failure (160 roots,
   preflight refused three times, by hand rc 0) cannot be diagnosed now: it
   predates friction-tools' stderr surfacing and no log kept stderr. The
   next occurrence prints exit code and stderr cause first.
8. **PKT-258, launcher rule** (6124b2b4). unpooled_launches() resolves
   argv through the module's assignments and judges the program element by
   every value assigned to each name in it. **Finding:** the resolution
   flagged tools/run_store.py:415 (`command = [str(bridge_image.resolve_acl2(env))]`),
   which is pooled by an explicit `_acquire_slot =
   acl2_slots.acquire_tree_slot` call earlier in the same `__init__`; the
   old rule passed it only because it could not see the argv. The rule now
   treats a function calling acquire_tree_slot (or an alias, or a module
   function calling it) as pooled. No launcher escapes the pool.
9. **PKT-341, prover refusals labelled** (0e238d72). `; teeth:
   prover-refusal REASON` in the comment block directly above a must-fail;
   tools/ledger.py (Book.prover_refusals, totals, ledger.md row) and
   tools/teeth_check.py --summary count them apart (1,588 must-fails, 2
   labelled). Audit (comment scan over every must-fail): the two are
   rep-wave-d-3's in store-checkpoint-reader-tests (2^64-octet length
   width; the stobj recogniser); checkpoint-compaction-preservation-tests'
   refusals each have an evaluated counterexample beside them. A static
   tool cannot find a must-fail whose comment does not say it has no
   witness: a teeth audit of must-fails without a paired assert-event
   counterexample is PKT-445 (c).
10. **PKT-218/248.** C3 and C4 repaired to the selected contract, each
    keeping the regression it detects. C3 (test_native_live_reconfiguration):
    a live `peer list` is answered by the running owner (exit 0) and shows
    exactly the peer just added, and the pinned reader's `LIST ACTIVE` is
    still what it was (the old expectation, refused at the lock, predates the
    live query verbs). C4 (test_native_control): a well-formed supplied Path
    is accepted under D32 and stored with exactly one Path line,
    `fn.example.invalid!elsewhere!not-for-mail` (the node's identity
    prepended, the tail kept); a Path that is not a path (`not a path`) is
    still refused and absent, as are the address-less From and the wrong
    Message-ID. Native on hbox, the production image of this tree
    (`fn-host` `35c680c8...`, /tank/fn/scratch/tooling-velocity/native-c3c4):
    live_reconfiguration 11 tests OK (log `ec4d6356...`); control 14 tests,
    1 failure, 3 skipped (developer selectors, correctly), log
    `fc4a1c8a...`: the failure was this lane's first C4 assertion (it read
    the Path as the first header line; the first is Injection-Info); the
    corrected test reran alone, `--no-build` on the same image: OK, log
    `46b86774...` (`hbox-native-c3c4-run.txt`, `hbox-native-c4-rerun.txt`).
    The control module in that run took 25 s; harness-repair-2's sweep had
    it at 148.7 s, so the 125.5 s selector test below needs a remeasure
    before any change. The seven over-budget modules, examined from
    harness-repair-2's sweep logs: control 125.5 s is
    test_the_production_image_refuses_every_selector_at_startup, 96
    production-image starts (48 selectors x `operator run` and `store
    recover`) at about 1.3 s of image boot each; peer_pull 121.7 s
    (cursor publication cuts), served_crash_model 131.8 s (prepare/publish/
    finish cuts), state_checkpoint 78.8 s (every cut), native_checkpoint
    36.7 s (reclaim cuts), history_required 30.4 s (every marker cut): each
    one image start per enumerated cut, a cost of the enumeration, not a
    harness wait. bp_node 21.4 s IS a harness wait: three `time.sleep(5.5)`
    and one `sleep(2)` waiting out `*fn-bpnp-default-owner-backoff*`
    (5,000 ms, books/bp-forward-attempt.lisp). No split or fix landed:
    the selector loop's reduction trades dynamic coverage and the backoff
    wait needs a configurable backoff; both are PKT-445 (b) with defaults.
    PKT-288 (a fake owner with feeds for twonode/scale) not reached:
    PKT-445 (d).
11. **PKT-120** (a1b45e1d): proofs.json's m5 note and rep-heap's two
    placeholders. The rcon accessor-equality warnings (5, books/records-
    codec-concrete, records-concrete) and the intent teeth's
    bare-general-claim need book changes: PKT-120 narrowed to those.
12. Docs (fcb1e0ee): docs/proofs.md, docs/proof-style.md section 5.

## Packets

- Closed: PKT-306, PKT-346, PKT-345, PKT-305, PKT-312 (the check; its
  backlog is PKT-446), PKT-117 (examined: no gap in the key), PKT-258,
  PKT-341.
- Narrowed: PKT-285 (the merge_lane.sh lines are proposed; certify-in-place
  designed), PKT-120 (the rcon and intent-teeth warnings), PKT-218 (C3 and
  C4 repaired; key_statements was repaired at 0a1f2d54; hybrid_author,
  consumer_project_bounds and the kill harness's band remain), PKT-248 (the
  rest in PKT-445).
- PKT-445: (a) merge_lane.sh adopts the two lines above; (b) the bp_node
  backoff wait (a test-configurable backoff, then wait on `after=`) and the
  control selector loop (default: keep every selector on `operator run`,
  one representative on `store recover`, since the gate is one function
  before any store opens; about 63 s, still a split decision); (c) a teeth
  audit of must-fails with no paired evaluated counterexample; (d) PKT-288's
  fake owner with feeds; (e) `farm.py certify-in-place` as designed above.
- PKT-446: the 349 stale spec/doc citations of 254 names listed in
  tools/spec_cite_exemptions.json: correct each name, or move it to
  `exemptions` with its reason.

## What ran

Laptop: every module this lane touched through tools/test_budget.py (29
tooling modules, 170 s, all within budget); `make check-lane` (below).
persvati: the farm run above; proof_repl list/reap. hbox: the two native runs
(/tank/fn/scratch/tooling-velocity/). /tank/fn/node untouched.
