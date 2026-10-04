# bp2 (BP-2, Opus), lanedump: branch lane/bp2

The predecessor is lane/bp@fed210549 (Fable, wound down). Merged on top:
origin/integrate/20261004, then origin/next twice (b7624961f, then the
e0a8516e9 line). Wound down on ember's ramp-down broadcast after slice 1.

## Coordinates

| what | value |
|---|---|
| head | see the final READY line (LANEDUMP.md section bp2) |
| K1–K3 admitted | persvati REPL `bpfc` (stopped), at ab8e639dd |
| narrow recertify | PASSED: persvati run-20261004T043809Z-45b8, manifest certify-20261004T044115Z-1138962 (4 of 4 passed: bp-forward-cursor, its tests, bp-route-step, bp-node-forward-retry; 358 installed from the cache); indexed in planning/evidence-index.tsv |
| hbox certify | cancelled twice (run-20261004T035652Z-039c, killed with no verdict); per assembler RULE 3 the closure belongs to the integrator's batch on next |
| raw witness | tests/native_bp_forward_cursor_raw.lisp PASS (laptop SBCL 2.6.8): 2,000 decisions per turn become 1 (startable head) or 64 (busy head); 32 turns of at most 64; same entry; fn-bpfc-run agrees |
| host_check --load | 55 of 55 raw files load, 0 findings (bare ACL2; world not evaluated, umbrella uncached on the laptop) |
| lock gate | 0 stored-callback R1 rows; baseline 366 → 353, 0 added; remaining bp rows are fnn-unwind-cleanups ×7 (generators2's) |
| ION natives on 45e05c7f | hbox:/tank/fn/scratch/bp2/native-ion-x10-45e05c7f, 2 FAILED in setUp ("store: canonical Store refused retention event"): the image predates e27ea2eb1 and the current fixture, so this is NOT a witness either way |
| advisory review | kimi and grok both completed; pasted verbatim in packet §6.1 with a source fact-check |

## What landed (commits on lane/bp2)

- ab8e639dd: book and tests. K1, K2 and K3 are admitted, with the
  lemmas. Two teeth that bit nothing are replaced. Both books are in the
  Makefile roots and the UNHOOKED markers are gone.
- 7bd3d7885: host. The `:forward` arm calls `fn-bpfc-turn`; the
  O(held × table) plan arm is gone. Also: the
  `+fnn-bpnode-forward-quantum+` 64 constant, both builds including the
  book, interfaces (fn-bpsched-forward-entry undeclared; fn-bpfc-initial
  and fn-bpfc-turn declared with K1–K3), the raw witness, and the spec
  row "The forward round".
- 22af9ee30: lock checker. Adds the `callback_contexts` contract table
  (checked declarations of a stored callback's entry), 5 declarations,
  the 13 stale rows removed, and 5 unit tests.
- 004d864cb, 683b18f50: packet. Slice-1 facts corrected; advisory review
  and fact-check; §7 AMENDED.
- cae74b899: tools/extract/world.py regeneration (5 derived world files,
  +1 include each).

## Not done / owed (the exact continuation)

1. Natives (the integrator's batched set on next: developer,
   dtn-developer, production). Run SCN-1110
   `tests.test_bp_node_native.NativeBpNodeTests.test_keepalive_peer_does_not_block_second_canonical_request`,
   then the three forward natives (selectors below), then
   `tests.test_native_ion_workflow` (X10A/X10B green-after). File each
   with `evidence_store.py put`; the index line is the claim.
2. SCN-1125 on the same set, after K5 is stated (packet §7(d), two
   conjuncts).
3. S025 (packet §7(e)) is escalated to ember: Busy (3) or Resource
   Exhaustion (5), plus the progress, drip, victim, sampling and settling
   gaps. Slice 3 does not start before that answer.
4. Slice 3a: the per-round attempt budget (§7(a)). Slices 2 and 4 per
   §3 with the §7 amendments.
5. Generated files for the integrator: planning/interfaces.json
   (fn-bpfc-turn added, fn-bpsched-forward-entry gone), ledger,
   current.md. PRF-1311 is claimed in id-claims.jsonl but not yet in
   planning/proofs.json; an integrator or next lane adds it with the
   manifest.
6. make check-fast reds are all base (merge_registry HST-003, 23
   reach_check rows, ledger and current_view stale, unwind-cleanups lock
   rows, 2 O->? lock tests). None names a bp2 file. check-lane was not
   run: base 48/91 red, and the assembler's RULE 3 makes the narrow
   recertify the gate.

## Native selectors (for the integrator's batch)

    tests.test_bp_node_native.NativeBpNodeTests.test_keepalive_peer_does_not_block_second_canonical_request
    tests.test_bp_node_native.NativeBpNodeTests.test_older_unrouted_transit_does_not_block_younger_local_request
    tests.test_bp_node_native.NativeBpNodeTests.test_older_mru_wait_allows_younger_forward_and_replays
    tests.test_bp_node_native.NativeBpNodeTests.test_removed_route_keeps_transit_held_and_reports_no_route
    tests.test_native_ion_workflow.NativeIonWorkflowTests.test_observation_binds_explicit_route_and_survives_reopen
    tests.test_native_ion_workflow.NativeIonWorkflowTests.test_unrepresentable_lifetime_refuses_before_attempt_or_helper
