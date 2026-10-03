# HOST-LIFECYCLE continuation (wound down 2026-10-03)

Branch: lane/host-lifecycle at 4e409a9d6 (pushed; handed to runner a8c1198f67920c411 for the dev merge).
Worktrees: build/lanes/host-lifecycle (lane), build/lanes/host-lifecycle-red (RED tree, branch
lane/host-lifecycle-red, never merge: dev + item 3 + developer hold hooks + all tests; remove when done).

## Per item
| item | commits | verified |
|---|---|---|
| 3 / S010 TLS suffix | b85207d76 test, fa644fd88 fix | VERIFIED: red native-red3 (exit 4 "protected owner read left a TLS suffix"), green native-green3b 2/2. Ledger: ready. |
| S001/S004 accept attempt | 43c0b60dd test, 36670bccc fix, 375bc9b57 dispatch-rule fix + interfaces.json | AcceptExhaustionTests red at dev (red4: owner exit 4 "Socket error in accept: 24") and passed in green7. |
| S006 bp-node peer reset | 36670bccc; test moved to tests/test_bp_node_native.py NativeBpNodePeerResetTests (4e409a9d6) | UNVERIFIED: the old test class's setUp (producer fixture) refuses at dev; new light class not run yet (in green8/base8). |
| S007 pull local refusal | 36670bccc | UNVERIFIED (no native case; under `operator run` max-conns is 2^64 so the sweep trigger is unreachable). |
| 12 / F12 NIL worker + join default | 4dda888b1 | red6 FAULT(4) -> green7 pass. |
| 10 / F10 / S018 publisher+exporter tails | 68533b1cb | red6 owner exited while held -> green7 pass. |
| 9 / F9 / S021 adopt across stop, wake on closed pipe | c3db20174 | red6 socket fd 15 open -> green7 pass. |
| 11 / F11 idle timer | d140933b5 | unreachable-in-composition: OVER not on cursor arm (over_pins 0/4); test skips by name. |
| 5 / F5 / S003 inline commit removed (fnn-owner-feed-logical) | 715a3df63 test, 99022509d fix | red6: health 10.2 s during web POST stall. green7: web suite broke (303) from my S030 change; fixed forward 4e409a9d6, UNVERIFIED. |
| S030/S031/S066 web classify/release | 99022509d, 4e409a9d6 | UNVERIFIED (see above). |
| S032 web reply join + deadline | 2b7170e94 | UNVERIFIED. |
| 13 / F13 pending-accept slots | 507cdd9ed test, 1cb0ec0e0 fix (+specs/host.md HST-024 host fact) | red6 30 accepted -> green7 pass. |
| S037/S065 web single thread | not attempted (needs per-connection fn-web-in/out or the mux) | open |
| S084-S091 (low) | not started | open |

## Runs (hbox, tools/hbox_native.sh status LABEL from the worktree that launched it)
red3, green3b, red4, green4 (failed interfaces-check, superseded), red5 (interfaces-check), red6 (red tree), green7 (1cb0ec0e0),
green8 (4e409a9d6, still running at wind-down), base8 (red tree baseline of slow_disk/implicit_tls/checkpoint_auto/over_pins/web, running).
green7 other failures to triage against base8: test_native_slow_disk (graceful stop past deadline did not exit in 60 s;
reads-flat timed out) -- COULD BE MINE (item 5/13); test_native_implicit_tls store inspect returned 0 while running;
test_native_checkpoint_auto budget deferral + source test (gated macro text, pre-existing); over_pins 0/4 (known).
check-lane at 1cb0ec0e0 red: host_loaded_check, witness_check, delta-code source tests, raw_scripts ... likely pre-existing;
baseline on the red tree was launched (build/remote-check/hbox-check-lane.log in host-lifecycle-red).

## lock_discipline_check (lane/lock-check fb4423550) on this tree: --check FAILS
NEW findings from my code: R1 UNRESOLVED "macro fnn-connection-scoped hides a synchronization or handler primitive"
(bp.lisp:772, bp-app.lisp:355, bp-node.lisp:996) -> declare it in tools/lock_discipline_contracts.json failure_scopes
(it converts: indet/fault re-signalled, refusal/os/socket -> connection word); R1 UNRESOLVED bp session lambdas reaching
fnn-owner-core (stored callbacks; were already there, keys moved lines -> STALE rows + NEW rows: rebaseline);
owner.lisp publisher thread lambda R1 rows moved (5258 -> 5443). Many STALE rows from line moves: run
`python3 tools/lock_discipline_check.py --write-baseline` after merging lock-check and commit the lowered baseline.
R10 targets (41 rows, e.g. io.lisp:1120 fnn-log-swap-fd ignored close) NOT started.

## Next steps
1. After the merge: rebase on origin/dev; read green8/base8; fix forward any red attributable here (slow_disk first).
2. Make lock_discipline_check --check pass (contracts row for fnn-connection-scoped; rebaseline).
3. Measure pull commit latency before/after F5: FN_HOST_LIFECYCLE_MEASURE=1 tests.test_native_host_lifecycle.PullCommitLatencyMeasure (needs FN_NATIVE_HOST).
4. FAILURE-SCOPE (a20a851dc63e822b0) will convert the publisher-tail 4-arm handler to fnn-owner-thread-escape after both land.
5. Remove build/lanes/host-lifecycle-red and its hbox scratch trees when done.
