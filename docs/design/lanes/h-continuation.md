# fn2 layer H continuation (the surface harness and the nightly; present state at origin/dev a4bea27de, rewritten whole 2026-11-04)

Layer doc: `docs/h-harness.md` (targets, recipes, the fn1-bug ledger). Brief:
`docs/design/briefs/FN2-LAYER-H-HARNESS.md`. No H seat is live on 2026-11-04; the deputy fixed the nightly's
promotion defects (bad1b23f0, 8cc2f2c4f) and regenerated the interim table (554e1e407).

## The line (the measure every "serves" in the record cites)
`build/h8/nightly/LATEST.txt` on the Mac, at 132ac2c62 (2026-11-04):
`M2 cuts 0/12 (sim-layer-e over the served machines not yet run) | serves 26 verbs (...); 5 interim rows left: D6
2, D7 1, E2 1, E4 1 | fn2: S ok served 32100 interim 929 (D6 929) WIRE 16768 opened/16768 judged/0 unjudged/0
refused, disagreements 0; exit 3 | fn2-native: S ok served 32100 interim 929 (D6 929) WIRE ...; exit 1 | NOT RUN
by owner (both targets): D6 (groups at init) 55, D/E (family not serving) 32, B/D (store init) 16, D (developer
verbs) 12, opt-in / box fixtures 4, H (fn2 owner for the differential; D6, E2) 1, H (driver hook) 1`.
Runs at the new root: 2026-11-04-bad1b23f0 (every surface run failed before its first connection: tools/acl2 not
found), -8cc2f2c4f (red on the socket: every TCP client was a peer), -132ac2c62 (the line above).

## The nightly (`tests/harness/laptop_nightly.sh`)
- Cron: `30 3 * * * /bin/sh /Users/ember/dev/fn/tests/harness/laptop_nightly.sh`. Worktree
  `build/lanes/h-nightly`, fast-forwarded to origin/dev; output `build/h8/nightly/<date>-<sha>/` and `LATEST.txt`;
  PID file `build/h8/nightly/running.pid` (stop: `kill -- -$(cat build/h8/nightly/running.pid)`); refuses under 60
  GiB free or with a run live. Its re-exec ignores setsid's EPERM under cron (bad1b23f0).
- It runs `--target fn2` (the simulator session) and `--target fn2-native` (the socket session) for the nntp family
  at 1,000 x 50 over the seeded store (`tests/seeded-store.lsp`; posting on, peering off).
- The interim table `tests/surface/fn2_conn_interim.json` is D's export (`tools/acl2 < tests/conn-interim-export.lsp`
  against a certified `books/conn-answer`); a verb that leaves it is judged as served.

## Owed, with the exact next step
1. **M2 cuts** (lane/m2-measure): `H_NIGHTLY_M2` set to a command that runs `tests/sim-layer-e.lisp` over the
   served machines and writes `OUT/m2.json` `{"passed": n, "total": 12, "source": ...}`
   (`tests/surface/nightly_nntp.py:75-84`, `laptop_nightly.sh:54-57`).
2. The two exit codes: the line prints `exit 3` (simulator) and `exit 1` (socket) beside 0 disagreements; read
   `build/h8/nightly/2026-11-04-132ac2c62/` and name what each code means in the line, or fix the driver.
3. An fn2 owner for the nntp differential (F); `Fn2Backend.init` with groups when the served node takes groups at
   init (the 55 D6 NOT RUN rows); posting through the socket carrier beyond the seeded store; the W7 perf adapter.
4. The fn1 row on hbox (`tests/harness/hbox_nightly.sh`): not run this round (hbox has 13 GB free).

## Seams
- From D: the interim export after every change to `*fn2-answer-interim*`.
- From E: sim-layer-e's M2 entry point. From A: the seeded store shared by sim-session, native-serve,
  native-session.
