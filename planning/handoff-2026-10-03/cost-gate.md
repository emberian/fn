# LANEDUMP cost-gate (Opus 5.5, wound down 2026-10-03)

Branch lane/cost-gate, head f4c5d4e53 (on origin; base 4aa332295; sent to the runner for the all-onto-dev merge).
Worktree build/lanes/cost-gate. Two new files only: tools/cost-probe.lisp, tools/cost_gate.py. No host,
build-script, Makefile or registry change. Nothing loads the probe into an image: cost_gate.py `--eval`s it
into a developer launcher at run time and refuses a non-developer launcher.
Ledger: cg-report (open, WIP), cg-gate (open), r71-F14, r72-F9 (open, notes); added cg-owner-io-guard
(owner stage-5b) and cg-newnews-hang (owner served-catalog-live).

## Measurements (hbox, tmpfs, 2 KiB POSTs, one connection, guards ON as fnn-main runs them)
- Image set 77b7d258d (before sf-success): POSTing N since open took 0.15 s at N=30, 5.45 s at N=200, and
  more than 595 s at N=1000 (killed). That is cubic. At N=150, fn-owner-io: 303 calls, 10.1 s, 2.49 GB, 99.8% in
  its guard fn-sn-statep, with 2.26M fn-held-p calls (successes x records).
- Image set 45e05c7fd (sf-success in), plain launcher: N=30 0.13 s, N=200 1.63 s, N=1000 30.1 s, which is
  4, 8 and 30 ms per POST. That is still O(N) per POST.
  Probe: fn-owner-io (2 calls per POST) costs 27 ms and 3.5 MB per call at N=300, and 92 ms and 11.8 MB per call
  at N=1000. Exponent k=1.0; 99.9% is the guard fn-sn-statep. Inside it at N=1000:
  - fn-sf-record-listp 63 ms (about 3 fn-held-p per record);
  - the success keyset 24 ms;
  - fn-node-statep 3.5 ms.
  Extrapolated linearly, that is about 9 s and 1.2 GB per call at 100k, or about 18 s per POST. The other
  entry guards are flat (O(article), not O(N)):
  - fn-owner-chunk-span about 1.3 ms;
  - fn-owner-prepare-buffer about 3.3 ms (fn-article-syntax-p);
  - fn-owner-take and fn-owner-pending-octets about 1.5 ms.
  Raw dumps were in /dev/shm (removed); the numbers above are the record.
- NEW DEFECT (cg-newnews-hang), plain launcher on 45e05c7fd: `NEWNEWS * / fn.* 20261001 000000 GMT`
  - N=3 and N=8: answered in 2 to 8 ms;
  - N=12: no answer within 100 s;
  - N=50: 225 s at about 77% owner CPU, then the connection closed;
  - `NEWNEWS fn.g1` at N=50: answered in 7 ms.
  The 8 groups take every 5th article cross-posted. This hang is what blocked cost_gate.py's window.

## Tool state
- cost-probe.lisp works on both images. It does these things:
  - wraps fnn-call per entry and every FN- guard predicate (810 functions), with per (entry, predicate,
    parent) rows;
  - serves a request thread that polls FN_COST_PROBE/request.lisp (never a signal: SIGUSR2 is SBCL's GC
    stop);
  - provides cp-calibrate (timed 122 ns and skipped 15 ns per wrapper), cp-elide and cp-unelide (build
    phase only), cp-fixture-report (asserts fn-sn-statep and fn-owner-retain-statep; verified T at N=100),
    cp-dump and cp-reset.
- cost_gate.py: run, table, check, baseline and box are written.
  - The build phase at N=400 completes: elision, withdrawals through control.cancel, and the stalled reader.
  - The window hangs at its NEWNEWS line. To get the table now, drop NEWNEWS from window() (or bound it with a
    socket timeout and record it as a failure).
  - table, check and baseline have NOT run on real data yet.

## Next
1. Put a timeout on NEWNEWS in window(). Then run
   `cost_gate.py box --image /tank/fn/images/45e05c7fd.../fn-host-developer --sizes 1000,3000,10000,30000,100000`.
   The coordinator asked for 100k reopened with N since open = 0; the checkpoint and recovered windows give
   that.
2. `cost_gate.py table OUT --md planning/guard-cost.md --json planning/guard-cost.json`, then
   `baseline OUT`, then commit. READY cg-report, then cg-gate in report mode.
3. Read checkpoint_s per N (r72-F9) and the stalled-reader curve (r71-F14). For the 9x header charge,
   measure the peak heap of 1, 4 and 10 MiB POSTs; not started.
4. Hook shape agreed with DEF-ENTRY (planning/cost-hooks.json):
   - the fixture is named `served`;
   - an entry the workload never reaches is NOT EXERCISED, which fails;
   - sizes use a fixed vocabulary.
   Not implemented in check yet.
- Traps: never `pgrep/pkill -f` a pattern that is in your own ssh line; use /dev/shm/fn-cost-gate/reap.sh.
  hbox cache: /dev/shm/fn-cost-gate is 110 MB (the shipped tree); remove it when the lane is done.
