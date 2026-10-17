lmg: merge c6bd60a14 (clean, 130 tests OK). NEW 131 at base.
fix gap4 (let rebinding) 7628db384 -> NEW 127. fix gap5 (sync table) -> NEW 127 (web-replay cleared, measure-table reclassified write->read).
helpers: /tmp/lmg-gate.sh N PREV, /tmp/lmg-mut.sh <checker> <TestClass>, /tmp/lmg-act.py REGEX (actors per access), /tmp/lmg-path.py FN
Findings: gap 1 hypothesis mostly falsified: no spawner attribution; 'main' arrives via real calls (mux start->stop-loop failure path) or uncalled entry (fnn-pull-worker-guarded is test-only dead code in host).
todo: gaps 2/3 (hb before make-thread; death), 6 (threads rows, leaf locks), 1 (dead entries).
gap6 done (NEW 120). next: gap3 hb-before-spawn, gap2 dead-guard
gap3 (hb before spawn): prototype at /tmp/lmg-hb-prototype.py (loops/Event.loops, run_once, reach_indices, ordered_before, prune_ordered_writes, contract entries_exclusive). Clears NOTHING real: peer-flight-bank blocked because fnn-pull-service-start is only passed as #'ref (module-start callback, no call edge); mux wake write+spawn share a dolist; decoded-storage has mux/pull/web lambdas that are also started via refs. Needs funcall-of-parameter dataflow. NOT committed.
DONE: fixes 7628db384 (let rebind), 5efc9a067 (sync table), 813bb130e (rows+leaf locks), bc404e040 (dead guard), 6ce58afbf (test-only entry). NEW 131 -> 114. gate files /tmp/lmg-gate-{0,1,2,4,7,8}.txt (+ .diff).
