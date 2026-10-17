# p10w continuation
- worktree build/lanes/p10-world, branch lane/p10-world. HEAD has coverage_dump guard_callees commit.
- world v1 (no guard) at /tmp/p10w-world-v1.json sha 2c25a98b.. tree d3b392c32; v2 dump (with guard_callees) running via coverage.py dump --host hbox, log /tmp/p10w-dump2.log.
- before-captures: /tmp/p10w-before/ (default.out 379 lines rc0; summary-strict.out rc0, 374 orphans). Makefile mode: reach_check.py --summary --strict.
- finding: pure-world edges => 394 findings (+20, 0 removed). causes: (1) absstobj export->exec edges (world has only logic) keep text; (2) guard mentions are real calls (image guard-checking t) -> dump guard_callees; (3) TRUE text false green: quoted global name 'fn-owner-history-capture in fn-owner-history-capture-slot read as call of same-named defun.
- experiment scripts /tmp/p10w-exp.py, p10w-why2.py
- plan: overlay in Graph.__init__: world edges (callees+guard+attachment) for world fns that are not absstobj exports, plus text edges to names NOT in world.functions (macros); text otherwise. --world flag.
