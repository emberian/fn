# extract-forms continuation (2026-10-07)
Done: task (i) spike. tools/extract/spike/{forms-spike.lisp,bare-compile.lisp,SPIKE-LOG.txt} + results.
Run: scp forms-spike.lisp to hbox:/tank/fn/scratch/extract-forms/, then
 SPIKE_OUT=dir/ SPIKE_LIMIT=60000 SWARM_MEM_MAX=36G swarm-build <world image> < (":q" (load ...) (sb-ext:exit)),
 then bare-compile.lisp under /tank/fn/sbcl/bin/sbcl. World used: extract-cache/world-18bcd... (Oct 5; use dev's for final).
Verdict: feasible. Runtime list = 229 ACL2 system raw defs (ignorep=RECLASSIFYING; 228 pinnable to acl2-8.7 source defun),
 50 *1* names (44 *1* of CL prims), 27 variables. Needs: defstobj creators emitted, attachment cells, defg for stobj live vars.
NEXT (ii): move emitter into core-export.lisp (ACL2-side), xt-verify-defs (per-fn sha256 manifest), runtime list in clruntime.lisp
 pinned file:line, core.sh fails on undefined-function warnings; teeth tests. Then (iii) delete chicken.py/*.scm/fcheck*, retarget gate.py.
 Merge origin/lane/extract-c first. Do not touch xt-core-verdicts/table-alist/raw-trap.
