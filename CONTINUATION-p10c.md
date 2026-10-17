LANE CLOSED by Deputy C: lane/p10-cite stays pushed (3d15df13a) and UNMERGED, as the record only.
Reason: +71 LOC, no shared parser or resolver; the three tools check different things, so the P10(a) premise does not hold.

# p10c continuation
- Layout: tools/cite/{__init__,__main__,core,paths,names,docs}.py; shims tools/{cite_check,spec_cite_check,docs_check}.py.
- Before capture runs on worktree build/lanes/p10-cite-before (remove at end: git worktree remove).
- /tmp/p10c-capture.sh OUTDIR ROOT ; before=/tmp/p10c-before after=/tmp/p10c-after
- Tests ported in place (tests/test_{cite_check,spec_cite_check,docs_check}.py import cite.*).
- TODO: equality diff -> /tmp/p10c-equality.txt, fixture equality test, wc, commit/push.
