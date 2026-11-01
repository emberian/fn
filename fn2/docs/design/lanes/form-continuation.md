# fn2 machine-form seat continuation (present state; rewritten whole after every commit)

Seat: Opus, writes the code; owns layer A's generator and adapter (and A's executor). Brief: main's launch prompt +
`build/coordinator/briefs/FN2-SEAT-COMMON.md`; method `build/coordinator/fn2/WORKFLOW-20261031.md`. Statement:
`build/coordinator/fn2/MACHINE-FORM-20261030.md` §6 (6.10 = what is built and what is open, rewritten with every landing).

## Landed (dev)
| sha | what |
|---|---|
| d04660248 6f05dbba0 516c2daf3 9a453bffd 7a0edee7a cb903f15c 24fce1ecd 82eb2bfc2 | G1, probe, P1, P2/P3, G2, P4, per-arm tuples, one shape theorem per function |
| 3804cb211 | Q1 reds: q1-unit's pin = the assembled catalogue; q1-teeth's profile serves reading |
| 371c48e4e | the `:local` listener (0600 Unix socket as the listener capability's second fd; `:local` peer w0 uid w1 gid; simulator per-capability peer) |
| 56b866c35 | G3 1/n: `:repeat` cost derived, F13 per-call holds (multisets), F10 phase-valued fields |
| 144596771 | turn bound from the registry: `*fn2-turn-transition-max*` = work-empty + max budget bytes+steps over every kind (Argon 9.8) |
| 4c7ab8df3 | native session serves the sim session's profile + seeded store (`fn2-n-make-host :seeds`, `fn2-nserve-replay` replays ENVELOPE from the seeded store) |
| a0556c390 | G3 2/n: paths (F11), holds per path (F14), typed links (F8), inner machines (`:sub`) — details below |

## How G3 2/n is built (a0556c390; for editing it)
Files: books/machine-arms.lisp, arms.lisp, machines.lisp, executor.lisp, tests/machine-arms-unit.lisp.
- **Paths (F11 + F14).** Every terminal records a path in acc `:paths`: (SOURCES ENDS USES ENTRY SETS STOP).
  The env carries path knowledge: `:known`/`:entry` (values of row-phase and each enum field, narrowed by
  `(equal ROW-F C)`/=/eql/eq, not/and/or in `:if`/`:cond`; `fn2-arms-path-narrow`), `:path-sets`, `:path-uses`
  (an op with answers acts only on its :ok paths: `fn2-arms-do-body`'s `use`), `:next-phases`, `:impossible`.
  A `:goto` re-walks the sub-arm (subs keep `:src (steps refusal subs)`) carrying `*fn2-arms-path-keys*`,
  so a shared sub-arm's leaves count per caller phase. Arm/handler contract `:next` = the paths' ends
  (`fn2-arms-path-ends`), contract gains `:paths`.
- **Conditional holds (F14).** `:holds` element `(K :while (F V ...))`, F an enum field; declaration keeps
  base `:holds` and `:holds-while ((PHASE K F V ...) ...)`. D0 per path (arms.lisp `fn2-arm-paths-problem`,
  enumerating F's values where the path's tests leave them open; a transfer to another row counts as the
  giver's release on a path, `fn2-arm-resource-problem-1 ... t`). Enforced for kinds with `:holds-while`;
  for every other generated kind the per-path findings are printed at defmachine-run
  (`fn2-machine-arm-path-report`), not refused. Found so far: FN2-SCRIBE :reserve -> :stopped holds a window
  it never acquired (probe kind; :stopped should not hold it on the refusal paths); the listener's
  :admitting finding was the transfer gap, now fixed.
- **Typed links (F8).** `:links ((L :kind K2 :slot S :gen G [:kind-field KF] [:back (B [BG])] [:reads (F ...)]))`.
  `defmachine-arms K :children` first emits K-LINK-L-LIVE-P and K-LINK-L-F (defun + type thm + defcost
  :child itself) over K2's table and fn2-machines; K2's table joins K's tuple after the registered extras
  (`fn2-arms-table-pairs`, machine tables register only at the assembly). `(:live L)`, `(:read L F)` (F in the
  read set), `:owner L` = the link's triple; a linked kind writes no `:okind/:oslot/:ogen` by hand. Liveness
  checks row-ok, kind (with KF), slot range, generation, back fields; no kind constant (index-time).
- **Inner machines (C gap 4).** `:sub ((NAME :field F :phases (Q ...) [:on-refusal ..] :arms ((Q STEP ...) ...)))`
  desugars in defmachine: enum field F (enum K-NAME), a sub-arm NAME (a `:cond` on ROW-F per inner phase),
  `(:sub-next NAME Q)` = `(:set (F *K-NAME-Q*))`.
- **Turn bound (Argon §9.8).** executor.lisp: `*fn2-turn-transition-max*` = work-empty + max over every
  registered kind's budget bytes+steps (`fn2-exec-kinds-work-max`, make-event over `fn2-machine-names`).
- Verified: hbox machine-arms-unit (25.9 s), machines-a-unit, cursor-unit, assembly, host-unit, q1-unit, q1-teeth,
  executor; sim-layer-a-smoke PASS on hbox (tree made a git repo with an empty anchor commit for the revision);
  native-serve-check PASS + GROUP/STAT over the seeded store. Not measured on forge yet (forge base is pre-G3).

## Next (in order)
1. Forge before/after numbers for 2/n (sync /build/lanes/form-base, certify assembly; the per-path re-walk
   costs expansion time per :goto).
2. `:genesis (STEP ...)`: a generated per-row genesis arm, run by the executor's init for each row of the
   kind (replaces C's fn2-sealer-start-row; C's fn2-engine-genesis keeps the group/sealer genesis ops).
3. F9's owed row owner = holder (a range handed between rows), with links.
4. Proof-structure changes adopted for after G3: per-output type/wfp facts as :rule-classes of one theorem;
   `:do` chains longer than four steps auto-split into chained sub-functions disabled in the parent.
5. Assembly per-child books (assembly-access 52 s, rows-other, the reference books, assembly-init's
   fn2-core-init-wfp, the executor's per-kind run rewrite); then listener registry arms by family, outbound Connect.

## Boxes
hbox: `~/form-g3`, a plain copy (rsync fn2/ tools/ excluding certs), not git, so smoke runs on forge. Launch
`(setsid sh build/X.sh > build/X.out 2>&1 < /dev/null &)` then `ps -eo pid,cmd | grep "[s]h build/X.sh"` -> PID file.
Certify progress is in `build/fn2-certify-*` (the newest), not build/X.log. REPL check of the generator alone:
`tools/acl2 < build/ma.lsp`. Forge `/build/lanes/form-base` (synced to dev 10-31 evening): measurement + smoke.

## Rules
PID files only; never stash / add -A; named paths; secrets check before push; a book over 60 s is its owner's
to fix; disk pressure: stop and tell.
