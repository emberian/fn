# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Method of 2026-10-29
(`briefs/FN2-SEAT-COMMON.md`): dev is the branch; Opus writes the code; Codex only for bounded
pieces with real signatures pasted; READY to main per commit. Brief:
`briefs/FN2-LAYER-C-ORDERED-RUNS.md`. Layer doc on dev: `fn2/docs/c-ordered-runs.md` (design,
seams, schemas, read contract, keystones, quest plan, interim decisions §7 incl. C-ASSEMBLY,
C-ASSEMBLY-THEORY, C-ONE-ASSEMBLY, C-OVERLAY-SORTED). Box safety verbatim in COMMON.

## Landed (all READY sent)
- 181df0df0 C1a, 8dfba6db2 C1b, 1e823b06f C1b', 37ba641da boxes.md hbox fallback.
- 1c603fcdd **C1c first item, the run assembly** (`fn2/books/runs-assemble.lisp`, macro
  `fn2-run-assemble`): dispatcher `fn2-run-layout-{fields,keys,decode,encode,size,compare}` (case
  over schema ids; level 0 entry layout, positive level index layout); generic `fn2-run-add`
  (`-add-ready` pure + `-add-write`), `fn2-run-seek`, `fn2-run-build-add/-promote`; per-schema
  keystones generated at assembly; owed `fn2-run-glue-verified` + certify-time check
  (`fn2-run-glue-check` over `fn2-run-glue-assembled`). defrunschema = 3 deflayouts + compare +
  registration; refuses after the assembly (table `fn2-run-assembly`).
- 8db53928a **C2a**: scans (path table `fn2-run-paths`; cursor phases :at :up :end :lost;
  `fn2-run-nth (sid lv k ...)`), generic overlay (`fn2/books/overlay.lisp` tables + placement;
  assembly: `fn2-ov-entry/-order/-search/-locate/-write/-insert`). Keystones NAME-RUN-SCAN,
  NAME-OVERLAY-SORTED.
- c06369c9d **C2b identity** (`fn2/books/identity.lisp`): schema fn2-identity id 1; spec
  (`fn2-id-decide-spec`, `-record-spec`, `-answers-spec`, `-binding-spec`, `-within-bound`); macro
  `fn2-identity-assemble` (decision machine `fn2-id-decides` rows: start, overlay block walk,
  run-start, run-scan, fold, `fn2-id-decide-step`; `fn2-id-record` under
  `*fn2-identity-contents-max*` = 4, refusal `:identity-conflict-bound`; adapters
  `fn2-identity-decide-image (offers split forget queries)`, `fn2-identity-binding-image`;
  keystones `fn2-exact-identity`, `fn2-identity-binding-converges`). Installed-run registry
  `fn2-run-installed` (runs.lisp). Test assembly `fn2/tests/runs-assembly.lisp` (identity +
  fn2-rt-num + fn2-rt-mid, assembled once; teeth makers fn2-rt-teeth/-run-teeth/-scan-teeth/
  -overlay-teeth); units `runs-unit`, `identity-unit` include it; owed-export.lsp includes both.
- Cursor step structure now: helpers `fn2-run-step-{header,seek,child,deliver,up}` (scalars),
  wrappers `fn2-run-phase-*` (read the row via `fn2-ra-with-cursor (vars body)`), dispatcher
  `fn2-run-cursor-step (scan c ...)`, `fn2-run-lookup-step` / `fn2-run-scan-step`; cursor-start is
  `(c schema level slot gen unit counter rb okind oslot ogen)`.
- Worktree `/Users/ember/dev/fn/build/lanes/fn2/c-found` (branch fn2/c-found) = dev c06369c9d,
  clean. forge clone `/build/lanes/c` holds the same tree (scp'd files, certified).

## Next (critical path B5 -> C2 -> C3 -> D3)
1. **C2c Ribbon per sealed run.** Homogeneous Ribbon (w = 64, r = 8 bits; always solvable; free
   rows from a PRNG seeded by the run id, so pages are reproducible), keyed on a 64-bit hash of the
   Message-ID octets (FNV in `fn2/books/fnv.lisp`, seeded per run; adversarial FPs cost only extra
   run reads: record as a decision), built at seal (bounded, resumable Gaussian insertion in key
   order + back substitution), stored in `:partitioned-filter` pages referenced by the run
   descriptor's FILTER- ref (and a column in `fn2-run-installed`). The decision's run-start phase
   probes it and skips the run on a miss; `:found` never comes from it. Owed: no false negative
   (every recorded Message-ID passes its run's filter), with teeth (positive: all keys of a built
   run pass; negative: a filter built without one key rejects it). Report bits/key and probe cost.
   Consider writing the GF(2) insertion by hand first, then a Codex helper for the solver if useful.
2. **C2d** IDENTITY checker (`fn2/sim/check-identity.lisp`) and M3 in the simulator: read
   `fn2/sim/` and A/B's checker pattern first (check-*.lisp, sim-layer-b).
3. **C3** ordered schemas (metadata, overview, addr) + range cursors with resume key and logical
   version, positioned seek (scan already exists), M2, read contract (exactly-at / at-least,
   catch-up; UC §12 decision 2). INBOX-DELIVERY §4-5 for addr.
4. Rest of C1c: descriptor + manifest schema (C-MANIFEST-IS-A-RUN), the sealer machine through A's
   defmachine with full arm contracts (`lanes/a-to-d-arm-contracts.md`), GC2 member when B5 lands
   (layer doc §8 item 2), production assembly (C-ONE-ASSEMBLY: C units then move onto it). Then
   C4-C6.

## Pitfalls hit (and what worked)
- Per-schema generated functions must be thin; everything else generic over the dispatcher.
- **World-dependence of proofs**: deflayout disables fields/pool accessors locally; a world that
  includes a schema's certified book has them enabled → assembly 148 s instead of 17 s. Fixed by
  `fn2-run-assembly-theory` inside each assembly encapsulate. If an assembly proof is slow in one
  world and fast in another, diff the theories (disabledp) first.
- `-rows` accessors: disable a stobj's rows only where a callee changed that stobj (shape lemmas use
  -rows); keep enabled where element types come from the recognizer.
- Split multi-branch stobj functions: pure checks + straight-line writes; per-phase helpers with
  scalar params; wrappers that read a row prove shape with the row accessors folded
  (fn2-ra-shape's disables list).
- Recursive loops: count-down measures `(nfix k)`; `(nfix (- n i))` measures loop the rewriter.
- `(zp x)` needs natp guards; dispatcher uses `(and (integerp lv) (< 0 lv))`.
- `fill` is a CL special: never bind it. b* binders must be `(mv ...)` with stobjs spelled out.
- A function returning one stobj still returns (mv code st).
- ld vs include: local events in an ld'd file run (local arithmetic, local in-theory).
- Kill the `tools/acl2` wrapper by its PID (it takes sbcl down); an `sh -c` PID orphans it. On
  forge `sh build/c1.sh` children survive killing sh: start it with `setsid` and wait instead.
- New files: `git add <file>` in the worktree, then `git commit -F msg -- <paths>`.
- Before an OWED export, merge origin/dev into the worktree (others' rows), or the export drops them.

## Commands that work
- Certify (laptop): `sh fn2/tools/certify.sh tests/identity-unit.lisp tests/runs-unit.lisp`.
- Per-event timing: REPL driver with `(set-inhibit-output-lst '(prove proof-tree warning
  observation event))` and `ld` of the forms; sort `Form:`/`Time:` pairs.
- Detached: `nohup tools/acl2 --timeout 900 < drv.lsp > out 2>&1 & echo $! > pid` (foreground call).
- Forge: `git push -q -f fn@forge:/build/fn.git HEAD:refs/heads/fn2/c-found`; on forge in
  /build/lanes/c: `git checkout -q -- . && git fetch -q /build/fn.git fn2/c-found && git reset -q
  --hard FETCH_HEAD`; scp changed files; `(setsid nohup sh build/c1.sh > /dev/null 2>&1 & echo $! >
  build/c1.pid)`; results in build/c1-closure.out, build/c1-export.out, fn2/docs/OWED.md.
- Integration: commit in the worktree; shared tree `git merge --ff-only fn2/c-found`; secrets
  check; `git push origin dev`.

## Certify times (forge, c06369c9d, load 7-8)
| book | seconds |
|---|---|
| books/runs-page | 24.4 |
| books/runs-schema | 1.7 |
| books/runs | 16.9 |
| books/overlay | 4.3 |
| books/runs-assemble | 2.2 |
| books/identity | 8.7 |
| tests/runs-assembly | 40.7 |
| tests/identity-unit | 3.2 |
| tests/runs-unit | 7.5 |
