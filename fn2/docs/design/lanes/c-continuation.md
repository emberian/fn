# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Third seat since 2026-10-30. Method of
2026-10-29 (`briefs/FN2-SEAT-COMMON.md`): dev is the branch; Opus writes the code; Codex only for
bounded pieces with real signatures pasted; READY to main per commit (SendMessage to "main"). Brief:
`briefs/FN2-LAYER-C-ORDERED-RUNS.md`. Layer doc on dev: `fn2/docs/c-ordered-runs.md` (design,
seams, schemas, read contract, keystones, quest plan, interim decisions §7). Box safety verbatim in
COMMON.

## Landed (all READY sent)
- 181df0df0 C1a, 8dfba6db2 C1b, 1e823b06f C1b', 1c603fcdd run assembly, 8db53928a C2a (scans,
  overlay), c06369c9d C2b (identity Binding).
- 37a48f7d0 **C2c** (dev e9cbd926b): `fn2/books/ribbon.lisp`, homogeneous Ribbon w=64 r=8 per sealed
  run, one `:partitioned-filter` page (slots = keys + keys/16 + 63; max 61,472 keys,
  C-FILTER-ONE-PAGE). Build: `fn2-ribbon-start` (writer row already opened by `fn2-run-open` on a
  fresh page, page-kind partitioned-filter), `fn2-ribbon-work` until `:ready`, `fn2-ribbon-add` per
  key (field row of octets; `:more` = insertion pending, drive work until `:idle`),
  `fn2-ribbon-finish`, work until `:sealed`. Probe `fn2-ribbon-probe (pslot pgen hb qrow qk qs qg
  pk ps pg fields pool)` -> `:maybe`/`:absent`/refusal. 32-bit ops are mbe functions with
  unconditional widths (bitops local to one encapsulate); macro `fn2-ribbon-ub` states a width as
  predicate + natp + linear bound. runs-page: `fn2-run-head-b` shared B header. runs: installed rows
  carry FILTER FUNIT FCOUNTER (`fn2-run-install-filter`). identity: run-start probes the filter
  (`fn2-id-filter`), `:filter-miss` when uncached; decides counts READS SKIPS;
  `fn2-identity-cost-image`. Keystones fn2-ribbon-no-false-negative, fn2-ribbon-mutation-refused
  (teeth in tests/ribbon-unit.lisp).
- 76b82807c **C2d** (dev 4c7c775b4): `fn2/sim/check-identity.lisp` (independent; events `(:offer
  mid c answer outcome) (:query mid c answer) (:seal n) (:reclaim x) (:binding facts)`;
  `(fn2-check-identity events bound)`). identity: `fn2-id-stamps` (bucket = FNV hash seed 0 mod
  rows, bumped per record), `fn2-id-version` (max live identity run id); decide-start snapshots
  BUCKET STAMP VRUN; `fn2-id-record` (now takes fn2-id-stamps and fn2-run-installed) refuses `:stale`
  FIRST when either moved (C-IDENTITY-STALE). Adapter run ids start at 1 (row k, run k+1).
  `fn2/tests/sim-layer-c.lisp`: M3 (`fn2-m3-trace seed n defeat`, `fn2-m3-sweep`), keystone
  fn2-identity-linearizable; `sim-layer-c-sweep.lsp` 10,000 seeds (not yet run: run it on forge
  with forge-driver.sh when a box is quiet and report the row).
- d2f2ea9e8 ribbon uses A's word book (`fn2/books/words.lisp`: fn2-u32, fn2-u32-mul,
  fn2-prng-mix32); fn2-ribbon-mul32/-mix deleted; width lemma `fn2-ribbon-mix32-width`.
- ab5662b34 **C3a** (dev 654d1fd39): `fn2/books/ordered.lisp` (fn2-article id 2 :latest,
  fn2-overview id 3 key (group number) value (article position line (:octets 1024)), fn2-addr id 4
  key (principal position)); `fn2/books/range.lisp`: `fn2-read-plan` (pure, the read contract),
  tables `fn2-ranges` / `fn2-range-sources`, `fn2-range-start (g sid qbase hbase sbase smax cbase
  rbase pfield plimit qk qs qg ranges sources overlays installed)`, macro `fn2-range-assemble`
  generating `fn2-range-step (g budget ranges sources overlays overlay-index installed cursors
  paths cache fields pool)` -> :entry (rows at fn2-ranges-out, owner ok os og) / :end / :more /
  :miss / refusal; adapters `fn2-range-image (sid layout sources lo hi pidx plimit budget sealat)`,
  spec `fn2-range-spec`, keystone fn2-range-read-exact. Moves: `fn2-run-copy-row` (runs-page),
  `fn2-run-version sid` (runs), overlay COV column + `fn2-ov-cover`; `fn2-ov-start` takes cov.
  Test world `tests/range-assembly.lisp` (runs-assembly + range, calls fn2-range-assemble); unit
  `tests/range-unit.lisp`. Told main D6 can start.
- OWED.md regenerated at each (390 requirements at C3a, other seats' rows included).
- Worktree `/Users/ember/dev/fn/build/lanes/fn2/c-found` (branch fn2/c-found) = dev 654d1fd39.
  forge clone `/build/lanes/c` at d42bff1d2.

## Seam requests outstanding (sent to main)
- B: GC2 inside B5 (layer doc §8 item 2), still pending; blocks C1c's sealer and M3's device leg.

## Next
1. **C3b** positioned seek over overview: `Seek(stream, after = p)` = first entry of group g with
   position > p. Plan: a schema option naming a monotone value field as a fence (with the stream
   prefix length), copied into index entries at promotion (runs-schema index layout +
   `fn2-run-build-promote`), and a seek variant comparing (prefix, fence) at index levels and
   (prefix, value) at level 0; a range read then starts at a position. Fallback if the format
   change is too costly: binary search over numbers by lookups. Then M2 (cold sparse groups past
   cache capacity, charging directory and overlap reads; report reads per delivered row).
2. Rest of C1c once B5/GC2 lands (sealer machine through defmachine, descriptor + manifest,
   production assembly, filter ref in the descriptor). C4 (deffold, folds, summary cut, overlay
   replace for :latest) does not wait on GC2.
3. Watch: tests/runs-assembly 52 s on forge; split the identity assembly into its own book if it
   passes 55.

## Pitfalls hit (and what worked)
- Guard proofs and stobj column values: a column read through an enabled accessor becomes raw
  nth; the type facts may not fire through rewrite chains. Checking the width at run time
  (`(unsigned-byte-p 32 x)` in a b* `unless`) is the house style and cheap; loops should return
  only code + stobjs (the caller computes the new index), not an index needing a type lemma.
- Type facts used by `rationalp`/`integerp` guard goals need :type-prescription or natp+linear
  forms with no hyps; hyp'd natp rewrite rules do not answer them (`fn2-ribbon-ub` with hyps t).
- `mv-nth 0` is normalized to `car`: state type-prescriptions on `(car (f ...))`.
- A `-preserves` macro disables the function unless `:disable nil`; put the type lemma first.
- Preserves of a setter with computed values needs the values' types as hyps (natp index, u32).
- Termination of a big stobj loop: split one non-recursive "tick" and a loop that disables it.
- Never define a constant named `*t*` (built in).
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
- Laptop certify (in the worktree): `sh fn2/tools/certify.sh tests/identity-unit.lisp
  tests/runs-unit.lisp tests/ribbon-unit.lisp tests/sim-layer-c.lisp sim/check-identity.lisp`.
- REPL iteration on a book: driver `(include-book "fn2/books/runs-page") (include-book
  "fn2/books/fnv") (set-inhibit-output-lst '(proof-tree warning observation)) (ld
  "fn2/books/ribbon.lisp" :ld-error-action :return)` via `tools/acl2 --timeout 600 < drv.lsp > out`;
  grep `ACL2 Error`. For test bodies: include the certified assembly, `ld` a copy of the test file with
  its include-book lines stripped.
- Forge closure + export: in the worktree commit, merge origin/dev, `git push -q -f
  fn@forge:/build/fn.git HEAD:refs/heads/fn2/c-found`; `ssh forge 'cd /build/lanes/c && git
  checkout -q -- . && git fetch -q /build/fn.git fn2/c-found && git reset -q --hard FETCH_HEAD &&
  (setsid nohup sh build/c1.sh > /dev/null 2>&1 & echo $! > build/c1.pid)'`; wait (background
  until-loop on `kill -0 $(cat build/c1.pid)`); results build/c1-closure.out ("closure rc=0"),
  build/certify-closure.log, build/c1-export.out ("FN2-OWED-EXPORT PASS"); scp fn2/docs/OWED.md
  back and commit it alone.
- Integration: merge origin/dev AND the shared tree's local dev into fn2/c-found, then in
  /Users/ember/dev/fn: `git merge --ff-only -q fn2/c-found`, `python3 tools/secrets_check.py`,
  `git push -q origin dev`.

## Certify times (forge, d42bff1d2)
| book | seconds |
|---|---|
| books/runs-page | 24.4 (c06369c9d) |
| books/runs | 16.9 (c06369c9d) |
| books/ribbon | 16.2 |
| books/ordered | 16.1 |
| books/identity | 11.1 |
| books/range | 24.2 |
| tests/runs-assembly | 52.1 |
| tests/range-assembly | 27.0 |
| tests/identity-unit | 4.0 |
| tests/ribbon-unit | 2.3 |
| tests/range-unit | 3.1 |
| tests/sim-layer-c | 18.9 |
| sim/check-identity | 0.3 |
