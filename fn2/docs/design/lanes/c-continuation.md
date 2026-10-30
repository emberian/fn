# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Method of 2026-10-29
(`briefs/FN2-SEAT-COMMON.md`): dev is the branch; Opus writes the code; Codex only for bounded
pieces with real signatures pasted; READY to main per commit. Brief:
`briefs/FN2-LAYER-C-ORDERED-RUNS.md`. Layer doc on dev: `fn2/docs/c-ordered-runs.md` (design,
seams, schemas, read contract, keystones, quest plan, interim decisions). Box safety verbatim in
COMMON.

## Landed
- 181df0df0 C1a (:schema kind). 8dfba6db2 C1b (run pages, defrunschema). 1e823b06f C1b' (multi-page
  runs, cache, cursors, run lookup; GC1 closed). 37ba641da boxes.md hbox fallback.
- **1c603fcdd C1c first item: the run assembly** (`fn2/books/runs-assemble.lisp`, macro
  `fn2-run-assemble`, expanded once per world after its last schema). Dispatcher
  `fn2-run-layout-{fields,keys,decode,encode,size,compare}` (case over schema ids; level 0 entry
  layout, positive level index layout) + shape lemmas; generic `fn2-run-add` (= `-add-ready` pure +
  `-add-write`), `fn2-run-seek`, `fn2-run-build-add/-promote`, `fn2-run-index-skip/-nth`,
  `fn2-run-step-{header,seek,child}`, `fn2-run-lookup-step`; generic adapters
  `fn2-run-page-image/-seek-image/-lookup-image (sid layout ...)`; per-schema keystones generated at
  assembly (names unchanged); owed `fn2-run-glue-verified` + certify-time check
  (`fn2-run-glue-check` over `fn2-run-glue-assembled`). defrunschema = 3 deflayouts + compare +
  registration (`:compare` in the row); refuses after assembly (table `fn2-run-assembly`).
  Cursors carry `schema`; `fn2-run-cursor-start (c schema level ...)`. READY sent.
- **8db53928a C2a**: scans (`fn2-run-paths` table; `fn2-run-cursor-step` shared by
  `fn2-run-lookup-step` / `fn2-run-scan-step`; phases :at :up :end :lost; `fn2-run-nth (sid lv k ...)`
  returns next offset) and the generic overlay (`fn2/books/overlay.lisp`: `fn2-overlays`,
  `fn2-overlay-index`, `fn2-ov-start/-freeze/-retire/-place`; assembly: `fn2-ov-entry/-order/-search/
  -locate/-write/-insert`); keystones NAME-RUN-SCAN, NAME-OVERLAY-SORTED. READY sent.
- Worktree `/Users/ember/dev/fn/build/lanes/fn2/c-found` (branch fn2/c-found) = dev 8db53928a.
  forge clone `/build/lanes/c` holds that tree (uncommitted copy, certified).

## Next (critical path B5 -> C2 -> C3 -> D3)
1. (done in 8db53928a) **C2a: generic range iteration + overlay** (both emitted by assembly-time macros, since they call
   the dispatcher; staged library-macro books expanded in order after `fn2-run-assemble`).
   - Iteration: path per level (table rows c*6+level: slot gen unit counter idx entries) recorded
     during descent; `next` at leaf: deliver entry idx (off tracked; off=0 -> nth via restart),
     at leaf end pop to the lowest level with idx+1 < entries, take that index entry, descend
     leftmost; a path page no longer cached -> `:lost` (caller re-seeks strictly after the last
     delivered key). cursor-start needs the root's unit/counter.
   - Overlay (generic per schema): bounded sorted in-memory run. Entries encoded by the schema's
     entry codec into a C-owned pool arena (C-OWNER copy at admission); resident u32 offset index
     kept sorted (binary search by decode+compare; insert shifts, bounded by capacity); phases
     :active/:frozen (frozen while sealing, still readable); seal = feed sorted entries to build-add.
     Decision C-OVERLAY-SORTED (recorded in layer doc §7 at C2a): no InfiniFilter in front of a
     resident bounded sorted table; FILTERS item 3 stays a measured alternative.
2. **C2b identity** (statement first). Drafts in the worktree: `build/c/identity-lib.lisp` (schema,
   spec: block/decide/record/answers/binding/within-bound; reorder answers-over and within-bound-over
   before their callers), `build/c/identity-engine.lisp` (fn2-id-decides machine: start, overlay block
   walk, run-start, run-scan, fold, decide-step, record; needs a `fn2-id-decide-fold*` macro and
   okind/oslot/ogen columns on `fn2-run-installed`), `build/c/registry.lisp` (the installed-runs table
   to append to runs.lisp). Still to write: adapters (offers processed with seals every `split`,
   staging slot released before queries) and the two keystones with teeth, in a new unit
   `fn2/tests/identity-unit.lisp` (assembles the identity schema alone). Design: `defrunschema fn2-identity :id 1 :key ((message-id (:octets
   250)) (content :digest)) :value ((state (:enum fn2-identity-state (:accepted :conflict)))
   (article (:id article)) (binding (:id event)) (principal (:id principal))) :merge :union`.
   Decide(mid,c) over overlays + runs: seek LB (mid, empty digest), iterate the mid block (<= bound+1
   entries): duplicate iff (mid,c) present; conflict iff other content; else stored. Admission of
   conflict evidence under per-mid bound, refusal `:identity-conflict-bound`. Keystones:
   `fn2-exact-identity` (image builds via real admit/seal with split, releases source slots, decides;
   = spec; negative tooth: index built from facts with octets dropped answers :stored on the re-offer
   where spec says :conflict); `fn2-identity-binding-converges` (keys-only Binding + conflicted equal
   for two delivery orders; negative: a node that refuses conflicts and records nothing diverges).
   Interim resident run registry per schema until the manifest (C1c rest).
3. C2c Ribbon per sealed run: homogeneous Ribbon (r=8, w=64; never fails; free rows from a PRNG
   seeded by run id), keyed on Message-ID octets hash, in :partitioned-filter pages, FILTER- ref.
4. C2d IDENTITY checker + M3 in the simulator. Then C3, rest of C1c, C4-C6.

## Pitfalls hit (and what worked)
- Per-schema generated functions must be thin: preconditions checked at run time by generic
  functions proved once. Proving per schema exploded (minutes, failures).
- B's shape lemmas are stated over `-rows` accessors: keep `fn2-pool-rows fn2-fields-rows
  fn2-digests-rows fn2-fc-rows fn2-fc-context-rows fn2-b3-rows` disabled locally; use `:raw-rows t`
  on writer/restart preserves when callers see opened rows.
- Pass scalars, not a stobj that was just updated, to generic helpers (frame lemmas otherwise).
- `fn2-fc-shape` (B's macro) is the cheap way to state shape lemmas: it disables the recognizers.
- Recursive loops over stobjs: put the case logic in a non-recursive step and disable it in the
  loop's measure hints, or the termination proof opens it (minutes).
- `:position nil`-style mistakes: a function returning one stobj still returns `(mv code st)`.
- Name clash: defcolumns generates `NAME-put`; do not name a function that.
- REPL with the worktree's own `tools/acl2`; `ld` of a book that `include-book`s a stale certified
  book conflicts: certify the lower books and include them.
- Never `&` inside a backgrounded Bash call; never chain sleeps; use run_in_background waiters.

- Generated guard proofs: disable a stobj's `-rows` only where a callee changed that stobj (shape
  lemmas use -rows); leave it enabled where element types are read from the recognizer, or the
  prover inducts (build-add failed; lookup-step took 355 s). Split multi-branch stobj functions into
  pure checks + straight-line writes / per-phase helpers, each disabled after definition.
- `(zp lv)` needs natp guard; dispatcher uses `(and (integerp lv) (< 0 lv))` under guard t.
- Disable each generic entry point after its definition; give recursive adapters termination hints
  disabling the step they call.
- Per-event timing: ld the inner forms with summary output on (not the macro) — see it2/it3.lsp.
- `nohup tools/acl2 ... & echo $! > pid` in a foreground Bash call so the PID is the wrapper itself
  (an `sh -c` PID orphans the wrapper when stopped).
- New files: `git add <file>` in the worktree, then `git commit -F msg -- <paths>`.

## Commands that work
- REPL: `cd <worktree> && tools/acl2 --timeout 580 < scratch/it10.lsp` (include certified
  runs-schema, ld runs.lisp, ld the unit body extracted with `sed -n '/^(defrunschema/,$p'`).
- Certify: `sh fn2/tools/certify.sh tests/runs-unit.lisp` (worktree lock; < 1 min at low load).
- Forge: `git push -f fn@forge:/build/fn.git HEAD:refs/heads/fn2/c-found`; in /build/lanes/c
  `git fetch /build/fn.git fn2/c-found && git reset --hard FETCH_HEAD`; `nohup sh build/c1.sh`
  (closure under swarm-build, then `certify.sh --export-owed`; OWED.md written in that tree).
- hbox: `(git ls-files; echo <untracked>) | tar czf - -T - | ssh hbox-saas 'cd
  /tank/fn/scratch/fn2-c/tree && tar xzf -'`; `/tank/fn/scratch/fn2-c/cert.sh` sets FN_ACL2 and
  ACL2_SYSTEM_BOOKS and runs certify.sh under swarm-build.

- Integration: commit in the worktree; in the shared tree `git merge --ff-only fn2/c-found`,
  secrets check, `git push origin dev`.

## Certify times (forge, 8db53928a)
| book | seconds |
|---|---|
| books/runs-page | 24.4 |
| books/runs-schema | 2.0 |
| books/runs | 15.1 |
| books/runs-assemble | 2.1 |
| books/overlay | 4.2 |
| tests/runs-unit | 22.5 |
