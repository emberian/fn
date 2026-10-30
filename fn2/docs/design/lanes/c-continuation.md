# fn2 layer C continuation (present state, rewritten whole after every commit)

Seat: Opus, layer C (the ordered-run metadata engine). Method of 2026-10-29
(`briefs/FN2-SEAT-COMMON.md`): dev is the branch; Opus writes the code; Codex only for bounded
pieces with real signatures pasted; READY to main per commit. Brief:
`briefs/FN2-LAYER-C-ORDERED-RUNS.md`. Layer doc on dev: `fn2/docs/c-ordered-runs.md` (design,
seams, schemas, read contract, keystones, quest plan, interim decisions). Box safety verbatim in
COMMON.

## Landed
- 181df0df0 C1a: `:schema` declaration kind. 8dfba6db2 C1b: run pages and defrunschema (page
  level), layer doc. 1e823b06f C1b': multi-page build, verified-page cache, resumable lookup
  cursors, `NAME-run-lookup-exact`; GC1 closed (R6a1 compare). 37ba641da boxes.md hbox fallback.
  READY sent for each.
- Worktree `/Users/ember/dev/fn/build/lanes/fn2/c-found` (branch fn2/c-found) is reset to dev
  37ba641da, clean apart from certificates. forge clone `/build/lanes/c` (branch fn2/c-found on
  forge's bare repo) and hbox `/tank/fn/scratch/fn2-c/tree` are scratch.

## Next (in this order; the critical path is A6 -> B3 -> B4 -> B5 -> C2 -> C3 -> D3)
1. **Assembly dispatcher (C-GLUE-UNVERIFIED's remedy), before more per-schema glue grows.** Design:
   a `fn2-run-assemble` event macro (run once in a top-level book after every `defrunschema`;
   test units call it after their schemas) generates `fn2-run-layout-decode/-encode/-size/-compare
   (lid ...)` as `case` dispatch over the registered schemas' layouts (rows of table
   `fn2-schemas`, `:layouts`), their shape lemmas by cases, and then the generic build-add,
   promote, index-nth and lookup-step written ONCE over the dispatcher and guard-verified there.
   defrunschema then emits only layouts, registration and adapters. Measure: assembly cost with
   2 and 9 schemas; per-schema expansion should fall to the deflayout time (~3-5 s).
   Main (2026-10-30): accepted C-GLUE-UNVERIFIED with this remedy as the obligation, and made it
   C1c's FIRST item. Record an owed row with teeth: a certify-time check that refuses any
   registered schema whose build/lookup glue is not guard-verified once the dispatcher exists
   (positive tooth: the assembled test schemas pass; negative tooth: a schema declared with the
   old unverified glue is refused by name).
2. **C2 identity** (layer doc §4, FILTERS-2026 items 1-3, UC §4.3): schema `fn2-identity`
   (key message-id `(:octets 250)` + content `:digest`; value article, binding ref, state,
   event; merge `:union`); the bounded active overlay (resident sorted table, defcolumns, fed by
   the prepared successor; per-Message-ID conflict bound with refusal `:identity-conflict-bound`);
   InfiniFilter for the overlay (never delete a non-member); Ribbon per sealed run (built at seal
   into `:partitioned-filter` pages, referenced by the run descriptor's FILTER- ref); the decision
   function stored/duplicate/conflict; the IDENTITY checker; keystones `fn2-exact-identity` (T9)
   and `fn2-identity-binding-converges` with teeth; M3 (lookup after bodies and journal
   placements are reclaimed). Ribbon/InfiniFilter are bounded, well-specified pieces: a Codex
   helper quest is reasonable once one filter has been done by hand.
3. C3 ordered schemas (metadata, overview, addr) + range cursors with resume key and version,
   positioned seek, M2.
4. C1c sealer machine + manifest schema + run descriptor + GC2 member use (B builds the member in
   B5; agreed form in the layer doc §8: hook gets the commit owner triple; >31 pages through
   C-sealed `:dependency-manifest` pages followed one level by B5).

## Handoff (2026-10-30)
This seat is past its context ceiling (about 750K); a successor starts from this file and the
layer doc. Nothing is in flight: no background jobs, no uncommitted C work, no PID files of mine
alive (forge `/build/lanes/c/build/c1.pid` and hbox `/tank/fn/scratch/fn2-c/cert.pid` name
finished runs).

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

## Certify times (laptop)
| book | seconds |
|---|---|
| books/runs-page | 19.5 |
| books/runs-schema | 1.7 |
| books/runs | 11.7 |
| tests/runs-unit | 27.3 |
