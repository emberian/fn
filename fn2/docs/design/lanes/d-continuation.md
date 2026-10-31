# fn2 layer D continuation (present state, rewritten whole; 2026-10-30 night, the eighth Opus seat)

Seat: Opus, layer D. The seat WRITES the code; Codex (`codex exec -m gpt-6-astra -C /Users/ember/dev/fn`)
only for bounded pieces with real signatures. Brief `build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md`
over `FN2-SEAT-COMMON.md`. Layer doc `fn2/docs/d-machines-nntp.md` §15 is D6 (design, statement first,
Astra's review folded in, rulings recorded in §15.8). macOS has no `setsid`: detach with
`nohup perl -MPOSIX -e 'POSIX::setsid(); exec @ARGV' CMD ... & echo $! > X.pid` (the pid is the group leader).

## State
- dev (this seat): **c01f87b6a** "fn2 D6: the query cursor, statement first" on origin/dev (on
  f794c78f3; gate: whole closure + export green at e9acc2c5b, own books + export green at f794c78f3).
  It is the rebase of the shared tree's local 5b65f7154 (same files but OWED.md); the shared tree's
  dev still carried 5b65f7154 on cd2b74e48: main resets it to origin/dev (`git reset --keep`) —
  §15 of the layer doc, `fn2/books/owed-cursor.lisp` (subject `fn2-cursor-run profile seeds later
  transcripts`: articles seeded and published through C-S3, one batch each; reference
  `fn2-cursor-spec-wire`; owed rows `fn2-cursor-reply-exact`, `fn2-cursor-range-cost`,
  `fn2-cursor-view-pinned`), `fn2/tests/cursor-unit.lisp` (teeth: the reference against hand-written
  replies, its negatives, the seeding publishes and the served core still answers the interim 503),
  registered in `fn2/tools/owed-export.lsp` after txn-unit. Laptop: owed-cursor 12.4 s, cursor-unit 12.2 s.
- Earlier seats: D4 2/n 57601292a; D5 1/n 4ed6172b1; sim-session 323c9da1d, e0f1377a3; A5r peer 10e454049.
- The cursor profile `*fn2-cursor-profile*` raises `:identity-overlays` to 32 and the 4 KiB pool class
  to 48 slots: each seeded batch takes one private overlay + arena per schema (4) and nothing retires
  them before C1c's sealer (seeding the second article hit `(:stage :full)` at the defaults).
- Rulings received (main, 2026-10-30): C-S4 is D's to write as `fn2/books/machines-c-read.lisp`
  (layer :c, machines-c-groups pattern), a foundation commit under the whole-tree gate, C reads the
  diff, B reads the `fn2-b-field-rows` line, with C's five binding amendments (layer doc §15.8:
  stripe layout below the sealer's, per-step staleness re-checks, frontier from a `:published`
  column C adds to `fn2-id-engine` in `fn2-succ-publish`, LIST as an ordered scan not a range read,
  identity read through the decision path's lookup). C-S3a is C's (landing; C sends the sha).
  S-ARTICLE-LOCATION recorded for B-S2/C5. The taken-kind + TX hand-over design is accepted.
- Worktree `build/lanes/fn2/d6` (branch fn2/d6, from dev cd2b74e48) for the C-S4 foundation commit;
  the branch was re-pointed at origin/dev + the D6 commit; the machines-b draft (`*fn2-b-read-stride*`,
  `fn2-b-read-rows`, the `+ stride·R` term in `fn2-b-field-rows`) is saved as
  build/coordinator/fn2/lanes/d-quests/d6-machines-b-draft.diff
  (re-apply by hand: B5 changed machines-b.lisp since). Forge tree `/build/lanes/d6` (clone of /build/fn.git; push dev there
  with `git push fn@forge:/build/fn.git dev:refs/heads/dev`, then `git -C /build/lanes/d6 pull
  --ff-only /build/fn.git dev`; rsync uncommitted files). Its `build/c1.sh` = own books + the whole
  closure + export (status in build/c1.status). Forge `/build/lanes/d5` deleted (dead scaffold).
- hbox `/tank/fn/lanes/fn2-d5` is behind dev: re-copy before use.

## Next, in order
1. **C-S4 first half** in the worktree (foundation): `machines-c-read.lisp` after machines-c-groups;
   assembly-index includes it instead of machines-c-groups; assembly-callbacks-c materializes
   `(fn2-read-core-events)`. Plan:
   - capacity `R = (fn2-b-read-rows profile)` = `(if (fn2-profile-get :reading profile) x 0)` and
     `*fn2-b-read-stride*` 1,024, both in machines-b.lisp (fn2-b-field-rows needs them before C's
     books; name it in the message; the cursor kind's capacity uses the same function).
   - field stripe of read row x: `base(x) = rows − 1024·t − SEAL − stride·(x+1)` (SEAL = the
     sealer's 1,280 once C's machines-c-sealer lands; 0 before); regions: lo key at +0 (80 rows), hi
     at +80, lookup reader at +160 (`*fn2-run-reader-fields*`), source heads after (8 ×
     reader-fields); assert it fits the stride (if reader-fields > 96, lower the sources or raise
     nothing past 1,024 — C capped the stride).
   - core children through `fn2-idc-child`: `fn2-ranges` (R rows), `fn2-range-sources` (8R),
     `fn2-seeks` (R); grow `fn2-succ-txns` to t + R rows (read row x's exact-lookup continuation is
     succ-txns row t + x, so `fn2-xl-step` serves it unchanged: the generalization by allocation
     recorded in §15.9) and `fn2-run-cursors` to t + 9R (lookup cursor t + x, source cursors
     t + R + 8x + i), `fn2-run-paths` to levels × that; `fn2-idc-profilep` gains the u32 checks and
     `+ R·stride` in its field inequality.
   - ops (pool/stobj level, then core wrappers with `fn2-core-preserves`, defcosts in the book):
     `fn2-read-key x region j value`, `fn2-read-key-octets x j slot gen off len okind oslot ogen`,
     `fn2-read-lookup x sid budget -> (mv code erow)` (fn2-xl-step, tx = t + x), `fn2-read-range x sid
     pfield plimit` (fn2-range-start g = x), `fn2-read-next x budget` (fn2-range-step), `fn2-read-value
     x f` (entry at the range's OUT), `fn2-read-octets x f from n dslot dgen dk ds dg -> (mv code
     copied)` (the fn2-idc-copy loop, incremental), `fn2-read-seek x lo hi p pfield` /
     `fn2-read-seek-step x budget`, `fn2-read-frontier` (C's `:published`), `fn2-read-release x`.
   - range.lisp exports no shape lemmas for fn2-range-start/step or fn2-seek-start/step (its adapters
     use local stobjs): prove them with `fn2-ra-shape` as range.lisp does for advance-all.
   - **Base it on C's sealer machine (7a6680f71, landing on 5674cae12) when main sends the sha, not
     before** (main, 2026-10-30): the sealer's six children and its field stripe are what the read
     stripe sits below; then SEAL = `*fn2-b-seal-field-rows*`.
   - gate: whole tree on forge (`build/c1.sh` pattern: every unit book + A's seven drivers with the
     113 A4 blocks identical + export), then land; C and B read the diff.
2. **D6 1/n** (D's books): `fn2/books/cursor.lisp` (the taken kind, §15.2; own section book
   `assembly-callbacks-d-cursor`), conn's `:query` phase and fields `query query-gen group current
   view` (view pinned at the greeting from `fn2-read-frontier`), `fn2-answer` answering `:query` for
   GROUP LISTGROUP NEXT LAST STAT OVER XOVER, the TX cycle with cancellation (§15.3; conn's release
   wakes its cursor), pages restart the read at `next` (§15.4), GROUP's numbers at the view
   (positioned seek + tail count, §15.1); teeth turn to served = spec; regenerate
   `fn2/tests/surface/fn2_conn_interim.json` (tests/conn-interim-export.lsp); READY so H reruns.
3. D5 2/n's B-independent parts between D6 commits (overview row with its Xref line through C-S3a,
   addr entries, generated Message-ID injection), and the durable POST when B-S2's sha arrives.
4. D6 2/n (identity read, LIST scan, HDR), D6 3/n bodies, D7 4/n.

## Pitfalls hit (this seat)
- ACL2 `substitute` with `:test` is not ACL2; write the replace by hand.
- The shared tree's certs churn under other seats (another seat's cert.pl was rebuilding executor
  and conn-unit); `certify.sh` serializes on `build/fn2-certify.lock`, and the laptop export fails
  on any stale test cert (owed-unit's book-hash): run the export on forge.
- Plus the seventh seat's: `(mv :x (f fn2-core))` is illegal; re-check snapshot codes after core
  changes; one wake slot per run; arm names must avoid K-<table op>; Q1's case catalogue lists a new
  kind's cases; forge-certify needs acl2-projects and FN_ACL2.
