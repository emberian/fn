# fn2 layer B continuation (present state, rewritten whole after every commit)

Seat: Opus, layer B. Method (`briefs/FN2-SEAT-COMMON.md`, last sections): dev is the branch; Opus
WRITES the code; Codex only for bounded pieces with real signatures, every line read; READY to
main per commit (SendMessage "main"). Box safety verbatim in COMMON. One-minute rule binding.

## On dev
- 12cd1031f: B library merged (B1, B2a-f, B4a/b, B3a, BR1, BH1, BR2, BM1 port). READY sent.
- 19149d32e: **B3b-1** = converged commit machine (B3b + B3c + DM0b callbacks) ported to R5e1/R5e2,
  with A seams: `assembly-callbacks-a.lisp` (A's continuations; split for the 60 s rule),
  interim `fn2-commit` holds row in resources.lisp (R7 4/n moves holds into defmachine :holds and
  deletes the table; it ports fn2-commit's declaration to arm contracts and keeps the split),
  q1 pin 54. READY sent; layer C started on it.

## Also on dev
- 810a4c376: B seams for C and A (fn2-digest-store, run namespaces, named charges :advance 16 and :stage 32).
- 49ffcd6af: **B3b-2** (commit-proof keystones + unit, OWED 196, sim-layer-b a forge nightly row).
  READY sent with the concrete sweep: S13 10000 PASS, S14 10000 PASS (2000 per fault class),
  768 B/ack at 16 members, 2,736 s wall on forge.
- Branches: b-durability, b-commit, b-done and b-machine are deleted (local and origin). Archive tags
  `archive/fn2-b-durability` (be4bf39ee), `archive/fn2-b-durability-local` (f30d8d387),
  `archive/fn2-b-commit` (ea950f50a) keep the shas the docs cite. Worktrees b-verify, b-commit and
  b-durability are removed. The one lane worktree is `build/lanes/fn2/b-machine` on local branch `fn2/b`;
  rebase it on origin/dev and push `HEAD:refs/heads/dev`.
- Forge clones: /build/lanes/b (dev 19149d32e, sweep), b2 (scratch), b3 (49ffcd6af certified).
- Pending from the DSL seat: a generic contract-assert factoring for generated run/handler
  preservation lemmas (assembly-callbacks 48 s, assembly-core 43 s on forge come from fn2-commit's
  run/handler). Apply it to the commit kind when the form arrives.

## GC2 (agreed with C; build with B5)
Member kind :run-replacement. C's workspace: fn2-format-run-replacement body at 0 (<=167 B),
N in 1..31 fn2-format-dependency-entry records from offset 256 (<=121 B each). Admission
`(fn2-commit-admit-runs schema slot gen body-len entry-bytes entry-count okind oslot ogen fn2-core)
-> (mv code batch fn2-core)`; codes :ok (workspace handed to commit kind) / :exhausted /
:admission (bad decode, N range, an entry extent still has :outstanding-io, schema mismatch).
Record packed with record kind :run-replacement; entries go verbatim into the dependency page;
fence/preflush covers them. Install after root swap calls the constrained hook
`(fn2-runs-install schema batch slot gen okind oslot ogen fn2-core) -> (mv code fn2-core)`
(C amendment a, ruled yes), passing the commit kind's owner triple, read-only by contract; C attaches via defattach; the
default attachment refuses :unregistered; a non-:ok makes the batch uncertain. Uncertain batches never
call it; B5 replays the hook for a durable, uninstalled member. More than 31 pages: an entry whose
TARGET page-kind is :dependency-manifest is a C-sealed page of entries; recovery follows it
exactly one level and checks every listed target.

## Owed / notes
- HELD-NOTIFICATION control is a lock-order inversion; an EXEC §7a-shaped control is a B7 item.
- fn2-exec-now stays unreachable from continuations; B reads scalar fn2-control-now (A ruled).
- Laptop load is 70-250 today; laptop wall times are not measurements. Time on forge.

## Next (handoff point: the seat hit its context ceiling here, 2026-10-29 ~17:00 forge time)
1. **B5 recovery + GC2**, written by the seat (no Codex insulation). The scope is the prewritten
   `b-quests/B5.prompt` (25 lines: read list = b-durability.md whole; STORAGE-DESIGN-ASTRA concrete parts
   F/G/H/I + the recovery-invariants section; ROUND2 §E.4/E.5/F.1/F.2 rows 15-16; SCHOLAR ch. 4 §4.3-4.6).
   The worktree is now `build/lanes/fn2/b-machine` (branch fn2/b), not b-durability. Statement-first: write
   the three keystones as defthm-owed with teeth BEFORE code (`fn2-recovery-never-shortens-intact`,
   `fn2-recovery-broad-bad-tail-unknown`, `fn2-recovery-rollback-needs-witness`). They replace
   `sim/commit-history.lisp`'s stand-in (`fn2-b-recover`) in HISTORY, the delete-the-twin rule.
   Add GC2 (section above, with C's two amendments): `fn2-commit-admit-runs`, the :run-replacement
   member, the constrained `fn2-runs-install` hook (defattach seam; default :unregistered), replay
   of the hook for a durable, uninstalled member, and following :dependency-manifest pages one level.
   Split it into READY-sized commits (machine + checker; scenarios; GC2), each < 60 s per book,
   timed on forge. The tiny sweep is the gate; the concrete sweep is the forge nightly row.
2. When the DSL seat sends its generic contract-assert form, apply it to fn2-commit's generated
   run/handler (assembly-callbacks 50 s and assembly-core 45 s on forge are near the line).
3. B6 checkpoint + cleaner (`b-quests/` has prompts), B7 decisive scenario (STORAGE-DESIGN §7;
   refine the HELD-NOTIFICATION control to EXEC §7a's shape).

## Commands that work
- Forge: `git push fn@forge:/build/fn.git origin/dev:refs/heads/dev`; clones /build/lanes/{b,b2};
  `rsync -aR <files> forge:/build/lanes/b2/` for uncommitted files (never laptop .cert files);
  `swarm-build sh fn2/tools/forge-certify.sh [books]`; drivers `forge-driver.sh NAME` or
  `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g-tls64k tools/acl2 < fn2/tests/X.lsp`.
  ssh to forge drops sometimes: retry.
- Laptop certify (zsh array): `T=(...); (nohup timeout -k 5 3000 sh fn2/tools/certify.sh -j 6
  "${T[@]}" --export-owed > build/X.log 2>&1 & echo $! > build/X.pid)`.
- Per-event profile: REPL `(ld (cdr (fn2-commit-event-forms)) :ld-error-action :continue)` after
  including assembly-callbacks-a; `build/evtimes.py <log>` sorts event times.
- `git reset` is refused by permissions; amend, `git restore --staged`, rebase work.

## API later quests rely on
- `fn2-commit-start id members first-key mode partner fn2-core` -> `(mv code fn2-core)`
  (refuses :admission for non-commit ids); `fn2-commit-run id budget fn2-core`.
- `fn2-commit-idp`, `fn2-commit-partner-state` (:invalid/:failed/:ok), `fn2-commit-checked` macro.
- `fn2-commit-proof-step` in sim/commit-proof-step.lisp; `fn2-digest-store` in format-check.
- B1 `fn2-cm-*`, `fn2-lm-*`; sim/commit-history.lisp = recovery stand-in until B5.
