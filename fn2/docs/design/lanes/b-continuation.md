# fn2 layer B continuation (present state, rewritten whole after every commit)

Seat: Opus, layer B. Method: briefs/FN2-SEAT-COMMON.md (dev is the branch; Opus writes; Codex only for
bounded pieces with real signatures, every line read; READY to main per commit via SendMessage "main").
Main's ruling 2026-10-30 (REVIEW-20261030.md §1, §6): B5, GC2 and B-S2 are B's only work, in order, each
landed under the whole-tree gate (every unit book; A's seven drivers with the A4 summary blocks identical
to a dev baseline; books under 60 s), nothing interleaved.

## On dev
- 717bec1c3 **B5-1**: defcolumns init fresh (resize 0 then n; extras emptied/reset/cleared); controls in
  columns-unit; sim/check-death.lisp (fn2-b-death-difference, -plant-survivor, -death-control) and
  tests/death-unit.lisp. READY sent. Gate: forge /build/lanes/b51 (closure 194 rc 0; drivers 7 rc 0;
  A4 123 summary lines identical to /build/lanes/bdev = dev b25c1ea51 baseline).
- Earlier: B library 12cd1031f, B3b-1 19149d32e, B3b-2 49ffcd6af, seams 810a4c376.

## In flight (worktree /Users/ember/dev/fn/build/lanes/fn2/b-machine, branch fn2/b)
fn2/b = origin/dev 294055805 + three LOCAL commits (rebased 2026-10-30; nothing pushed):
- 903680244 **B5-3** (msg b-quests/b53.msg; GATE_LINES placeholder: amend after the gate).
- 34d0ec870 **B5-2** (b52.msg; EXPORT_LINE placeholder). Content = what was GREEN at 84e6bb293 on
  forge b5w; rebase conflict only in exec-state.lisp's stop reasons (C's :engine-genesis first, then
  :recovery-bounds :recovery-release).
- 55bca6279 **B5-4a WIP** (reword before landing; never push as is). Not certified past
  machines-b.lisp (the assembly needs the nesting fix: children now 35+).
**WAITING** for main's sha of the DSL mv-nesting commit. Then: `git rebase <sha>`; push fn2/b to
forge (`git push fn@forge:/build/fn.git fn2/b:refs/heads/fn2-b`); gate B5-3+B5-2 on forge b5w checked
out at the B5-2 commit (gate2.sh: bdev pulled to dev, certify, drivers both trees, tiny gate, export;
detached under setsid with a group-leader PID file), diff A4 (a4blocks.sh), amend messages, secrets
check, push the two commits to dev (`git push origin <B5-2 sha>:refs/heads/dev`), READY each.
Then B5-4a: a second forge tree b54 at the WIP commit: closure, commit-member-unit, sim-layer-b tiny.

## B5-4 (statement: b-quests/b54-design.md, after Astra's read b54-astra.md; C said YES to the rename)
B5-4a as written in the WIP commit:
- books/commit-members.lisp: fn2-commit-member (32 rows) and fn2-commit-settled (64 rows; reserve,
  settle, free, take, free-count); certifies locally.
- machines-b.lisp: children fn2-core-commit-members/-settled; commit fields cb-wrote cb-open dep-bytes
  rec-bytes; state :dropping (holds batch-membership storage-window; -> :draining); root columns
  aborting abort-event; reason :install 7. exec-state: stop reasons :commit-publish :commit-drop
  :commit-settle.
- commit.lisp: hooks (fn2-commit-hook-events: encapsulate + -UNREGISTERED default + defattach for
  fn2-runs-install, fn2-successor-publish, fn2-successor-drop, fn2-member-replay; constraint
  -CONSTRAINT = corep/wfp + frame over *fn2-commit-hook-frame*); fn2-commit-pick, -admit-keyed
  (n mode okind oslot ogen -> (mv code id batch event)), -put-members, -take, -abort-state, -refuse,
  -fail, abort-aware partner-state (:failed when aborting <= batch), stop-follower refuses unwritten;
  collect closes (cb-open 0); seal failure -> fail (runnable t); writes: follower waits for leader's
  first write, cb-wrote set on issue, issue failure -> fail; publish calls the hook then stops
  :commit-publish on non-:ok; notify settles accepted; drain settles uncertain first and lets a
  dropped batch drain whatever its partner; fn2-commit-drop arm (wait for leader, drop hook, unprepare,
  settle refused, end-abort, -> draining).
- assembly chain now a -> b -> c -> d -> r -> s -> t (-b expands the hooks then part 1).
- machines-c-bind.lisp: C's wrappers renamed fn2-succ-core-publish/-drop, defattach'd (C agreed;
  C's frame proof may need hints at defattach: if it fails, ask C).
- harness: fn2-b-start goes through admit-keyed (checks the row and event it expected, :harness-row
  otherwise); busy-row refusal is now :exhausted (sim-layer-b expectation changed).
- tests/commit-member-unit.lisp: refused leader, refused pair (draft; expectations to be pinned).
Not yet: B5-4b (run member, envelopes, dependency verification, replay), then the commit port, B-S2.

## Commands that work
- Forge trees: bdev (dev baseline, certified), b51 (B5-1, done), b5w (B5 work). Sync uncommitted:
  `rsync -a --exclude '*.cert' --exclude '*.cert.out' --exclude '*.fasl' --exclude '*.port' --exclude docs/ fn2/ forge:/build/lanes/b5w/fn2/`.
- Detached certify (group leader = $!): `ssh forge 'cd /build/lanes/T && setsid sh -c "swarm-build sh
  fn2/tools/forge-certify.sh > build/run.out 2>&1; echo rc=\$? >> build/run.out" </dev/null >/dev/null 2>&1 &
  echo $! > build/run.pid'`; times: `python3 fn2/tools/certify-times.py`.
- Drivers: scratch drivers.sh (copied to /build/lanes/b51/build/drivers.sh): seven drivers under setsid,
  one PID file and .rc each. A4 blocks: /build/lanes/b51/build/a4blocks.sh LOG (summary lines, timing
  stripped); diff against bdev's.
- Commit in the worktree: `git add <new files>; git commit --no-gpg-sign -F msg -- <paths>`; secrets
  check; `git push origin HEAD:refs/heads/dev`; then push dev to forge.
