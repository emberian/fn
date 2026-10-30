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

## In flight
**Landing B5-3/B5-2** from the scratch worktree
/private/tmp/claude-501/-Users-ember-dev-minidregg/01a18d5d-691b-72d0-9a7c-08f584d470bb/scratchpad/land
(detached; `git worktree list` in /Users/ember/dev/fn shows it): f5017f2d0 B5-3, 8ce8cb872 B5-2 over
dev 323c9da1d; messages b-quests/b53.msg/b52.msg filled into scratchpad b53.final/b52.final (GATE_LINES
names base 57601292a; refresh it to the final base). Gate history: green at 6bde0055b (b5g), e3573e0af
(b5h), 57601292a (b5i: drivers 7/7, A4 identical but exercised 34/85 vs 34/77, tiny S15 336 S16 12 S13
316 S14 1882, export PASS 509); own books+export green at 762c94853 (511); now the whole gate3 again on
323c9da1d at forge b5i (PID file build/gate.pid) because D5 1/n also edited q1-unit.lisp (catalogue now
98 = 90 + 8 recovery). When green: copy b5i's fn2/docs/OWED.md into B5-2 (`git commit --amend -F
b52.final -- fn2/docs/OWED.md`), amend B5-3's message (needs the B5-3 commit amended first: checkout
the B5-3 sha, amend, cherry-pick B5-2, amend), secrets check (python3 tools/secrets_check.py),
`git push origin HEAD:refs/heads/dev`, READY with both shas. Q1 judge: does not refuse the recovery
kind (it names conn/echo/listener/scribe only; recovery has no control record, owed like fn2-commit).
Forge scripts: /build/lanes/b51/build/gate3.sh (T=<tree>), drivers.sh, a4blocks.sh.

**B5-4a** in /Users/ember/dev/fn/build/lanes/fn2/b-machine (branch fn2/b: WIP commit 60cf26a47 plus
uncommitted fixes) still on the OLD base 6bde0055b + old B5-3/B5-2; after landing, rebase it onto dev
(drop the two old commits). It certifies locally through the whole assembly and
tests/commit-member-unit.lisp passes (refused leader/pair, outcomes :refused, frontier restored).
Uncommitted on top of the WIP: commit-alloc.lisp cancel/free shape lemmas (Codex, read and certified),
commit.lisp fixes (abort-state nfix, pick disabled, end-abort guards, hook -RESULT-CONSP, abort event
from the root recipe), machines-b.lisp :format-slots default/floor (+ 4 :large-upload-windows) (main's
ruling; absent windows key = 0), machines-c-bind defattach hints, the unit's expectations.
Still to do in B5-4a: hook defcosts with (:layers :c :d) for fn2-runs-install and fn2-member-replay
(e3573e0af); the whole gate (S13/S14 counts may change); b-durability.md §11 B5-4 from b54-design.md.

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
