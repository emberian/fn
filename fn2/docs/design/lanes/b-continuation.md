# fn2 layer B continuation (present state, rewritten whole after every commit)

Seat: Opus, layer B. Method: briefs/FN2-SEAT-COMMON.md (dev is the branch; Opus writes; Codex only for
bounded pieces with real signatures, every line read; READY to main per commit via SendMessage "main").
Main's ruling 2026-10-30 (REVIEW-20261030.md §1, §6): B5, GC2 and B-S2 are B's only work, in order, each
landed under the whole-tree gate (every unit book; A's seven drivers with the A4 summary blocks identical
to a dev baseline; books under 60 s), nothing interleaved.

## On dev
- 2062b2f74 **B5-3** and 5674cae12 **B5-2** (landed 2026-10-30 on cd2b74e48; READY sent). Whole gate on
  323c9da1d (forge b5i): closure, drivers 8/8, A4 identical but exercised=34/98 (dev 34/90), tiny S15 336
  S16 12 S13 316 S14 1882, export 554/549/97; Q1 judge does not refuse the recovery kind (no control
  record, owed).
- 717bec1c3 B5-1; earlier B library 12cd1031f, B3b-1 19149d32e, B3b-2 49ffcd6af, seams 810a4c376.

## In flight: B5-4a
Worktree /Users/ember/dev/fn/build/lanes/fn2/b-machine, branch fn2/b = dev 5674cae12 + two local WIP
commits (e74e6c178, 7900ca65d; squash/reword at landing) + uncommitted hook defcosts in machines-b.lisp
((:layers :c) / (:layers :c :d), e3573e0af). Assembly chain on dev is a -> c -> d -> d-conn -> d-conn2 ->
d-upload -> d-txn -> b -> r; B5-4a makes it a -> b -> c -> ... -> d-txn -> r (-b includes -a, -c
includes -b, -r includes -d-txn). Before the rebase it certified locally through the whole assembly and
tests/commit-member-unit.lisp passed. Next: local recertify on the new base, then whole gate on forge
(gate3.sh with T=<new tree>), S13/S14 counts compared, b-durability.md §11 B5-4 from b54-design.md,
squash into one commit, land, READY. Then B5-4b (run member, envelopes, dependency verification,
replay), the commit port (ruling 3), B-S2 (D's :ready calls (fn2-commit-admit-txn slot gen bytes okind
oslot ogen fn2-core) -> (mv code batch event fn2-core); D's interim of that name exists on dev and is
replaced; a :full/:exhausted waiter is woken through the grant service, form stated with B-S2).

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
