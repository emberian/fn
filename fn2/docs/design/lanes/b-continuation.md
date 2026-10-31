# fn2 layer B continuation (present state, rewritten whole after every commit)

Seat: Opus, layer B. Method: briefs/FN2-SEAT-COMMON.md (dev is the branch; Opus writes; Codex only for
bounded pieces with real signatures; READY to main per commit via SendMessage "main").

## Standing rulings (2026-10-31)
WORKFLOW-20261031: no whole-tree gate per commit; seats distill at ~400K and continue. B owns its order;
only the twelve arms' port waits for MACHINE-FORM. Earlier tonight: do NOT start the commit arm port in
the old form (defmachine + hand-written defmachine-callback arms, one
shared assembly re-proving every kind, per-octet exports). Stand by for main's statement of the new form;
fn2-commit is its first B kind. The port's input in any form is the arm table and the absorb list below.

## On dev
- 747afb64c **B5-4a** (landed 2026-10-31 on 6f05dbba0; READY sent): the member and settled tables,
  admission (fn2-commit-pick, fn2-commit-admit-keyed), refusal as a suffix abort with :dropping, the
  four hooks with refusing defaults (C attaches publish/drop), settlement and fn2-commit-take; events
  from 1; the derived format rows (fn2-b-upload-windows); four commit section books (-b, -b2, -r,
  -r2); the harness on fn2-turn. Gate on forge (f2ed887f7, bdev 6f05dbba0): closure rc 0; drivers 7/7
  both trees; A4 identical but Q1 34/101; sim-layer-b S13 306 (reorders 86, tears 130), S14 2046, S15
  326, S16 12; export PASS. Published: sim-allocation full restart 51.1 MB -> 73.1 MB allocated.
  Message: b-quests/b54a-final.msg + the gate paragraph (worktree build/b54a.msg).
- B5-3 2062b2f74, B5-2 5674cae12, B5-1 717bec1c3; earlier B library 12cd1031f, B3b 19149d32e/49ffcd6af.

## Next (owned order; WORKFLOW-20261031; BRICKS-20261031 §5 is the program order)
Landed: named stops 75adea036; the envelope c0ae11af4 (record header = event envelope; §11b S9/S10).
Landed: B-S2 6d4e7f977; the section split c4dde2215 (assembly-callbacks-bt between -b and -b2;
forge -b 45 s, -bt 41 s, -b2 48 s); E's control-connection format rows cd45d4719 (fn2-b-ctl-rows :control-connections default 2,
fn2-b-ctl-slot = 4+w+S; floor 4+w+c; amended: the slot's own 128-row stripe, no stripe below the reads);
B-S2's three keystones ca3aded2b (commit-proof.lisp over
fn2-commit-txn-proof-run; teeth in tests/commit-txn-unit.lisp; b-durability.md 11b).
1. **PARKED (ember's spine-only ruling, 2026-10-31).** No B5-4b, B6 or commit port until main wakes
   the seat (the port follows G3). Open items when woken: rebase over C's *fn2-b-txn-field-rows*
   (machines-b's fn2-b-field-rows; txn stripe 1024 -> 2048) when main sends C's sha; the cross-owner
   copy-range is queued at the form seat (then retire B-TXN-COPY); S10's borrow edge and block hash
   come with D4 3/n. The post-landing check at ca3aded2b on forge b54 is green (commit-txn,
   sim-layer-b, commit-proof units over the rebuilt tree). Nothing of B's runs on forge. Standing reds not B's: q1-unit's catalogue pin and a q1-teeth tooth
   reading the generation of a kind with no row in the teeth profile (dev's new kinds).
2. B5-4b replay. 3. The twelve arms' port in the form (stops to :stops).
Forge: tree /build/lanes/b54 (at c0ae11af4's parent + diff). Sync by copying changed files, NOT
git checkout + apply (that touches every file and recertifies the whole chain, ~40 min).
Asks out: C (sealer profilep demands its pool class; C-SEAL-NO-ROW unreachable).
Lessons: stobj positions in mv / stobj-let producers must be the variable; a stop in an arm
returns at once (fn2-commit-stop-arm); zp needs natp, use posp; expected-member fixtures in
sim/commit-history move with the record header.

## fn2-commit's twelve arms as built (input to the port in any form)
Every arm except idle and observe begins with the partner gate: `fn2-commit-partner-state (batch-no, partner)`
reads the partner row's batch-no and phase and root row 0's `aborting`; `:invalid` (partner not a commit row)
stops the core (`fn2-commit-invalid-row`, :machine-phase); `:failed` (an abort at or below this batch, or an
older partner uncertain) goes to the follower stop: pre-write arms `fn2-commit-stop-follower` (cb-wrote 0:
refuse -> :dropping; else :uncertain :predecessor, stopped when quiescent), post-write arms
`fn2-commit-stop-written-follower` (cb-wrote 0 there stops the core :commit-follower). Declared charge of every
arm today: the per-run cap (4096 bytes, 32 steps, 4 descriptors); the actual charge is in the result column.

| phase -> arm | row reads | row writes | children / effects | result charge | next | refusals / failure path |
|---|---|---|---|---|---|---|
| :free idle | phase | - | - | 0 (idle) | :free | - |
| :collect collect | batch-no partner (+gate) | phase cb-open | alloc-edges: prepared-successor edge add (root-edge nil) | 0 bytes, stage, runnable | :seal; gate: :dropping/:uncertain | root-edge non-:ok absorbed by assert$? (owed: stop :commit-edge) |
| :seal seal | batch-no partner cb-stage (+ the step's reads: cb-stage cb-issued member-count cb-cursor cb-seal-len pool-slot pool-gen generation) | cb-stage cb-cursor cb-issued cb-seal-len, phase via seal-advance at the last stage | pool (zero, copy, pack: own slots), fields/fc/fc-context/b3/digests (format checker row 0-1, hasher), commit-root (seal-ready, parent seal) | 4096 bytes, stage, runnable | :seal :dependencies; failure -> fn2-commit-fail :seal (cb-wrote 0 => refuse -> :dropping) | step :bounds/:state => refuse; four asserts in context/format-core/page-hash/seal-context |
| :dependencies writes | batch-no partner phase cb-issued cb-done cb-deps-ok cb-mode cb-wrote pending generation (+ partner's batch-no phase cb-wrote) | cb-issued pending cb-wrote, cb-done/deps/log via writes-finished, phase | ops: fn2-issue-write (dependency unit, role 0), commit-io edge add (io-edge t) | 4096, stage, 1 descriptor | :log-write (deps done) :fence (baseline after deps? per mode) :uncertain :dropping | :exhausted yield; issue non-:ok -> fail :issue (refuse when cb-wrote 0); partner uncertain -> fail :predecessor; follower gate waits (mailbox) |
| :log-write writes | as above | as above | issue-write roles 1-2 (records, seal) with the FUA flag in mode 1 | 4096, stage, 1 | :fence :durable :uncertain | io-edge non-:ok absorbed (assert$?); resource extent not u32 absorbed |
| :fence fence | batch-no partner cb-fence-live cb-fence-ok cb-mode deadline pending (+ partner phase cb-fence-live) | cb-fence-live deadline pending phase | ops: fn2-issue-fence; clock read (fn2-commit-now) | 0, transition, 1 | :log-write (mode 1) :durable :uncertain | deadline passed -> timeout uncertain; issue non-:ok -> uncertain :issue; clock overflow -> uncertain :timeout; busy-polls the clock while runnable (owed: ArmWake) |
| :durable durable | batch-no partner cb-deps-ok cb-log-ok cb-fence-ok cb-failed | phase | extents: fn2-alloc-commit-allocation (the extent becomes committed) | 0, transition | :install :uncertain | flags not all set or allocation non-:ok -> uncertain :durable |
| :install install | batch-no partner | phase | commit-root installed := batch (root-swap nil); alloc-edges installed-root add + prepared-successor drop | 0, stage | :publish :uncertain | swap not ready -> mailbox wait; root-edge non-:ok absorbed (assert$?) |
| :publish publish | batch-no partner | cb-published phase | commit-root published := batch; hook fn2-successor-publish (C) | 0, advance | :notify :uncertain | swap refused -> uncertain :durable; hook non-:ok stops the core :commit-publish |
| :notify notify | batch-no partner member-count cb-acks cb-stage | cb-acks phase cb-stage | settled table: settle member :accepted (published root as evidence); sched: wake the owner if same incarnation | 0, advance | :notify :draining | settle refusal / wake refusal stop :commit-settle |
| :draining / :uncertain drain | batch-no partner phase cb-cursor member-count pending cb-fence-live cb-stage cb-wrote generation | cb-cursor stopped cb-stage phase | settled: settle members :uncertain first (uncertain only); pool: release roles 0-3 (release-pool) | 0, advance / mailbox | :free (draining) ; :uncertain stays (stopped 1) | release code not :ok/:retired absorbed (assert$?) |
| :dropping drop | batch-no partner cb-stage outcome cb-cursor member-count (+ partner phase batch-no) | cb-stage cb-cursor phase | hook fn2-successor-drop (C); alloc: prepared-successor edge drop (when collect ran) + cancel reservation; commit-root seal-ready 0; settled :refused; root row 0 frontier restore (end-abort) | 0, advance | :draining | an older partner still dropping -> wait; hook or unprepare non-:ok stop :commit-drop |
| observe (:write-result, :fence-result) | cb-issued cb-done cb-bytes cb-failed cb-fence-live phase pending | cb-fence-live cb-done cb-bytes cb-fence-ok cb-failed outcome cb-reason phase | commit-io: drop the io edges when the last write completes (drop-io) | handler | :uncertain from any phase (stray or failed result) | drop-io codes absorbed (assert$?) |

## Where commit.lisp and alloc.lisp absorb (27 `assert$?`: ACL2's er hard? at run time, the shown value in the logic)
commit.lisp (22): fn2-commit-resource :160 (index out of range -> (mv 0 0 0 0 0)); fn2-commit-reserve-extent :195;
fn2-commit-save-pool :222; fn2-commit-release-pool :244; fn2-commit-reserve-pools :261 (release on failure not
:ok/:retired); fn2-commit-release-pools :274; fn2-commit-frontier :284 (no root row 0 -> zeros);
fn2-commit-prepare-root :315; fn2-commit-ready :321 (make-runnable refused); fn2-commit-root-edge :456 (resource
bounds); fn2-commit-collect :547 (root-edge code); fn2-commit-context :604; fn2-commit-format-core :625;
fn2-commit-page-hash :637; fn2-commit-seal-context :669; fn2-commit-io-edge :802; fn2-commit-drop-io :827;
fn2-commit-writes :898 (extent not u32) and :910 (io-edge code); fn2-commit-root-swap :981 (no root row 0);
fn2-commit-install :1131 (root-edge code); fn2-commit-drain :1189 (release-pool code).
alloc.lisp (5): fn2-alloc-reserve :247, fn2-alloc-retire :372, fn2-alloc-unlink :402, fn2-alloc-free :420,
fn2-alloc-checkpoint-drain :459 (each a free/retired/pending list-link shape check).
Each becomes a named stop reason with a control in the port (one reason per family: :commit-resource,
:commit-pool, :commit-root, :commit-format, :commit-io, :alloc-links).

## Commands that work
- Local certify (Mac, slot pool): `sh fn2/tools/certify.sh -j 6 -k <books>` from the worktree, detached
  with `python3 -c "import os; os.setsid(); ..."` writing build/cN.pid (macOS has no setsid binary).
- REPL diagnosis: copy a unit to fn2/tests/zz-b-probe.lsp with assert-event -> a printing macro, ld it
  from build/probe (paths relative to the tests dir), then delete the probe file.
- Forge: `ssh forge`, trees /build/lanes/{bdev,b54}; drivers /build/lanes/b51/build/drivers.sh; A4 blocks
  /build/lanes/b51/build/a4blocks.sh.
Pitfalls: editing a book while its certify runs breaks the run (book-hash mismatch); commit.lisp is
included by machines-b, so any commit.lisp edit recertifies C and D above it (~25 min on the laptop).
