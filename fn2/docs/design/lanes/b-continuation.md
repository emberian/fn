# fn2 layer B continuation (present state, rewritten whole after every commit)

Seat: Opus, layer B. Method: WORKFLOW-20261031 (a commit = the changed books certify, the touched
scenarios pass on the tiny profile, the author read the diff; push to dev; fix forward). READY to main
per commit via SendMessage "main". Design record: fn2/docs/b-durability.md (§6, §11a, §11b).

## State: CONVERGE (ember, 2026-11-01): stopped, nothing in flight
Dev tip with B's last commit: 71a9f55bc. Worktree /Users/ember/dev/fn/build/lanes/fn2/b-machine
(branch fn2/b) is clean and equal to dev. Nothing of B's runs on forge, hbox or the Mac. Forge b54 holds
dev 0022ac2f8 + the posture files (committed since) with certs current.

## On dev (B, newest first)
- 71a9f55bc fn2-commit-posture (S11: :serving/:draining from the commit rows' phases; defcost
  :answers (:serving :draining) on fn2-core-machines; no :child yet, see §11b S11) and
  fn2-commit-take's :child fn2-cs-take. Checked over C's §4a 0022ac2f8 (*fn2-b-txn-field-rows* 2048):
  commit-txn-unit, sim-layer-b, commit-proof-unit green.
- c0645b91e docs: Argon rulings (§11b S11 posture, S12 one encoding; §6 geometry => import).
- cd45d4719 E's control-connection format rows: fn2-b-ctl-rows (:control-connections, default 2),
  fn2-b-ctl-slot = 4+w+S, floor 4+w+c (amended: the slot's own 128-row stripe, no stripe below reads).
- ca3aded2b B-S2's three keystones (commit-proof.lisp, fn2-commit-txn-proof-run; teeth in
  tests/commit-txn-unit.lisp). c4dde2215 the B-S2 section book assembly-callbacks-bt (-b 45 s, -bt 41 s,
  -b2 48-51 s on forge).
- 6d4e7f977 B-S2 (admission, seal verbatim, :batchable, stream-wake hook, S9 source ref, S10 block read).
- c0ae11af4 envelope fields in the record header; 75adea036 the 27 assert$? -> named stops;
  880e5edad §11b statement; 747afb64c B5-4a; B5-3 2062b2f74, B5-2 5674cae12, B5-1 717bec1c3.

## Exact next step (when main wakes the seat; spine-only otherwise)
1. S12 record kinds at D's txn port: when main sends C's list (the record kinds fn2-successor-emit
   writes: acceptance, the five identity records, membership, overview, addr, the folds' events, the
   outcome), add each to the record-kind enum (format-events.lisp) and *fn2-commit-txn-record-kinds*,
   extend fn2-commit-txn-body (commit.lisp section 1t, -bt) with one branch per kind calling its
   generated decoder with the exact-length check (next = end), and extend commit-txn-unit's
   verbatim fixture with one record of each kind. Certify -bt, -b2, commit-txn-unit, sim-layer-b.
2. Posture's :child: once the form seat says how a kind reads the commit rows' phases in child form
   (the commit table in D's txn tuple, or a directory column), give fn2-commit-posture that body.
   :child bodies for fn2-commit-admit-txn and fn2-commit-txn-source come with the commit port.
3. Owed, not started: keystone subjects on fn2-turn (Argon §9.2, OWED priority at M2); B5-4b replay;
   B6, B7; the commit arm port after G3; B-TXN-COPY retires when the cross-owner copy-range lands; S10's
   borrow edge and block hash with D4 3/n.
Standing reds that are not B's (seen at cd45d4719): q1-unit's catalogue pin; a q1-teeth tooth reading
the generation of a kind with no row in the teeth profile.

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

(These 27 are named stops since 75adea036; kept as the arm port's input.)

## Commands that work
- Forge: `ssh forge`, tree /build/lanes/b54 (detached at dev). Certify detached with a group-leader PID
  file: `(setsid sh -c "echo \$\$ > build/X.pid; exec > build/X.out 2>&1; swarm-build sh
  fn2/tools/forge-certify.sh -j 8 <paths>; echo rc=\$? > build/X.done" < /dev/null > /dev/null 2>&1 &)`;
  stop with `kill -TERM -- -$(cat build/X.pid)`. Per-form times: awk over the .cert.out (Form:/Time:).
- REPL probe on forge: write /tmp/b-*.lsp, run `../../tools/acl2 --timeout N < probe` from fn2/tests
  or fn2/books.
- hbox (ssh hbox-saas): / and /othersys were at 40-41 GiB free on 2026-11-01, under the brief's 60 GiB
  stop line, so B used forge.
Pitfalls: editing a book while its certify runs breaks the run; machines-b and commit.lisp sit under
almost everything, so a change there rebuilds the tree (~45 min on forge). A slow proof is usually an
inline body case-split: make the body its own function with fn2-core-preserves.
