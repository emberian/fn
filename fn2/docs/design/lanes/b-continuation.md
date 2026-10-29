# fn2 layer B continuation (present state, rewritten whole after every quest)

Seat: Opus monitor for layer B (crash/log models, formats, commit batch, allocator, recovery,
checkpoint, cleaner). Brief: `build/coordinator/briefs/FN2-LAYER-B-DURABILITY.md` over
`FN2-SEAT-COMMON.md` (method, one-minute rule, Astra as peer, where builds run). Binding review:
`build/coordinator/fn2/REVIEW-20261028.md` (every diff read whole before commit; quests sized to be
read; REPORT copied per quest; this file records what was read and run). Report to main only
READY/RED/BLOCKED (SendMessage to "main").

## Directives in force (binding)
1. Every remaining quest prompt is prewritten so a handoff is review + launch.
2. Launch the next quest while reading/verifying the previous when files are disjoint; for long
   verification use a separate detached worktree (`b-verify`, below) so Codex can proceed.
3. Codex multi-agent for disjoint pieces only; the top level owns shared docs.
4. WIDTH: A-WIDTH-PER-COLUMN (`a-to-b-width-per-column.md`). `:u64` resident waits on A's native kind.
5. At most one fence in flight per storage domain, kept by the commit machine (built in B3b).
6. REVIEW-SINS-20261028 standing rules (assert never absorb; DSLs generate meaning; layers meet at
   seams). B remedies 12-16 CLOSED and reported.
7. One-minute rule: every quest's acceptance includes the certify-time table; a book over 60 s
   blocks the commit. Never a step/time limit or a weaker statement.
8. DSL metatheory: DM0a (`fn2-declare`, 4cf85c4a8) and DM1 (9cc09f2bf: obligation store
   `fn2-squares`, `defthm-owed` is its view, `fn2-owed` deleted, layer from `fn2-book-layer`) are
   on fn2/main. Every B book that declares carries `(fn2-book-layer :b)` after its includes (16
   books have it, be4bf39ee). OWED.md must carry B's obligations with separate counts (now 109 B
   + 22 A = 131).

## Where things are (2026-10-29 04:45)
- B3c ACCEPTED on 9cc09f2bf as 1b2bc095e (pushed as fn2/b-commit before the rebase). Seat read
  commit-resources.lisp and check-deadlock.lisp whole, machines-b diff and commit.lisp's added
  lines (assert$? = hard error at runtime; real bug fixed: scratch release read commit-io row 6/6).
  Deadlock lines: tiny threads=13 rectangles=2066 deadlocks=0 (both modes); concrete threads=523
  rectangles=4 deadlocks=0; controls MUTEX-ORDER / HELD-NOTIFICATION deadlocks=1 witness (2 2 2);
  CONSERVATION PASS. Note: the HELD-NOTIFICATION control is structurally a lock-order inversion
  (batch/send); a control closer to EXEC §7a (two batches holding both slots while waiting on
  recipients' send capacity) is a B7 refinement.
- fn2/b-commit REBASED onto fn2/main 26570c101 (local, unpushed): 261db654a (B3c) + 901e742d9
  (seat: restored `(fn2-commit-events)` before `(fn2-resolve :callbacks)` and B's 8 unit includes
  above `(fn2-resolve :coverage)` in owed-export.lsp; `-X ours` drops both on every rebase).
- **RUNNING** (Codex): B3c part 2 = DM0b migration, PID file `b-quests/B3c-r2.pid`, log
  `B3c-r2.log`, message `B3c-r2.msg` (callbacks into the restricted b* language, fn2-call; ember's
  decision 2: convert, never widen; needs go to A as notes with the exact form; fn2-input-seals;
  coverage seal; full acceptance incl. concrete sweep). When it exits: copy REPORT.md to
  `B3c-r2.REPORT.md`, read the diff whole, commit, seat certify (b-verify: `git -C b-verify
  checkout --detach <sha>`, build native lib, certify -j 6) + drivers + concrete sweep, push
  fn2/b-commit and fn2/b-durability (force-with-lease; remote b-durability is be4bf39ee), then
  READY to main with the sha (B3b + B3c on current main).
- Next: **BR3** (`b-quests/BR3.prompt`; check declare.lisp on the new base for a `:layout` kind
  first; fill WORKTREE/BRANCH = b-commit / fn2/b-commit). Then B5, B6, B7.
- Worktrees: `b-commit` (Codex), `b-verify` (seat, detached at be4bf39ee), `b-durability` (idle,
  stale checkout). b-trial removed.

## B certify-time table (seat run on be4bf39ee, 97 books, -j 6, all < 60 s)
Full list `b-quests/B3b.seat-cert-times.txt`. Top: assembly-callbacks 50.5, sim-adapter-base 46.7,
assembly-core 46.1, format-check 34.8, merkle 33.6, format-events 29.1, layout 27.4, sim 23.5,
assembly-access 22.9, assembly-reference 22.2, blake3 22.1, format-storage 21.1, echo 17.3,
vocab 14.6, machines-b 11.9; every other book < 12 s. Note: assembly-callbacks (A's section book
that runs B's `(fn2-commit-events)`) is the closest to the line.

## Quests
| quest | state | commit (on 9cc09f2bf) |
|---|---|---|
| B1 crash model + log model + differential | ACCEPTED | in history |
| B2a-B2f layouts, BLAKE3, format, checkers, Merkle, :u64 | ACCEPTED | in history |
| B4a/B4b allocator + retirement FIFO | ACCEPTED | in history |
| B3a HISTORY checker | ACCEPTED | in history |
| BR1, BH1, BR2 remedies 12-16, C BLAKE3, teeth as evaluators | ACCEPTED | 10a0e1d89, 79dc1b485 |
| B3b commit machine | ACCEPTED (seat concrete sweep green, pushed be4bf39ee). Seat read the whole diff: machines-b, commit.lisp (838, whole), commit-alloc, commit-format, commit-proof, commit-history, check-history diff, seam lines; reran on the rebased tree: closure 97 books green; HISTORY units 16/16 6/6 3/3; FORMAT POOL 39/39 x2; KEYSTONE teeth 12/12; format-roundtrip, layout-roundtrip, format-check, crash-model-differential, alloc-random, merkle-random, blake3-native (C 441 MiB/s incremental), core-allocation, A4 driver all rc=0; machines-a-unit now green (A's prefix test). Remedies carried into B3c Part 0 | 456d3365b, be4bf39ee |
| B3c holds/PV/deadlock + B3b remedies | ACCEPTED on 9cc09f2bf; part 2 (DM0b migration) RUNNING | 1b2bc095e -> 261db654a |
| BR3 deflayout through fn2-declare | prompt ready | - |
| B5 recovery, B6 checkpoint/cleaner, B7 decisive scenario | prompts ready | - |

## Review findings carried (B3b, read 02:15-02:25)
- Absorbing: `fn2-commit-resource` (zeros out of range), `fn2-commit-save-pool`,
  `fn2-commit-context`, release-pool's commit-io branch (silent no-op). -> B3c 0a.
- Numbers as meaning: `cb-stage` 0..18, reasons 1/3/4/5/6/255, 12288/4096/4063/4064/96/64/32,
  4294967295 sentinels. -> B3c 0b.
- Eleven hand-written `fn2-commit-*-child-wfp`/`-update-wfp` pairs (SINS A17 shape). -> B3c 0c.
- `fn2-commit-events` ends with global theory edits seen by A's later books: alias rewrite
  `fn2-core-wfp-commit-opaque`, disables of `fn2-core-wfp`, `fn2-outbox-peek`, `fn2-layoutp-head`.
  Exact (equalities), but a B change to A's proof theory: localize or record as stand-in for
  DSL-METATHEORY §4's kit. -> B3c 0d.
- Notify advances one ack per run with no recipient capacity: B3c models notification debt.
- A callback lacks the harvested op token; log edges released per class (A interface need; not
  reported yet: raise with B5 if recovery needs exact per-op release).
- Isolated ack = 12288 bytes (3 x 4 KiB); concrete 16-member batch 768 B/ack (for B7 numbers).

## API later quests rely on
- `fn2-commit-start id members first-key mode partner fn2-core` -> `(mv code fn2-core)`;
  `fn2-commit-run id budget fn2-core` (generated); observer via A's router.
- B1 `fn2-cm-*`, `fn2-lm-*` (docs §4); `fn2-lm-recovery-allowedp` is what HISTORY/RECOVERY call.
- Layout codec docs §5; BLAKE3 docs §6/§8 (digest rows); allocator docs §7.
- `fn2/sim/commit-history.lisp` = recovery stand-in until B5 (`fn2-b-recover`, `fn2-b-manifest*`).

## Commands that work
- Assemble + launch (from b-quests/): `python3 assemble.py <Q> [gt-file]`, then for a fresh
  session `(nohup codex exec -C <wt> --skip-git-repo-check --sandbox workspace-write -c
  sandbox_workspace_write.network_access=false --output-last-message $PWD/<Q>.last.md
  "$(cat <Q>.final.prompt)" < /dev/null > <Q>.log 2>&1 & echo $! > <Q>.pid)`; to resume the
  veteran: `cd <wt> && (nohup codex exec resume <session> --skip-git-repo-check -c
  sandbox_mode=workspace-write -c sandbox_workspace_write.network_access=false
  --output-last-message $D/<Q>.last.md "$(cat $D/<Q>.final.prompt)" < /dev/null > $D/<Q>.log 2>&1 &
  echo $! > $D/<Q>.pid)`.
- Waiting (no foreground sleep): `for i in $(seq 1 57); do kill -0 $(cat X.pid) || break; sleep 10;
  done` in a 600 s Bash call, repeated.
- Certify (zsh: targets must be an ARRAY, `T=(${=$(cat build/seat-b3b-targets.txt)})`):
  `(FN_ACL2_SLOT_DIR=/tmp/fn2-bseat-slots FN_ACL2_SLOTS=6 nohup timeout -k 5 2400 sh
  fn2/tools/certify.sh -j 6 "${T[@]}" --export-owed > build/seat-b3b-cert.log 2>&1 & echo $! >
  build/seat-b3b-cert.pid)`; ~7 min for 97 books. Times: `grep 'Built '` lines.
- Drivers: `build/seat-drivers.sh` in b-commit (12 drivers sequential, status file
  `build/seat-drivers.status`). blake3-native needs `sh fn2/host/build-blake3.sh build/lib` first
  (NOT tools/build_blake3.sh, which lacks fn2's subtree symbol).
- Commit: zsh array `F=(...)`, `python3 tools/secrets_check.py "${F[@]}"`, `git add "${F[@]}" &&
  git commit --no-gpg-sign -F build/commit-<x>.txt`; full `python3 tools/secrets_check.py` before
  every push.

## Pitfalls hit
- zsh does not word-split `$T`: a target list in a scalar reaches cert.pl as one bad path.
- Codex's sandbox cannot open ~/.cache/fn-acl2-slots: every prompt sets FN_ACL2_SLOT_DIR under /tmp.
- A rebase onto a fixed A turns B's gap-evidence regressions red: they assert the defect; flip them.
- `fn2-book-layer` must precede the book's first declaration (blake3's defcolumns is line 5; a
  naive "after the last include" put it after machines-b's mid-file include of commit).
- Heredocs into the coordinator dir were refused once; Write tool / python work.
- A combined session edits shared docs at the end: commit a finished quest's doc hunks first.
