# testing-setup (wave 0, Opus) -- final entry, 2026-10-04

Brief: scratchpad fn-briefs/testing-setup.md. Branch `lane/testing-setup`
(origin, public). Worktrees: `build/lanes/testing-setup-wip` (the branch);
`build/lanes/testing-setup` is the d4e53323c measurement tree (holds the
filed certify run's logs under build/acl2/), left for ember's ruling on
stale worktrees. Nothing else of this lane is on disk.

## What landed (all merged to next/dev unless marked)

| sha | what |
|---|---|
| e9c777125 | docs/testing.md: one way to run each kind of test |
| 081404293 | 23 orphan tests/acl2 books wired as ACL2_BOOKS roots; resource-operation-tests deleted (subject in no world); includes added to host/web-host, web-post-stream-tests |
| 07d690b4a | raw runner discovers every tests/native_*_raw.lisp; 51 one-line .sh wrappers deleted; 7 unreproducible REPL probes deleted; matcher_heap -> tools/; 6 ACL2-world scripts needs-acl2 |
| 9cd1567fb, d1aa91e5a, b05eb1d18 | native_source_check 27 failed -> 0 (210/210) |
| f7a1265e8 | 65 fnn-core-stubbing fixtures renamed *-mock.lisp, out of 24 proofs + 11 requirements; test enforces it; harness_check test-stubs 4 -> 0 |
| 1036e0b97 (READY at exit) | reach_check: per-file content memo + no per-theorem table copies; byte-identical output; laptop 79-172 s -> 23 s cold / 6 s warm |
| 100d1b7bb (READY at exit) | ledger.Reader.line incremental: host_check --load --bare 765 s -> ~125 s, the make check critical path |

Evidence: certify-20261004T021712Z-3895962 (persvati, filed): 20 of 23
new roots green at d4e53323c; red roots are their subjects' theorems
(owner-operation-report; nntp-auth / consumer-reason closure).

Counts: ACL2 test books 24 orphans -> 23 wired, 1 deleted. Raw harnesses
30 runner-less -> 22 run by the discovered runner (16 as-is, 3 trace probes
made self-contained, bp_root_cleanup + 2 web fixed), 7 deleted, 1 moved to
tools; 51 wrapper scripts deleted. Fixtures: 65 renamed -mock. Native
source modules: 27 failing -> 0 (17 source-drift fixed or trimmed, 1
deleted, 2 skip bugs, 9 harness modules + 16 raw harnesses brought to the
host). make check, laptop, `make -k check PYTHON=python3.12`, cold then
warm in one tree: before (d4e53323c, load ~5) 13:40 / 12:51, of which
host_check --load --bare 720 s; after (100d1b7bb merged with next
6dfbc4c04, load 11-27) 5:08 / 3:36 (90 steps, 53 cached warm).  Different
trees and loads: re-measure on one quiet box (continuation item 10).

## Continuation (not started; each its own commit, READY to the assembler)

1. host_check --load: the remaining ~110 s is book_holes (~41 s), the
   forward-reference pass (~31 s, both builds) and interface_step's
   static half (~44 s): all ledger-reader parses of the same files,
   uncached. Memoise per file by bytes exactly as tools/reach_check.py
   now does (file_forms / memoised), or share callgraph's cache.
2. ledger: analyze_book (~12 s) re-parses every book on any edit (the
   tree cache is whole-tree keyed; suspects are already per-theorem
   incremental, C8). Per-book memo of analyze_book by bytes; then
   check_problems' green_check.audit and host_names' per-host
   book_closure_definitions (35 s profiled) are the next targets.
3. Path-scoped check-lane (coordinator ask): check_steps.py already
   records each step's traced inputs (build/check-cache/steps/*.json);
   expose `check_steps.py select --changed <paths>` that keeps the steps
   whose last trace read a changed path (and every never-traced step),
   and a `make check-lane PATHS=...`.
4. Baseline diff (coordinator ask): `check_steps.py execute --baseline
   build/coordinator/check-baseline-<sha>.txt` printing NEW reds vs
   baseline and exiting nonzero on new reds only.
5. certify preflight on the laptop against a synced cache index
   (farm.py/certify_books.py --dry-run), not on loaded hbox.
6. proof_repl must accept run-origin certs (certs.choose_entry refuses
   worktree-origin entries from another worktree as foreign-local; check
   how run-origin entries are treated in proof_repl's install path).
7. proof_repl replace-event / send-range without a restart on a
   restatement.
8. certify_books --affected-by --lane: stop at the lane's books plus their
   direct host includer, not every image-world umbrella.
9. tests/test_extract_callback_world: routed to root (re-extract the
   09-30 guarded world with tools/extract, or delete if parked).
10. make check after/before on one quiet box (persvati via
    remote_check.sh, cold then warm, at d4e53323c and at the D6 sha):
    the laptop was at load 20-125 during this lane's measurements.
