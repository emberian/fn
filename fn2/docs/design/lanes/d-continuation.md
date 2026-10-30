# fn2 layer D continuation (present state, rewritten whole; 2026-10-30, the third Opus seat handing off)

Seat: Opus, layer D (machines, scheduler over principals, accounting, NNTP over them). The seat WRITES
the code. Codex (second account) only takes bounded pieces with the real signatures pasted, and every
returned line is read. Brief: `build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md` over
`FN2-SEAT-COMMON.md`. Layer doc: `fn2/docs/d-machines-nntp.md` on dev. Section 4 is D3 as built:
4.2 the machine and its 32-value field limit, 4.3 the decision table, 4.5 the admission seam, 4.6
acceptance (WIRE, scenario 1, the surface session). Section 7 covers T1 and T8 as built. Section 8 is the
ABI. Section 11 lists the deferred assertions E restores.

## Tree
- The shared tree `/Users/ember/dev/fn` is on `dev`. Commit with `git commit -F <msg> -- <paths>`; new
  files first get `git add -N`; never stage. D's lane worktree is `build/lanes/fn2/d3-conn` (branch
  `fn2/d3-conn`), equal to dev at a95478bce. Assembly edits are made there and fast-forward dev (merge
  origin/dev into the lane first; `OWED.md` conflicts are resolved by taking theirs, then regenerating).
- Forge clone `/build/lanes/d3b` (`ssh forge`, user fn) is on branch `lane` at 90fd04369, plus rsynced
  copies of every later D file. Its closure is certified with the conn.lisp fix. To refresh it: push the
  lane with `git push fn@forge:/build/fn.git fn2/d3-conn:refs/heads/fn2/d3-conn`, then
  `rm` the copies of now-tracked files, `git checkout -- .`, `git fetch /build/fn.git fn2/d3-conn &&
  git checkout -B lane FETCH_HEAD`. `/build/lanes/d3` is an older clone; the reboot freed it.
- hbox-saas (`ssh hbox-saas`) is the fallback build box when forge is down (main's note). Ship the tree
  with `git archive`.
- Scratch: `build/d-seat/` holds the commit messages, `parens.py`, `conn-repl.sh` (REPL-load conn's
  events over a certified callbacks-a), `ss_smoke.py` and `a4-d3/` (A4 block compare input).

## Done
| quest | commit | one line |
|---|---|---|
| D3 3/n | ec9b96173 (dev a95478bce) | scenario 1 plaintext half under the simulator (`tests/sim-layer-d.lsp`): 15 clients, 4 rows, seeds 1-3 with no faults and 11-18 with network faults, WIRE-clean and fixture-exact, 37 s; fix: a zero-octet short send no longer closes; surface hook (`tests/sim-session.lsp` + `tests/surface/fn2_sim_session.py`); interim JSON `tests/surface/fn2_conn_interim.json` |
| D3 oracle | 67d678389 | the fuzz oracle compares D3's 501 in both directions (no DEFERRED list); 0 disagreements on 13,501 lines |
| D3 2/n | 20ecfc4fc (+ merge 90fd04369, OWED 9412139a1) | fn2-conn in the served core; owed-conn (T1, T8 fragmentation and privacy, reader-only interim); WIRE `sim/check-wire.lisp`; conn-unit; Q1 pin 67; OWED 331 |
| D2c | 56bcb0125 | the framer runs on fn2-pool-scan; the octet loop survives only as grammar-unit's reference |
| D3 prefix | 431982c49 | conn-answer library prefix is now fn2-answer- |
| D3 1/n | af591acec | conn-answer.lisp decision table; deferred sub-form checks; 67 spec fixtures (68 since the H7-07 one) |
| D3 design | 430a77b9a | layer doc section 4, section 8, seam request |
| earlier | 27fa4a089 7ead1d598 b121e210e 1ddce858f 615dfde78 90d9405c4 | section 11, D2b oracle and fuzzer, T10, D2a, D0 |

## What D3 is, as built (for the next quest)
- `books/conn.lisp` declares `defmachine fn2-conn` with the `:admission` seam (A's a20fac18f). Its
  fields: cap-index, cap-nonce, rx/tx slot and gen, start, pos, overflow, compacting, cursor, tx-off,
  after, pending, borrows, mask, ordinal, access-ref, auth-pending, refused, stopped, next-free. Those
  are 22 of the 24 a kind can have: the calling convention's mv caps it at 32 values.
- Arms: the idle arm; greet; command, which forwards to frame-run (frame, answer, overflow) or to
  compact-run (drop-prefix); input (reset, compact or Receive); reply (Send by loan; reset TX; move to
  `after`); close; drain, which forwards to release (TX then RX, then `fn2-machine-reclaim-fn2-conn`).
  `:article-input` and `:upgrading` refuse until D4 and D7. The events macro `fn2-conn-events` is
  materialized in `books/assembly-callbacks-d.lisp`.
- `books/conn-answer.lisp` holds the decision table `fn2-answer` over the pool. Its interim replies,
  `*fn2-answer-interim*`, must be empty at D9.
- `books/owed-conn.lisp` holds `fn2-conn-wire-run`, the logical view (clients, chunks, wire and close),
  and 4 owed rows. Their teeth are in `tests/conn-unit.lisp`.

## Next
0. **D7 now** (main, 2026-10-30): the scheduler over real principals and accounting. Extend
   sched.lisp (a seam request to A for edits in A's file) and write accounts.lisp. Principal rows are
   the shared ledger: limits, protected reservations, holdings, maintenance debt, runnable heads,
   weights. fn2-conn is charged to a principal from its first byte. Its scenario runs under the
   simulator, with keystones owed with teeth. Write the design into layer doc section 4 or a new
   section first, against ROUND2 sections B.2 (principal accounts), C (the 80-entry calendar, turn
   bounds, starvation), D0's `:principal-reservation` (rank 6, reserve `:system`) and the `:connection
   :request` bundle. Readable commits, READY per commit. D4 waits for A's form (an assembly split per
   kind, and a read-set snapshot for the field cap), which comes through main.
1. Before D4 registers a kind, A's two fixes must land (main says the DSL seat has both):
   - (a) On the merged tree, assembly-callbacks certifies in 54.8 s and assembly-core in 51.9 s. One
     more kind crosses the 60 s limit.
   - (b) The 32-value limit: snapshot only the fields an arm reads, or split the row. Upload and
     transaction rows need more than 24 fields.
2. D4: the upload machine, with `:article-input` in fn2-conn (block framer, discard to the terminator,
   TAKETHIS's immediate block) and scenario 4.
3. Scenario 1's remaining halves:
   - WORK, TRACE and OWN over D's runs: reuse A's fn2-echo-check-turn and fn2-own-check-trace-turn
     (load echo-scenario).
   - Process-death cuts, once recovery is in the served path.
   - The served half of fuzz-nntp through the sim session.
4. When H wires the hook, watch the first surface S run against fn2 and fix forward.

## Seam notes (sent to main)
- A: (a) and (b) above. The peer address in the Accept result is A5r's. It is declared as the owed
  interim `fn2-conn-reader-only-interim`; it does not block D3.
- The Q1 pin in `tests/q1-unit.lisp` gains every new kind's cases. The OWED.md evidence rows carry
  revision hashes from the evidence files, so a regeneration on a different tree differs only in
  those.
- When R6b makes a bundle atomic, sim-acquisition fails ("owed bundle passes"). Remove that
  bundle's :owed-by in resources.lisp.

## Certify times (forge, merged tree)
| book | s |
|---|---:|
| books/assembly-callbacks (A/B) | 54.8 |
| books/assembly-core (A) | 51.9 |
| books/assembly-callbacks-d | 29.5 |
| books/conn-answer | 21.7 |
| books/nntp-grammar | 17.9 |
| tests/grammar-fuzz | 12.5 |
| tests/conn-unit | 5.8 |
| books/conn | 4.7 |
| tests/grammar-unit (with the D2c equivalence) | 4.2 |
| books/owed-conn, sim/check-wire, tests/conn-answer-unit | < 2 each |
| tests/sim-layer-d.lsp (LD) | 37 |

## Commands that work
- Forge certify: `ssh forge 'cd /build/lanes/d3b && (nohup swarm-build sh fn2/tools/forge-certify.sh
  <books> > build/cN.out 2>&1 & echo $! > build/cN.pid)'`, then wait with `until ssh forge '! kill -0
  $(cat ...)'`. With no books it runs the whole closure. Times come from
  `python3 fn2/tools/certify-times.py . [build/certify-named.log]`.
- Drivers: `sh fn2/tools/forge-driver.sh <name>` for A's six (sim-layer-a-a4-driver,
  core-allocation-driver, sim-allocation-driver, executor-allocation-driver, sim-acquisition-driver,
  sim-layer-a-a4-smoke) and B's (`SECS=7200 ... sim-layer-b`, about 45 min). Compare A4 blocks with
  `python3 build/seat-ad/compare.py build/d-seat/a4-d3 build/seat-ad/baseline-r5e2-a4.log`.
- OWED export: `sh fn2/tools/certify.sh --export-owed` in the tree; it needs every included unit book
  certified.
- Fuzz oracle: `tools/acl2 < fn2/tests/grammar-fuzz-export.lsp > build/nntp-fuzz-cases.txt; python3
  fn2/tests/grammar-fuzz-oracle.py`.
- Scenario 1: `tools/acl2 < fn2/tests/sim-layer-d.lsp > build/sim-layer-d.log`, then grep SIM-LAYER-D.
- Session smoke: `python3 build/ss_smoke.py` on forge (imports `fn2.tests.surface.fn2_sim_session`
  with the repo root on sys.path; never run from inside fn2/tests/surface, whose `operator/`
  shadows the stdlib).
- Interim JSON: `tools/acl2 < fn2/tests/conn-interim-export.lsp | python3 -I fn2/tests/conn-interim-json.py`.
- Iterate on conn's callbacks without recertifying the chain: `build/d-seat/conn-repl.sh` (redef over
  the certified assembly-callbacks-a).

## Pitfalls hit
- Check paren balance with build/d-seat/parens.py before any ld.
- A defthm about `(mv-nth i (f ...))` over an arithmetic let* body case-splits without end; return
  one natural instead.
- Disable each function after its `fn2-pool-preserves` / `fn2-core-preserves` line. Use
  `:hints (("Goal" :in-theory (enable fn2-core-wfp)))` on core-preserves for a stobj-let pool wrapper.
- Reserved and special names: `view` (defcolumns), `fill` (CL), `fn2-conn-field-p` and other
  `fn2-conn-*` names, which defmachine generates for the kind. Keep a library's prefix distinct from
  the kind's.
- defmachine's "Invalid machine declaration" is generic. Evaluate its conjuncts in a REPL.
- D0 effect rows are keyed per (row, operation): one `:uses` entry per operation, even when it is
  called twice.
- Single-value readers (natp via nfix) beat mv readers for guards: the type lemma on mv-nth does not
  fire on `car`.
- A recursive helper with an enabled recursive callee on a quoted list in its ruler expands without
  bound during termination: disable every helper after its defun.
- with-local-stobj's mv-let returns every variable except the local stobj.
- Simulator: every round observes a clock reading, and a held Accept is re-delayed forever, so
  quiescence means no actions and no client octets for N rounds. Network faults need fault budget
  greater than 0; exclude death by its probability.
- SBCL block-buffers a pipe: read a long-lived ACL2 process through a pty. ld sets the cbd to the
  file's directory, so do not set-cbd inside an ld'd file.
- Stopping a swarm-build wrapper by its PID file leaves its children running and holding the lock.
  Record the inner PID, or use another clone.
- zsh: use an array `F=(...)` with `"${F[@]}"` for path lists; `$F` does not split.
