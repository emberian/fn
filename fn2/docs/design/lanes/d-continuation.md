# fn2 layer D continuation (present state, rewritten whole; 2026-10-30, the fourth Opus seat)

Seat: Opus, layer D (machines, scheduler over principals, accounting, NNTP over them). The seat WRITES
the code; Codex (second account) takes only bounded pieces with real signatures pasted, every line read;
Astra (`codex exec -m gpt-6-astra -s read-only`) reviews designs as a peer before code. Brief:
`build/coordinator/briefs/FN2-LAYER-D-MACHINES-NNTP.md` over `FN2-SEAT-COMMON.md`. Layer doc:
`fn2/docs/d-machines-nntp.md` on dev: section 4 is D3 as built, section 13 is D7 (design + 2/n, 3/n as
built), section 10 the open items, section 12 the quest table.

## Tree
- Shared tree `/Users/ember/dev/fn` is on `dev`. D's lane worktree is `build/lanes/fn2/d7` (branch
  `fn2/d7`). Foundation-touching work (assembly includes, conn.lisp) is done there, merged with
  origin/dev, gated on forge, then dev fast-forwards (`git -C /Users/ember/dev/fn merge --ff-only fn2/d7`,
  secrets check, `git push origin dev`). Commit with `git commit --no-gpg-sign -F <msg> -- <paths>`; new
  files get `git add -N` first; never stage. Messages live in `build/d-seat/d7-*.msg`.
- Forge clone `/build/lanes/d7` (branch `lane`) is the D gate tree, certified at the 3/n state. Refresh:
  `git push fn@forge:/build/fn.git fn2/d7:refs/heads/fn2/d7`, then in the clone `git checkout -- . &&
  git fetch /build/fn.git fn2/d7 && git checkout -B lane FETCH_HEAD` (rm untracked copies first).
  `/build/lanes/d3b` is the older D clone, now a scratch REPL tree.
- **Stuck process to report/clean**: on forge, pid 427111 (sbcl, a certify of the old
  tests/accounts-unit in /build/lanes/d3b, started 07:58 without a PID file; its forge-certify parent is
  426918). It holds an ACL2 slot. Not killed (no PID file); main or ember may stop it.

## Done (this seat)
| quest | commit | one line |
|---|---|---|
| D7 1/n | 7b12faab9 (dev 1d6cce7ca) | layer doc 13: ledger and scheduler-over-principals design, Astra-reviewed (`build/d-seat/d7-astra-1.md`), seam S1-S6 to A |
| D7 2/n | 424312db7 (dev a98d3c7c5) | `fn2/books/accounts.lisp`: the ledger library; acquire-protected and the charge lemmas proved; ops-conserve owed; `tests/accounts-unit.lisp` |
| D7 3/n | 792a36bd3, 703b5503a, edbda1d0b, OWED d15c0b3c1 (dev a98d3c7c5) | `accounts-core.lisp` (core child, wrappers, seam entry points), fn2-conn booked at the greeting and charged rx/tx/requests, `sim/check-account.lisp` (ACCOUNT), sim-layer-d ACCOUNT + scenario 11 flood half, `fn2-account-ledger-matches` owed with teeth in conn-unit |
Earlier seats: D0, D1a, D2a-c, D3 (see layer doc section 12).

## D7 as built (for the next slice)
- Ledger rows: P+1 (row P = system). Dimension-major arrays; holdings `:connection-row
  :principal-reservation`; charges `:rx-octets :tx-octets :requests :run-steps :run-bytes`. Readers
  `fn2-account-{hold,reserve,limit,charged,committed,capacity}`; core readers
  `fn2-account-core-{hold,charged,limit,reserve,rows,conservedp}`.
- Seam entry points (names A wires; all in macro `fn2-account-events`, `fn2/books/accounts-core.lisp`,
  materialized today in `assembly-callbacks-d.lisp`; A moves the materialization before its own callers):
  `(fn2-account-book p fn2-core) -> (mv code fn2-core)` (S1), `(fn2-account-charge-run principal bytes
  steps fn2-core) -> (mv code fn2-core)` (S2), `(fn2-account-grant-ready-p fn2-core)` and
  `(fn2-account-grant-one fn2-core) -> (mv id fn2-core)` (S5; no grants until 4/n). Also
  `fn2-account-unbook`, `-book-admitted (refused p)`, `-unbook-ref (ref)`, `-charge-core (p k a)`.
  Each wrapper has frame lemmas `<op>-FRAME-<child>` over every other core child.
- fn2-conn: `account-ref` (common field) is the booked ledger row or `*fn2-none*`; greet books via
  `fn2-account-book-admitted`, refused -> 400 like the partition reserve; frame-run charges `:requests`
  before answering; observe-receive/-send charge octets; release unbooks via `-unbook-ref`.
- ACCOUNT (`fn2/sim/check-account.lisp`): `fn2-account-check rows records capacity`, controls
  `fn2-account-controls` (third control `:n/a` without reserves).

## Next
0. (done) READY 2/n+3/n sent with the seam names. A landed S4 (fn2-sched-reattribute, 7fd40d0b7)
   and S6 (:account, used at drain). Main asked A to move `(fn2-account-events)` ahead of its callers
   when it wires S1/S2/S5.
1. D5 first (main/C, 2026-10-30): C's identity decision is linearizable by per-bucket stamps and an
   identity version; `fn2-id-record` refuses `:stale` before any other verdict when either moved since
   the decision began, and a stale offer is offered again. D5's `:identity-reservation` (D0 kind,
   serializing same-Message-ID offers on one node) bounds the retry count: declare it as an arm with
   its cost; WIRE stays one reply per POST/IHAVE/TAKETHIS; run D5's scenario with
   `fn2/sim/check-identity.lisp` on (C's IDENTITY checker, scenario M3). Then D4.
2. D4 (upload) and D5 (transaction) are unblocked (A's read-set 6b2f6ef5b, assembly split 71c1fb2f2;
   C2 identity c06369c9d; doc: `fn2/docs/c-ordered-runs.md`). H's M1a oracle has 713 POST interims for
   D5. Order: D4 then D5, or D5's POST path first if D4's upload machine is the smaller bottleneck.
3. S1 ruling (main, 2026-10-30): the DSL seat lands S1 as ONE commit: the listener books at Accept only
   when the target kind's :admission copies account-ref (echo copies nothing, so A4 never touches the
   ledger); admission copies principal-slot and account-ref and unbooks on a failed Accept or refused
   admission; and it changes fn2-conn-greet to stop booking and keep account-ref as copied (nothing else
   in conn.lisp). Its gate runs sim-layer-d (all four sets) and conn-unit. READ THAT DIFF when main sends
   the sha. S2 (charge-run in the executor, principal and service visits, non-:ok stops :account) and S5
   (grant source fourth; fn2-account-events at the head of assembly-access) are in A's acceptance.
   D7 4/n builds on S1: booking at Accept (move the book from greet), the request bundle
   (`:control-reply` phase, per-principal FIFOs, grant service), run charges, weights, reattribute.
   Then 5/n timers, 6/n TLS admission.
4. Prove `fn2-account-ops-conserve` when cheap (sum over the dimension-major array under one update).

## Certify times (forge, merged tree b587be19f + 3/n)
| book | s |
|---|---:|
| books/assembly-access (A) | 48.4 |
| tests/runs-assembly (C) | 43.7 |
| books/assembly-callbacks-d | 22.6 |
| books/accounts | 9.6 |
| tests/conn-unit | 7.4 |
| books/owed-conn | 6.3 |
| books/conn | 4.7 |
| accounts-core, accounts-unit, check-account | < 1 each |
| tests/sim-layer-d.lsp (LD, 18 runs) | about 3 min |

## Commands that work
- Forge certify (PID file!): `ssh forge 'cd /build/lanes/d7 && (nohup swarm-build sh
  fn2/tools/forge-certify.sh -j 12 > build/cN.out 2>&1 & echo $! > build/cN.pid)'`; wait in a background
  `until ssh forge '! kill -0 $(cat .../cN.pid)'`. Times: `python3 fn2/tools/certify-times.py .
  build/certify-closure.log`. To stop a swarm-build job: its scope from `/proc/$(cat cN.pid)/cgroup`,
  `XDG_RUNTIME_DIR=/run/user/$(id -u) systemctl --user stop <scope>`.
- LD runs with a stoppable PID: `(nohup sh -c "exec tools/acl2 < X.lsp > build/X.log 2>&1" & echo $! >
  build/X.pid)`; stop by killing the sbcl child of that PID (`ps -o pid= --ppid $(cat build/X.pid)`).
- REPL over certified callbacks-a (events only; declaration changes need recert):
  `sh build/d-seat/d7-repl.sh`.
- Drivers: `sh fn2/tools/forge-driver.sh NAME` (A's six, `SECS=7200 ... sim-layer-b`); verdict = no
  "ACL2 Error"/"HARD ACL2" in the log; A4 blocks: copy the a4 log to `build/d-seat/a4-d7/` and
  `python3 build/seat-ad/compare.py build/d-seat/a4-d7 build/seat-ad/baseline-r5e2-a4.log`.
- OWED: `swarm-build sh fn2/tools/certify.sh --export-owed` in the forge tree, copy OWED.md back.
- ld a library + unit quickly: `build/accu-ld.lsp` in d3b (`(ld "fn2/books/accounts.lisp")` ...).

## Pitfalls hit (this seat)
- A defun over stobj arrays: element facts must be rewrite rules (natp/rationalp/acl2-numberp) plus a
  typed reader (`nfix` of the element, disabled) so guards stay linear; index-in-range lemmas stated
  over the normalized `(nth *X-rows* st)` form, rule-classes rewrite and linear.
- Lemmas about `(fn2-X-rows st)` never fire: the accessor opens to `nth`; state them on `nth`.
- An arm that branches on the core (`(if c (mv :ok core) (op core))`) doubles every later subgoal
  (release went 7 s -> 29 s): put the branch inside a wrapper op.
- A recursive driver whose body is big: factor the body into a disabled non-recursive helper, or the
  termination proof grinds for many minutes.
- `cw` takes ~0..~9 only. ACL2 has no lambda arguments. `b*` needs std/util/bstar in sim books.
- defmachine declaration changes (uses/tables) are in conn.lisp's declaration, not the events macro:
  the REPL path cannot test them; recertify from conn.
- Background waits: never `sleep` in a foreground command; use a background until-loop.
