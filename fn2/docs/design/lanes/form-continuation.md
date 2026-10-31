# fn2 machine-form seat continuation (present state; rewritten whole after every commit)

Seat: Opus, writes the code; Codex/Astra for proofs and read-only design review. Brief: main's launch prompt
(2026-10-30 night) + `build/coordinator/briefs/FN2-SEAT-COMMON.md`. Statement: `build/coordinator/fn2/MACHINE-FORM-20261030.md`
sections 1-5 (main/ember), **section 6 = this seat's design** (6.2 syntax, 6.3 derivations/checks, 6.4 emitted list,
6.5 placement P1-P4, 6.6 order, 6.7 what layers change, 6.8 Astra's read taken, 6.9 built). Astra's review:
`lanes/form-quests/astra-design.md`.

## Landed (dev, READY sent for each)
| sha | what |
|---|---|
| d04660248 | G1: `fn2/books/machine-arms.lisp` (step language + generator over today's fn2-core carrier); listener, echo, scribe declared in it (`machines-a.lisp`); 32 hand callbacks deleted; `:answers` defcost key; tests ported (callbacks-unit onto fn2-conn-frame-run, machines-a-unit, executor-unit composition tooth, core-child-assembly-callbacks, q1-controls mutation sites). A drivers identical to base modulo rune counts and the now-exact D0 effect table. Intended failure change: listener's 3 ignored unbook results stop with :account |
| 516c2daf3 | P1: ready-prev/ready-next/wait-reason are directory columns (`*fn2-machine-directory-fields*`, kind `:table` = the rest); PUT-CORE / ROW-F / dispatchers route them; frame rows name the directory; sixth grant source `fn2-batchable-*` (B attaches in -b2) |
| 6f05dbba0 | placement probe: `tests/form-probe-kind.lisp` (arm over echo table + pool + ops, no core, 0.74 s) and `tests/form-probe-unit.lisp` (its fn2-core wrapper, guard + PRESERVES in 0.02 s prover) |

Measure after G1 (three probes): kind lines 817 -> 483, hand callbacks 32 -> 0, :unchecked 0; assembly-callbacks-a
66.0 -> 62.6 s CPU (forge, load 3-6). Books over 60 s that predate G1: callbacks-d 79.0 (C-S4's children), init 71.0,
executor 66.9, callbacks-t 61.1, machines-a-unit 60.5. "Certifies alone" is not delivered yet (arms still materialize in
the assembly).

## How the generator works (for a successor editing it)
- `defmachine` (machines.lisp) with `:arms` stores a skeleton `(TAG K-RUN-TAG)` per arm and `:arms :subarms :observe-arms`
  in the row; `fn2-machine-property` reads derived contracts from table `fn2-machine-arm-contracts` for
  `:continuations`/`:observes` (raw row via `fn2-machine-declared`).
- `defmachine-arms K` (machine-arms.lisp, included by `assembly-callbacks-a.lisp` and the test
  `core-child-assembly-callbacks.lisp` only, so generator edits recertify from callbacks-a) walks paths
  (`fn2-arms-steps`/`-do-body`/`-terminal`), env plist (:pending writes, :next, :next-done, :bound, :lets, :written,
  :refusal), acc plist (:charges :nexts :writes :uses :tables :reads :stay :issues). Writes are batched: one PUT before
  every operation call and at the terminal, phase written with the first batch after `:next` (chained inline PUTs
  across an operation fail guard proofs). Calls: positional args, owner triple okind/oslot/ogen filled, other formals
  `:FORMAL E`, stobjs from `stobjs-in`/`stobjs-out` properties.
- Then `defmachine-run K` (unchanged) builds K-RUN, certificates, teeth, owed rows from the derived contracts.

## Next (in order)
Workflow is WORKFLOW-20261031 W1: certify my changed books + touched units + the scenario for what I touched; read the diff; push; READY; main gates the tip nightly. No whole-tree gates of mine. At ~400K distill myself and continue.
1. **P2**: each operation an A arm calls gets a body over its children (`fn2-core-issue` over pool+ops returning a stop reason; pool range ops by handle incl. copy-range (B-TXN-COPY switches to it); parks/grants over the directory; stop over control; finish/charge; ledger ops over accounts); fn2-core faces generated one-stobj-let wrappers. Kind-declared stop reasons go in here: exec-state gets the generic reason :kind and control fields stop-kind/stop-detail; defmachine `:stops (R ...)`; `(:stop R)` routes. Say in P2's READY whether the language expresses identity ruling 6 (committed write with a refusal reply; :uncertain outcome) or which step adds it.
2. **P3/P4**: arms over children (stobjs from the ops' `stobjs-in`), K-RUN wrapper + per-kind rewrite in the assembly; registry arms; `:sealable`/`:batchable` become declared wait kinds with named wakers. Probes certify alone.
3. Ports: conn, commit + recovery, upload, txn (rulings 1, 6, 8 of IDENTITY-ACROSS-PEERS), sealer (`:sub`, `:genesis`, attached wait kind, kind stops).

## Boxes and scripts
Forge clones (`ssh forge`): `/build/lanes/form` (G1 at base plus fixes; acc/g1, g1b, x1) and `/build/lanes/form-base`
(at 747afb64c + P1 working files, certified through assembly.lisp; `build/acc/base` = the cee416335 baseline: certify 1784 s, the seven A driver logs;
`build/acc/g1r` = rebased recertify). In each clone's build/: `gate.sh NAME [nodrivers|full]`, `fin.sh NAME` (closure +
q1 evidence + export), `extra.sh NAME` (q1-controls + judge, crash-model-differential), `cmp.sh BASE NEW [N]`,
`detach.py PIDFILE LOG cmd...` (setsid; PID file = group leader; stop with `kill -- -$(cat PIDFILE)`). Laptop has no
setsid: `lanes/form-quests/launch.py`. A full closure on forge is ~30 min at load 3-6 (the serial assembly chain);
a generator-only edit recertifies from callbacks-a (~20 min to the end).
No detached runs of mine are live (base747 gate in /build/lanes/form was stopped by its PID file; its partial certs are at 747afb64c).

## Pitfalls hit
- Paren balance in long generator functions: check per-clause depth before certifying.
- Every mutual-recursion call must decrement fuel; unused let-bound names are translate errors.
- A test that overrides a kind's `:observes` must override `fn2-machine-arm-contracts` for a new-form kind.
- The worktree's OWED.md and evidence tallies are regenerated outputs: copy them from the forge run into the commit.

## Rules
PID files only (group leader); never stash / add -A; named paths (`git commit -F msg -- paths`); secrets check before
push; one certify at a time; a book over 60 s blocks the commit; disk < 60 GiB: stop.
