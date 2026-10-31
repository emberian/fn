# fn2 machine-form seat continuation (present state; rewritten whole after every commit)

Seat: Opus, writes the code; Astra for read-only review. Brief: main's launch prompt (2026-10-30 night) +
`build/coordinator/briefs/FN2-SEAT-COMMON.md`; method: `build/coordinator/fn2/WORKFLOW-20261031.md` (W1: certify my
changed books + touched units + the scenario for what I touched, read the diff, push, READY; main gates the tip nightly;
at ~400K distill myself and continue). Statement: `build/coordinator/fn2/MACHINE-FORM-20261030.md` §6 (6.5 placement
P1-P4 as amended, 6.9 built, 6.10 where every seat's ask lands).

## Landed (dev)
| sha | what |
|---|---|
| d04660248 | G1: machine-arms.lisp (step language + generator), A's probes declared, 32 hand callbacks deleted |
| 6f05dbba0 | placement probe (tests/form-probe-kind, -unit) |
| 516c2daf3 | P1: ready-prev/ready-next/wait-reason in the directory (`*fn2-machine-directory-fields*`, kind `:table`); sixth grant source `fn2-batchable-*` |
| 9a453bffd | P2/P3: arm-children.lisp (ops over children, core faces as stobj-let wrappers, defcost `:child`); generator child form `(defmachine-arms K :children)` / `:wrappers`; echo + scribe arms proved in machines-a-run.lisp with no core (27 s); listener stays core form (registry arms) |

## How child form works (for editing the generator)
- env `:children` = `(K fn2-machines fn2-pool fn2-ops fn2-control)`; `fn2-arms-callee` maps an op to its defcost `:child`;
  `*K-KIND*`/`*K-ADMISSION-ORDINAL*` become formals `kind`/`ordinal`; writes via `K-PUT-CHILDREN id slot ...`
  (machines.lisp) returning `(mv K fn2-machines fn2-control)`; stop = `fn2-control-record-stop`.
- Child fn `NAME-CHILDREN (id slot kind ordinal budget|event... K m p o c)`; shape theorems `NAME-CHILDREN-SHAPE-0..9`, one
  per child recognizer/invariant, hint closes callees, column readers, `nth`, `unsigned-byte-p min nfix` and the children's
  predicates (without that, 100-400 s per arm: nth openings and type-prescription storms). Tau proves them instantly in
  any world that already has them: REPL experiments must disable `(:executable-counterpart tau-system)`.
- Wrapper `NAME (id budget fn2-core)` = snapshot check, stobj-let of five children, slot from the directory, call.
- Reserved arm names now include `slot kind ordinal` and the child stobj names.

## Next (in order)
1. **G2** (6.10): F1 sub-arm `:on-refusal`; F2 take `(:ok :no-row)` + generation + `(:park :taken K)`; F3 `:answers` on
   drop-prefix / pool-borrows-read-code; F4 owner-declared wait kinds `(:park K)` (generalize `:sealable`/`:batchable`);
   F5 `(:wake-row E)` one wake per path; F7 `row-slot`; F12 reachability report; kind stop reasons (`:stops`, generic
   `:kind` reason + control `stop-kind`/`stop-detail` in exec-state, once).
2. **P4**: assembly as registry (one wrapper + rewrite per kind; listener's registry arms in the registry section).
3. Ports: conn (mine), then commit + recovery, upload, txn (rulings 1, 6, 8), sealer; G3 (F6 repeat, F8 links, F9 hand,
   F10, F11, F13/F14 holds, `:sub`, `:genesis`) after conn.
4. A items: outbound Connect primitive for E (after P4 unless E asks sooner).

## Boxes and scripts
Forge clone `/build/lanes/form-base` = my working tree (rsync books/tests from the worktree; not a git checkout of a
sha any more). `build/p2.sh` = certify A units + callbacks-a + smoke (detached via `build/detach.py PIDFILE LOG cmd`,
results in `build/p2.rc`). Local helper `scratchpad/cert1.sh BOOK...` (session scratchpad
/private/tmp/claude-501/-Users-ember-dev-minidregg/01a190f5-7c4c-7c33-aa50-10891bcd6bc3/scratchpad/) rsyncs and certifies
named books, printing the first error. REPL: `tools/acl2 < build/q.lsp` in the clone. `/build/lanes/form` holds a stopped
baseline at 747afb64c (unused). No detached runs of mine are live.

## Pitfalls
- `(mv-nth 0 x)` rules never fire (it simplifies to car); columns.lisp now states position 0 as `car`.
- A stobj returned from `mv` must be a variable: let-bind `fn2-control-record-stop` first.
- ACL2 flet bodies cannot see outer variables; use a helper function.
- Paren balance per edit (scratchpad parens.py); unused let-bound names are translate errors (declare ignorable).

## Rules
PID files only; never stash / add -A; named paths; secrets check before push; a book over 60 s blocks the commit;
disk < 60 GiB: stop.
