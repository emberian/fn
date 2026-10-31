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
| 24fce1ecd | per-arm stobj tuples: `fn2-arms-child-emit` (make-event) narrows each child-form function to the children its paths read (takes) and write (returns); sigs in table `fn2-arms-child-sigs`; :goto/:repeat/face bind by sig; shape lemmas only for returned children. Cursor (D's tree) 1,339 -> 501 s; machines-a-run 31.3 -> 20.5 s |
| cb903f15c | P4: `(defmachine-registry K)` (admit/take in child form in the kind's book; echo, conn, upload, txn), directory ops `fn2-machines-partition-install` / `-park-taken`; per-kind observe routes `fn2-machine-observe-route-K`; `:answers` lists without `:ok`. callbacks-a 55.4 -> 17.6 s, dispatch 44.6 -> 27.8 s |
| 7a0edee7a | G2: defwait wait kinds (generated grant service), take answers + generation + `(:park :taken K)`, `:repeat` (pass functions K-REPEAT-SITE-I), `:wake-row`, `row-slot`, hand/accept-hand ops, `:stops` kind reasons (foundation `:kind` + control stop-kind/detail), sub-arm `:on-refusal`, reachability `:unreached`; tests/machine-arms-unit.lisp |
| 9a453bffd | P2/P3: arm-children.lisp (ops over children, core faces as stobj-let wrappers, defcost `:child`); generator child form `(defmachine-arms K :children)` / `:wrappers`; echo + scribe arms proved in machines-a-run.lisp with no core (27 s); listener stays core form (registry arms) |

## How child form works (for editing the generator)
- Per-arm tuples (24fce1ecd): the walker emits over the kind tuple; `fn2-arms-child-emit-events` scans the body
  (`fn2-arms-scan`: reads = tuple symbols outside terminal mv tails; writes = tuple binders, callee sig outs) and
  rewrites it (`fn2-arms-narrow`: terminal `(mv x.. . T)` -> `(mv x.. . OUTS)`, calls of recorded functions get their
  own TAKES, tail calls widen to the caller's OUTS). A new emitter of child code must go through `fn2-arms-child-emit`.
- env `:children` = `(K fn2-machines fn2-pool fn2-ops fn2-control)`; `fn2-arms-callee` maps an op to its defcost `:child`;
  `*K-KIND*`/`*K-ADMISSION-ORDINAL*` become formals `kind`/`ordinal`; writes via `K-PUT-CHILDREN id slot ...`
  (machines.lisp) returning `(mv K fn2-machines fn2-control)`; stop = `fn2-control-record-stop`.
- Child fn `NAME-CHILDREN (id slot kind ordinal budget|event... K m p o c)`; shape theorems `NAME-CHILDREN-SHAPE-0..9`, one
  per child recognizer/invariant, hint closes callees, column readers, `nth`, `unsigned-byte-p min nfix` and the children's
  predicates (without that, 100-400 s per arm: nth openings and type-prescription storms). Tau proves them instantly in
  any world that already has them: REPL experiments must disable `(:executable-counterpart tau-system)`.
- Wrapper `NAME (id budget fn2-core)` = snapshot check, stobj-let of five children, slot from the directory, call.
- Reserved arm names now include `slot kind ordinal` and the child stobj names.

## Next (in order) — PAUSED by ember's ruling (10-31): spine only until the cursor and B-S2 land; main wakes me
1. The `:local` family Unix listener + peer uid/gid in Accept (E's consumer socket) — first when woken.
2. P4's remainder: the listener's registry arms (fn2-machine-admit over the admitted kinds' children, in a registry section), the per-kind run rewrite (`kind = K => fn2-machine-run = K-RUN`, stopped-row interception in K-RUN).
3. Ports (conn mine; commit/recovery, upload, txn, sealer by seats), G3 (`:repeat` cost, F8 links, F10, F11, F13/F14, `:sub`, `:genesis`), outbound Connect.
Notes: executor.lisp is 70.6 s (over the minute before P4; transition/service preserves 28 + 19 s). A child-form kind parking on :principal-reservation needs D's park op to name a :child.

## Boxes and scripts
Forge clone `/build/lanes/form-base` = my working tree (scratchpad now /private/tmp/claude-501/-Users-ember-dev-minidregg/01a191a8-05db-77e8-8974-3ca1139560de/scratchpad, cert1.sh and parens.py copied there) (rsync books/tests from the worktree; not a git checkout of a
sha any more). `build/p2.sh` = certify A units + callbacks-a + smoke (detached via `build/detach.py PIDFILE LOG cmd`,
results in `build/p2.rc`). Local helper `scratchpad/cert1.sh BOOK...` (session scratchpad
/private/tmp/claude-501/-Users-ember-dev-minidregg/01a190f5-7c4c-7c33-aa50-10891bcd6bc3/scratchpad/) rsyncs and certifies
named books, printing the first error. REPL: `tools/acl2 < build/q.lsp` in the clone. `/build/lanes/form` holds a stopped
baseline at 747afb64c (unused). No detached runs of mine are live (forge `/build/lanes/form-base`: `build/p4.sh` = certify + smoke, `build/evtimes.py BOOK.cert.out` per-event times).

## Pitfalls
- `(mv-nth 0 x)` rules never fire (it simplifies to car); columns.lisp now states position 0 as `car`.
- A stobj returned from `mv` must be a variable: let-bind `fn2-control-record-stop` first.
- ACL2 flet bodies cannot see outer variables; use a helper function.
- Paren balance per edit (scratchpad parens.py); unused let-bound names are translate errors (declare ignorable).

## Rules
PID files only; never stash / add -A; named paths; secrets check before push; a book over 60 s blocks the commit;
disk < 60 GiB: stop.
