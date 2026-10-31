# fn2 machine-form seat continuation (present state; rewritten whole after every commit)

Seat: Opus, writes the code; owns layer A's generator and adapter. Brief: main's launch prompt + `build/coordinator/briefs/FN2-SEAT-COMMON.md`;
method `build/coordinator/fn2/WORKFLOW-20261031.md`. Statement: `build/coordinator/fn2/MACHINE-FORM-20261030.md` §6 (6.10 = what is built
and what is open, rewritten with every landing).

## Landed (dev)
| sha | what |
|---|---|
| d04660248 6f05dbba0 516c2daf3 9a453bffd 7a0edee7a cb903f15c 24fce1ecd 82eb2bfc2 | G1, probe, P1, P2/P3, G2, P4, per-arm tuples, one shape theorem per function (see MACHINE-FORM 6.9/6.10) |
| 3804cb211 | Q1 reds fixed forward: q1-unit's pin = the assembled catalogue (110: conn :query + the cursor's 8); q1-teeth's profile serves reading (`:reading t :x 2`) so the cursor has row 0 |
| 56b866c35 | G3 1/n: `:repeat` cost derived, F13 per-call holds, F10 phase-valued fields (hbox: machine-arms-unit, machines-a-unit, cursor-unit, assembly, host-unit certified) |
| 371c48e4e | the `:local` listener: `:listener-path` (0600 Unix socket, the listener capability's second fd in the mux, Accept alternates), `:local` peer record w0 = uid, w1 = gid (getpeereid / SO_PEERCRED), `fn2-host-listener-bind` returns 4 values, the simulator's per-capability peer (`fn2-network-set-peer`, `fn2-network-peer`; `fn2-own-post-result` takes the record and posts Accepts through `fn2-post-accept-result`). Verified: native-serve-check PASS on forge (unix socket served, 0600, removed), sim-layer-a-smoke PASS, host-unit certified |

## How G3 1/n is built (56b866c35; for editing it)
- `:repeat`: the pass function returns passes-left first (child-emit k = 1; core form `(mv n fn2-core)`, `:position 1`);
  the call site binds `<HELPER>-LEFT`; env `:loops` ((LEFT N PB PS PD NB) ...); `fn2-arms-charge-form` adds
  `(* per (nfix (- N (nfix LEFT))))` per dimension and N*per to the static bound. Pass bound = the calls' defcost costs
  summed (`fn2-arms-calls-cost`) + 1 step. `:goto` after a `:repeat` refused.
- F13: `fn2-arms-call` records every call in acc `:calls` (multiset of use forms); contract `:uses` =
  `fn2-arms-uses-multiset`; arms.lisp `fn2-arm-mminus` / `fn2-arm-msubsetp` in `fn2-arm-moves` and `-moves-problem`.
- F10: machines.lisp `fn2-machine-phase-fields`, `-lower-phase-fields` (u8), `-lower-phase-initial`,
  `-phase-fields-problem`; the declaration carries `:phase-fields` only when declared. Generator:
  `fn2-arms-phase-values` checks `:set`; `:next ROW-F` lowers to `fn2-arms-phase-choice` (an if-chain over the subset's
  phase constants: PUT accepts only phase forms over constants).
- Test kinds in machine-arms-unit must have unique names (probe2..7 are taken further down the file).

## Next (in order, from main 10-31 evening)
1. G3 rest: F11 (walk a sub-arm's leaves per caller phase folding `row-phase` tests), F14 (holds per path; a hold
   conditional on a field), F8 (`:links`, `(:live L)`, `(:read L F)`, owner overrides only via a link; owner = holder
   owed row for F9's hand), `:sub` and `:genesis` for the sealer. The conn port (D's P.1 in d-continuation.md, written
   in G1 syntax) is the measure; conn's `after` enum ports to a `:phase-subset` field.
2. Assembly per-child books: assembly-access (52 s), rows-other (29 s), reference books (~40 s), assembly-init's
   fn2-core-init-wfp (20 s), the per-kind run rewrite for the executor (73 s). Before/after numbers on forge.
3. Listener registry arms (admission by peer family into E's kind); outbound Connect.

## Boxes
hbox is up: certify there (`ssh hbox-saas`, tree `~/form-g3`, a plain copy of the worktree's fn2/ tools/ acl2-projects,
not a git repo, so sim-layer-a-smoke's scenario-revision step fails there; run smoke on forge). Launch:
`setsid sh build/X.sh > build/X.out 2>&1 < /dev/null &` then find the `sh build/X.sh` pid with ps and write it to the
PID file (the `$!` of the ssh wrapper is not the group leader). hbox home has ~41 G free. Forge: `/build/lanes/form-base`
(a copy at dev + this seat's landed work; `build/detach.py PIDFILE LOG cmd`), the measurement box and the native/smoke
runs. When sed-templating scripts, never substitute `l2`-like tokens that also match `acl2`.

## Rules
PID files only; never stash / add -A; named paths (zsh: list paths literally, a variable does not split); secrets check
before push; a book over 60 s is its owner's to fix; disk pressure: stop and tell.
