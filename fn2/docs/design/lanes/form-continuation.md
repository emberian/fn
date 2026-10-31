# fn2 machine-form seat continuation (present state; rewritten whole after every commit)

Seat: Opus, writes the code. Brief: main's launch prompt (2026-10-30 night) + `build/coordinator/briefs/FN2-SEAT-COMMON.md`;
method `build/coordinator/fn2/WORKFLOW-20261031.md` (certify the changed books + touched units + the scenario, read the diff,
push, READY; main's nightly gates; distill at ~400K and continue). Statement: `build/coordinator/fn2/MACHINE-FORM-20261030.md` §6
(6.5 placement as amended, 6.9 built, 6.10 the language as built and where the asks land).

## Landed (dev)
| sha | what |
|---|---|
| d04660248 | G1: machine-arms.lisp (step language + generator); A's probes declared; 32 hand callbacks deleted |
| 6f05dbba0 | placement probe |
| 516c2daf3 | P1: ready-prev/ready-next/wait-reason in the directory; sixth grant source |
| 9a453bffd | P2/P3: arm-children.lisp; child form `(defmachine-arms K :children)` / `:wrappers`; echo + scribe in child form |
| 7a0edee7a | G2: defwait, take answers + `(:park :taken K)`, `:repeat`, `:wake-row`, row-slot, hand/accept-hand, `:stops`, sub-arm `:on-refusal`, reachability |
| cb903f15c | P4: `(defmachine-registry K)` (admit/take in the kind's book: echo, conn, upload, txn); per-kind observe routes; `:answers` without `:ok` |
| 24fce1ecd | per-arm stobj tuples (`fn2-arms-child-emit`, table `fn2-arms-child-sigs`): cursor 1,339 -> 501 s |
| 82eb2bfc2 | one shape theorem per function (`FN2-ARMS-OK-<k>-<children>` defun-nx, opened only on a result tuple; per-child corollaries); guards with readers/K and directory rows/predicates/stobj callees closed and tau off; per-child core inits (INIT-<field>, closed profile predicate, make-event :or fallback); liveness control on fn2-pool-reserve. cursor 501 -> ~90 s, machines-a-run 20.5 -> 6.5, conn 15.5 -> 9.5, upload 19.3 -> 13.8, txn 21.8 -> 12.3, assembly-init 91.5 -> 41.7 |

## How the generator works now (for editing it)
- The walker generates child-form code over the kind's whole tuple (K fn2-machines fn2-pool fn2-ops fn2-control . EXTRA, E's
  pre-pass). Every child-form function goes through `fn2-arms-child-emit` (make-event): `fn2-arms-scan` finds reads/writes,
  `fn2-arms-narrow` rewrites terminal `(mv x.. . T)` to the function's OUTS and calls of recorded functions to their TAKES (tail
  calls widen). The sig (TAKES RETURNS K) goes in `fn2-arms-child-sigs`; faces, :goto and :repeat read it.
- Shape: `fn2-arms-ok-shape-events` (one theorem + corollaries); total < 2 results keep per-child lemmas. Corollary proofs must
  disable the shape theorem itself (else the :use hypothesis rewrites to T).
- Guard hints close readers, `K-ROWS`/`fn2-machines-rows` only (other children's rows stay open: their raw nth facts need it),
  shape fns, stobj callees (`fn2-arms-stobj-callees`); tau off. Registry (defmachine-registry) the same, with ubp open.
- Reserved arm names: slot kind ordinal and the child stobj names.

## Next (in order, from main 10-31 evening)
1. **:local listener** (for E's consumer socket): owner-only (0600) Unix socket at the profile's path beside the TCP
   listener, simulator host and native loop; Accept's peer record for :local carries w0 = uid, w1 = gid (getpeereid on Darwin,
   SO_PEERCRED on Linux). Pieces read: `fn2/host/ffi.lisp` (fn2-native-listen, -accept: family 1 already maps to :local),
   `fn2/host/adapter.lisp` (listener cap index 0; fn2-n-start-ready's accept), `fn2/books/vocab.lisp` fn2-peer-recordp (today
   :local must carry zeros: allow w0/w1, keep port/w2/w3 zero), `fn2/books/host-boundary.lisp` fn2-host-listener-bind (add
   :listener-path), tests/host-unit.lisp (local records). Plan: one listener capability muxing both fds (Accept takes whichever
   is ready), so the listener machine is unchanged; the simulator's accepts may produce :local peers with uid/gid.
2. **G3** (the conn port's language): F8 typed links (+ hand owner = holder owed row), F10 phase-valued fields, F11 per-phase
   precision, F13/F14 holds per call/per path, `:sub` and `:genesis` (sealer), `:repeat` cost derivation.
3. **Assembly per-child books**: assembly-access 52 s (2,191 per-field events: per kind x field writer facts over fn2-core;
   move to the kinds' books or one generic instantiated theorem), rows-other 29 s, reference books ~40 s each (mostly
   include and event volume, not proof), assembly-init's remaining 20 s fn2-core-init-wfp; the per-kind run rewrite
   (`kind = K => fn2-machine-run = K-RUN`) for the executor (73 s: transition preserves 28 s of which tau 18 s, but closing
   tau and callees there made it 247 s; needs the rewrite, not hints).
4. Listener's registry arms (fn2-machine-admit over the admitted kinds' children); outbound Connect.
Asks routed elsewhere: D's fn2-cursor-render preserves 17 s (close callees, tau off); C's read ops returning only what they change.

## Boxes and scripts
forge only while hbox is down. `/build/lanes/form-base` = my working tree mirror (rsync books/tests from the worktree;
`build/p4.sh` = closure + units + cursor + smoke -> `build/p4.rc`, `build/evtimes.py BOOK.cert.out` per-event times,
`build/l1.lsp` = the A4 driver's setup + fn2-l1-controls only). `/build/lanes/form-cur` = a cursor clone (D's tree at
cb903f15c + my generator; `build/cur2.sh`). Detach with `build/detach.py PIDFILE LOG cmd` (PID file = group leader).
Local `scratchpad/cert1.sh` (session 01a190f5 scratchpad) certifies named books but is NOT detached: a timeout leaves the job
running without a PID file; use detach for anything over ~9 min. `scratchpad/parens.py`: read its "extra close" lines,
never only its last line. No detached runs of mine are live.

## Rules
PID files only; never stash / add -A; named paths; secrets check before push; a book over 60 s blocks the commit; disk <
60 GiB: stop.
