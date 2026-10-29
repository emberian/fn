# E1 mutation definitions

Executed evidence is in [QUALIFICATION.md](QUALIFICATION.md). The unmodified
tiny-profile control returns `:PASS` while its liveness summary contains 133
unattributed drops; A4's full post-run assertions reject that result. M2–M5
are qualified against passing original safety prefixes before this separate
later failure. M1/M6 have explicit parent-run controls.

These six files are frozen test inputs, not certified books. Load one into a
fresh ACL2 process **after** the layer-A books and test functions have loaded.
M2–M6 invoke `(redef!)` and redefine the named function in the ACL2 loop. This
updates both the executable counterpart and raw function, avoiding a raw-only
swap that leaves calls from ideal ACL2 test functions unmutated. No proofs run
after redefinition; the resulting test world is not certification evidence.
`:verify-guards nil` suppresses fresh guard proofs in this deliberately mutated
world, and does not exempt the mutation from the ordinary run-time monitors.

The source revision is `137695dfc`. The files contain complete replacement
functions, with nonsemantic declaration adjustments where needed. M2 and M4
expand the public `defmachine-callback` row argument convention in
`fn2/books/machines.lisp:320`; their original callback body comes from
`fn2/books/machines-a-run.lisp:35`.

| ID | Original source and single semantic change | Named distinguishing contract | Qualification obligation |
|---|---|---|---|
| M1 | `machines-a-run.lisp:82` admission and `:126` reclamation share the allocator. Declaration selects `different-capability` while omitting that allocator. | `E1-client-outcomes`: admission/refusal, per-capability bytes and close/drop histories under the stated occurrence correspondence. | Replay the supplied listener/reclamation prefix and both occurrence orders. Configuration 1 lacks a diamond checker and cannot discover a declaration defect. |
| M2 | `machines-a-run.lisp:35-43`: after the callback writes OFF, a new final writeback reads entry `ROW-OFF` and restores it. | Independent client byte equality (or its bounded progress contract if no conflicting byte is read). | A legal nonempty send followed by another send of the retained window. This is a synthetic stale-snapshot defect; no claim that this exact form existed historically. |
| M3 | `executor.lisp:24`: harvested completion routing is replaced by `(mv 4294967295 fn2-core)`. | Concrete/reference correspondence and TRACE's completed turn contract. | First routed completion in an ordinary echo run. Harvest and operation/pool effects still occur; only the observation callback and its wake disappear. |
| M4 | `machines-a-run.lisp:41`: OFF becomes COUNT rather than OLD-OFF + COUNT. | Independent client byte equality. | Two positive partial send completions from one window. Concrete and reference share this handler, so their agreement is insufficient. |
| M5 | `sched.lisp:127-153`: enqueue is dualized from tail insertion to head insertion, including all previous/next links and head/tail updates. | Principal FIFO selection, checked by TRACE and the independent list scheduler. | Two enqueues on one principal. Echo initialization already enqueues listener(s) and the scribe; an empty environmental choice list may suffice. No corrupt-link shortcut is used. |
| M6 | `sim/sim.lisp:386`: long-latency selection tests fault 2 instead of fault 14. | `E1-delay-class`: at a legal delay call, new DUE = min(2^60-1, NOW + L); L=100 for class 2 and L in {1000,10000,100000}, indexed by WORD mod 3, for class 14. | A pending operation with fault 2 or 14, WORD=0. The original existing echo monitors alone do not establish this adapter timing contract. A campaign latency monitor must be identical in all three configurations. |

Paths in the table are relative to `fn2/books/`, except `sim/sim.lisp`, which
is relative to `fn2/`. Runtime qualifications and saved concrete schedules
belong in the experiment's results and manifest; source inspection alone does
not qualify a mutant. A compile failure, timeout, unexercised mutation or
uncaught mutation is reported in that category, never silently discarded.

## Listener/reclamation prefix recipe

The parent executed the listener/reclamation negative control and saved its
16-choice prefix, reached state and routes in
`../results/listener-prefix.sexp`, `listener-state.sexp` and
`listener-routes.sexp`. The state has free-head=4294967295 and active=capacity=1.
Accept-first closes new capability `(0,3)`; close-first admits it. Both OWN
verdicts are `:PASS` and both stop reasons are 0. The recipe below describes
that construction; the saved concrete prefix is authoritative.
Use the tiny profile with `:c=1` and `:accept-credits=1`, otherwise retaining
its positive capacities, and echo mode. The simulator network has `:c` rows.

1. Initialize, run ordinary turns, and hand off the outstanding Accept.
2. Complete that Accept with fault 26 and word 0, obtaining capability `(0,2)`.
   Run ordinary turns until the listener has handed off its next Accept and
   the occupied echo row has handed off Receive. Hold the second Accept.
3. Complete Receive with fault 3 and word 0. The ordinary simulator environment
   arms a reset after zero physical transfers (`sim-adapter-base.lisp:595`),
   causing failed receive and then an ordinary Close of `(0,2)`. Run turns and
   handoffs until both that Close and the listener's Accept are in flight.
4. The two occurrences are the pending Accept with fault 26/word 0 and the
   pending Close with fault 26/word 0. Post both results before harvesting.
   Replay the entire common prefix afresh for each order.
5. Accept first gives the listener FIFO priority while the echo row is still
   occupied, so admission refuses. Close first gives reclamation priority and
   frees the echo row before admission. Complete the distinguishing subsequent
   Close or Receive through the same legal continuation to obtain the actual
   client-visible close/drop/bytes observation.

`network.lisp:100-123` permits accepting a reset slot and increments its nonce.
Thus the new capability is `(0,3)` in either route; the old `(0,2)` Close is
harmless if it becomes stale. Compare **both capability index and nonce** in
`different-capability`: the listener descriptor has `(0,0)` and the old echo
Close has `(0,2)`. Comparing indices alone would incorrectly reject this
candidate before testing the declaration. The occurrence includes operation
slot, generation and cell as well as its payload/fault. No allocator identifier
renaming is needed for this one-row recipe.

## Qualification driver and recording

`qualify.lsp` loads the existing layer-A echo driver, optionally loads one
mutation, then calls `fn2-sim-run-echo` with one target connection and the tiny
profile modified to one echo row and one listener. It retains the original
broad phase, forced early receive/send faults, handoff deaths and subsequent
200-connection liveness phase. The 120-second and 500,000 combined transition
limits are qualification safeguards; crossing either reports `:censored`.
Loading is reported separately. These are qualification runs, not the frozen
comparative campaigns.

`qualification-hooks.lsp` wraps both raw and executable-counterpart entries,
using ACL2's actual `*1*-symbol` function. A per-call dynamic stack prevents
double accounting when the executable counterpart dispatches to raw Lisp.
The hooks preserve multiple values and are restored on ordinary exit. Runtime
mutation itself is performed only by the in-loop redefinition files.

The output is an ordered S-expression event stream: every PRNG word, every
simulator observation, every actual environment choice with operation and
capability identity, each turn boundary, the first checker failure with exact
turn and core/reference counters, and the result. Capturing all PRNG calls
also captures client-message words and handoff-death draws. `FN2_E1_REPLAY`
replaces PRNG return words from such a saved stream while retaining the
ordinary PRNG's state updates; attempting another PRNG call after the supplied prefix ends reports
`:replay-prefix-exhausted` and stops, without drawing another random word. The output states how many supplied words were consumed and remain.
A same-mutant replay must reproduce the first failure before a witness is
called replay-validated. The semantic occurrence records remain available for
the generator interface's stronger occurrence-preserving paired replays.

The class-specific latency hook runs for ORIGINAL and every mutant, so M6 is
not given a private campaign oracle. All other checks here are the existing
TRACE/WORK/OWN/client monitors. Parent campaign code adds its shared allocator
monitor separately.

From the repository root, after the parent has finished closure certification
and written `build/scenario-revision.lsp`, a qualification launch is:

```sh
nohup env FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 \
  FN2_E1_MUTANT=ORIGINAL FN2_E1_SEED=20261028 \
  FN2_E1_OUTPUT=fn2/experiments/squares/mutants/qualification-ORIGINAL-20261028.sexp \
  timeout -k 5 900 tools/acl2 \
  < fn2/experiments/squares/mutants/qualify.lsp \
  > fn2/experiments/squares/mutants/qualification-ORIGINAL-20261028.log 2>&1 &
echo $! > fn2/experiments/squares/mutants/qualification-ORIGINAL-20261028.pid
```

Use a new output/log/PID path and a fresh process for every mutant and replay.
The parent coordinates the global limit of two running campaigns. Read the
`E1 QUALIFICATION` lines; a process timeout or load error is not a mutant hit.
