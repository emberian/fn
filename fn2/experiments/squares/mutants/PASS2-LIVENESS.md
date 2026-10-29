# E1 pass 2: the first ORIGINAL liveness drop is a refused admission

The first unmodified live-phase drop is a genuine rejected connection: the
listener refuses admission while the sole echo row is still occupied, and
the server subsequently closes the new capability with all 703 supplied
bytes unechoed. It is not merely a lost-client-record or completion-accounting
error. Raising QA from 4 to 5 makes the displayed capacity inequality strict
and leaves this witness unchanged. Equality in that inequality is therefore
not necessary for this failure.

This does **not** refute ROUND2-ASTRA C.3's scheduling-opportunity guarantee.
`fn2/docs/design/EXECUTION-MODEL-ROUND2-ASTRA.md:295-301` distinguishes service
opportunities from request completion and explicitly requires available
dependencies and protected reservations. The failed extension is the A4
workload's claim that every physical network accept completes an echo under
its displayed numerical premises; those premises do not establish an
available echo row at listener admission.

## Executed witness

Two fresh ACL2 processes ran the original `fn2-sim-run-echo`, seed 20261028,
one safety connection, then its unchanged live phase. Both start with the
one-row tiny profile used in E1: C=1, accept-credits=1, O=8, H=4, K=8, Aturn=8.
The second changes only QA from 4 to 5. Both assert `fn2-core-profilep` and the
same two capacity predicates used by
`fn2/tests/sim-layer-a-a4-driver.lsp:38-41`.

| Control | H predicate | Descriptor/operation predicate | First live drop | Core/reference transitions |
|---|---|---|---|---|
| QA=4 | 4 > 3 | min(8,4)=4 >= 2*1+1+1=4 | turn 59, capability (0,4) | 514 / 514 |
| QA=5 | 4 > 3 | min(8,5)=5 > 2*1+1+1=4 | turn 59, capability (0,4) | 514 / 514 |

The files `pass2-liveness-qa4.sexp` and `pass2-liveness-qa5.sexp` contain all
273 PRNG words and the observed semantic events. All **294 records after the
profile record are exactly equal** across the two controls. Each process
stops immediately after the first live drop. These probes are diagnostics,
not timed mutation campaigns, and do not classify each of the later 132 drops.

| Turn | Observed event | Consequence |
|---|---|---|
| 54 | Client reads the final 24 bytes of old capability (0,3), reaching 280/280 echoed, marks it `:ECHOED`, and calls network close. | The network slot is closed, but no echo-row reclamation has run. |
| 54 | Live adapter physically accepts new capability (0,4) in that slot. | Network acceptance can precede reclamation of the old machine row. |
| 55 | Client sees nonce 4, counts one accepted connection and supplies all 703 bytes. Old record is already terminal `:ECHOED`. | The fresh-nonce `lost` counter is zero; no old unfinished record is being counted as lost. |
| 56 | `fn2-listener-admit` sees free-head=4294967295 and active=capacity=1; sets listener phase 1 (`:closing`). | Actual allocator refusal occurs before any pool reservation attempt. |
| 58 | Server adapter closes capability (0,4), with network code changing `:OK` to `:CLOSED`. | This is an executed server close, not a client accounting inference. |
| 59 | Client record still has nonce 4 and death-epoch 1, sent=703, received=0 and expected=703; it becomes `:UNATTRIBUTED`. | One real unfulfilled connection is reported dropped. No nonce change or process death explains it. |

The witness logs each admission twice because the existing TRACE checker runs
`fn2-ref-turn` and then `fn2-turn` (`fn2/sim/check-trace.lisp:11-12`). They are
the corresponding reference and concrete executions, not two client
admissions. Both make the same refusal decision. The last completed turn's
TRACE/WORK/OWN verdict is `:PASS`; the client-round verdict is also `:PASS`,
while its returned drop count is one. The allocator stop reason remains zero.

## Why the premises and accounting differ

1. **Network acceptance is not row admission.**
   `fn2/sim/network.lisp:100-113` accepts a non-open network slot and increments
   its nonce. `fn2/sim/echo-evidence.lisp:68-69` performs the live Accept whenever
   the workload still allows more clients; it does not require an available
   machine row. `fn2/sim/echo-scenario.lisp:123-137` counts a fresh network nonce
   as accepted. The core has not necessarily admitted that capability yet.
2. **Admission explicitly depends on a different resource.**
   `fn2/books/machines-a-run.lisp:82-88` checks the echo free head and active row
   count. A missing free row selects closing. The listener issues the actual
   Close at `:117-121`. Reclamation returns a row to the free chain and lowers
   the active count only in `fn2-connection-release` at `:135-145`.
   Neither H>3 nor min(O,QA)>=2*C+accept-credits+1 implies that reclamation has
   already occurred. The QA=5 control demonstrates this distinction beyond
   the equality case.
3. **Attribution is incomplete, but the drop is real.**
   `fn2/sim/echo-scenario.lisp:79-83` classifies a closed network capability
   without a newer death epoch or reset as `:unattributed`, returning a drop
   while retaining `:pass`. A specific admission-refused attribution would
   improve the diagnosis. It would not make the missing 703 bytes appear.
   The separate lost-record branch at `:123-125` is false at the relevant
   transitions: at turn 55 the previous record is terminal, and at turn 59
   the nonce is unchanged.
4. **The inner `:PASS` does not assert zero drops.**
   `fn2/sim/echo-scenario.lisp:334-335` stops both safety and live rounds once
   echoed+dropped reaches the target and returns `:pass`.
   `:446-459` retains the safety verdict and appends live statistics without
   checking live dropped=0. The stronger checks are the A4 caller's explicit
   accepted=echoed=200 and dropped=0 assertions at
   `fn2/tests/sim-layer-a-a4-driver.lsp:87-89`.

Layer A should explicitly distinguish physical accepts, admitted connections
and refused connections, preserving their conservation accounting. If the
liveness claim is intended only for admitted connections, admission and its
reserved resources must be a stated premise of that claim and its monitor.
If it is intended for every physical accept, the workload/core design must
ensure the required admission reservation or defer new accepts until capacity
is available. Renaming `:unattributed`, changing >= to >, or treating the inner
`:PASS` as a complete verdict does not repair the demonstrated claim.

## Reproduction and scope

`pass2-liveness-driver.lsp` loads the existing test driver and
`pass2-liveness-hooks.lsp`. The latter uses the existing raw/executable-counterpart
wrapper helper, observes admission, reclamation, network close and client
state, and preserves all return values until it exits after the first live
drop. Its network-slot observer is intentionally scoped to C=1. No source
function is redefined and no frozen M1–M6 file is changed.

Run from the repository root, replacing `4` by `5` for the strict control:

```sh
nohup env FN_ACL2_SLOT_DIR=/tmp/fn2-a4-acl2-slots FN_ACL2_SLOTS=6 \
  FN2_PASS2_QA=4 \
  FN2_PASS2_OUTPUT=fn2/experiments/squares/mutants/pass2-liveness-qa4.sexp \
  timeout -k 5 120 tools/acl2 \
  < fn2/experiments/squares/mutants/pass2-liveness-driver.lsp \
  > fn2/experiments/squares/mutants/pass2-liveness-qa4.log 2>&1 &
echo $! > fn2/experiments/squares/mutants/pass2-liveness-qa4.pid
```

Both probes completed; no probe process remains running. All pass-2 additions
are new files under `fn2/experiments/squares/mutants/`.
