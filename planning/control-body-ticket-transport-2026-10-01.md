# Live control BODY receipt transport

Status: coordinator-ratified implementation contract, 2026-10-01. This is an
architectural handoff, not a native activation or certification claim.

## Decision and actual predecessor

Carry the existing ATS receipt explicitly through the live native callback and
core entry. Do not publish a receipt alias in STATE, substitute an APR grant,
mint a replacement ticket, or treat response resource policy as a receipt.

The actual predecessor is `92eb03f49707ff80489545a3e74f1d8c5be11faf`,
`host/native/owner-control-turn.lisp`. Its binding retains pool, slots, slot and
fixed enter/finish/fault callbacks. `fnn-owner-control-enter` calls
`fn-ats-enter-internal(slot, :owner-control, slots, pool)` and receives the
genuine nonce. This establishes GATE phase 2, not BODY phase 3. The old macro
hides that nonce from its body. Its receipt deliberately covers scheduler entry
and cleanup independently of operation BODY prepayment.

Neither a genuine phase-2 receipt nor passing it as an argument establishes
BODY authority. No genuine dedicated `:account-adoption` issuer exists in the
inspected account path. Preserve the actual immutable role `:owner-control`.
`:inspect` remains a scheduler class, not an ATS role.

## Native transport

Add this form in the owned control-turn implementation:

```lisp
(fnn-with-owner-control-issued-turn
    (binding slot nonce slots pool)
  ...)
```

The macro parameter list is `((binding slot nonce slots pool) &body body)`.
The four exposed values come only from the actual binding and returned entry
nonce. They are lexically borrowed until this invocation's outer cleanup.
The existing hiding macro may delegate to this implementation.

The native selected route is:

```text
fnn-owner-serialized-with-control-turn(service, cid, callback, optional class)
callback(slot, nonce, slots, pool)
  -> MV(word, answer, nextSlots, nextPool, nextState)
```

It selects the installed service binding and wraps the actual existing
scheduler/shared-action path exactly once. Do not wrap an already issued path
a second time. The wrapper preserves the existing owner/extent lock order;
the extent lock does not span a scheduler wait. Returned stobjs are retained
before result interpretation or failure handling. The actual binding and live
STATE retain these three returned stobjs; outer cleanup reads the retained
binding, not stale lexical inputs. The serialized variant returns `word` and
`answer` only after that cleanup. Account uses scheduler class `:control`,
inspection uses `:inspect`. An already owner-locked caller moves this entry to
its original outer dispatch site; it must not nest another serialized turn.

## Core signatures

The account family uses these signatures and output order:

```text
fn-owner-account-adoption-begin
  (config, bindings, entropy, slot, nonce, slots, pool, state)
  -> MV(word, result, slots, pool, state)
fn-owner-account-adoption-tick(slot, nonce, slots, pool, state)
  -> MV(word, result, slots, pool, state)
fn-owner-account-adoption-operation-select(slot, nonce, slots, pool, state)
  -> MV(word, result, slots, pool, state)
```

The native account adapters receive the same explicit arguments after their
existing config/bindings/entropy arguments. They do not reacquire a different
live pool or reconstruct a ticket. Account status remains a separate read-only
path and must not claim authority from the retained account job.

The inspect family uses the reader owner's exact ABI:

```text
fn-owner-inspect-response-source
  (slot, nonce, request, cached, slots, pool, state)
  -> MV(word, responseOctets, originalPRSvector)
fn-owner-inspect-operation-answer
  (request, cached, slot, nonce, slots, backing, pool, state)
  -> MV(word, diagnosticOctets, slots, pool, state)
```

`slots`, `pool`, `backing` and `state` denote their actual ACL2 stobjs, not
descriptor lists. The response helper's three values are response policy;
none is an ATS receipt or a compiled BODY allocation allowance.

## One source-specific prepayment and BODY dispatch

The composed core wrapper binds one named subphase to its actual retained
request and pre-state: `:inspect-response`, `:account-adoption-begin`, or
`:account-adoption-tick`. For account ticks the actual current job phase is
part of that selection; for inspection the original request/cache descriptor
is retained. No host phase flag independently authorizes a transition.

Within that same call:

1. Check the exact installed slots/pool association, slot, issued nonce,
   immutable `:owner-control` role and phase 2. Select the actual compiled
   source family for the retained subphase/request.
2. Obtain its genuine source-derived BODY allowance. This must cover the
   executed operation, called subphase transitions, rendering/cache updates
   and its charged epilogue. The bounded evaluator and its definite refusal
   path belong to already paid Qgate. No host numeric BODY argument is added.
3. Call `fn-ats-prepay-body-internal` on that same receipt. Only successful
   prepayment changes phase 2 to phase 3 and reaches operation constructors.
4. Check `fn-ats-role-bodyp(..., :owner-control, ...)` and invoke the selected
   actual BODY exactly once, preserving the selected request/subphase.
5. Return every stobj and the actual result to the enclosing native caller.

Prepayment source lookup cannot require phase 3 before obtaining its cost.
The phase-2 source lookup and phase-3 BODY authority checks are distinct. A
re-entered phase-3 prepay primitive does not license another operation under
the old charge. The selected composed entry and actual caller must prevent
that replay; no generic public callback/tariff interface is introduced.

The host-called proof subject is this composed source-selection, prepayment
and actual BODY wrapper. A theorem about the role predicate alone cannot show
that a particular renderer, account constructor or continuation was charged.
Existing finite family source producers remain real implementation obligations;
an unavailable getter or shaped family does not complete this path.

The composed operation entry accepts phase 2 only. Source lookup, prepayment
and BODY are one nonyielding call over the same lexically retained arguments;
phase-3 reentry is rejected. This supplies the request association without a
new descriptor field in ATS. A resumable job has its own retained descriptor
and obtains a fresh turn/cost for each later scheduler invocation.

## Cleanup, yielding and failure

The outer control wrapper is the sole owner of `fn-ats-finish-owned`. It calls
finish only after operation result handling and the actual scheduler cleanup
have definitely returned. The core BODY, account selector and inspect helper
must not finish the ticket early. Both BODY-paid and gate-only definite
refusals settle through their funded outer cleanup.

A normal yield may retain the actual account job, input aliases and their PRS
resource custody. It does not retain the completed turn's ATS authority. A
later scheduler tick obtains a new real turn after the prior turn is settled;
this is not a second issuance to repair missing authority in the same call.

A raw escape or ambiguous cleanup invokes the existing uncertainty transition,
retaining the slot nonce, cumulative allocation debt and ownership for
recovery. Do not unconditionally finish in an unwind path. Replayed or stale
nonces cannot decrement another live turn. Original PRS resource units,
charges, cancellation and physical lifetime obligations remain unchanged.

## Owned source changes and narrow checks

- Owner owns `host/native/owner-control-turn.lisp` and the actual serialized
  owner dispatch hunk.
- Reader owns the live-status hunk in `host/native/control.lisp` and inspect
  source/composed-answer wrappers.
- Captured/account owns `host/native/account-adoption.lisp` and the account
  Begin/Tick composed entries.
- Portfolio owns `host/account-adoption-operation-host.lisp` selection and
  its already assigned semantic account family.
- ATS keeps `books/allocation-turn-slots.lisp` and
  `books/allocation-turn-body-authority.lisp` unchanged unless an actual ABI
  conflict requires a coordinated repair. No new ticket schema is needed.

The narrow live check must observe the genuine enter nonce, source-specific
phase-2-to-3 transition, actual BODY, scheduler cleanup and final single leave
in that order. Mutations must reject gate-only BODY entry, wrong role, wrong
pool, stale nonce, changed request/subphase, repeated BODY, finish-before-
cleanup, and ambiguous cleanup followed by ordinary reuse. Preserve complete
multiple values in a positive actual caller witness. None of these checks by
itself qualifies the installed allocator source or the whole server image.
