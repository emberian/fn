# Once-only allocating scheduling turns (HST-042)

This is fn's internal allocation-accounting contract, not an RFC requirement.
The architecture implementation direction is the 2026-09-30 allocation epoch
and once-only scheduling-turn design. The public connection ABI stays unchanged.
An immutable qualified installation and actual operation source join are required
before activation. A representation constructor does not establish that authority.

`fn-allocation-turn-slots` is a separate concrete five-field stobj: exact SAMEpool
runtime association, installed slot count, immutable endpoint-kind array, mutable
current-nonce array, and mutable phase array. Installation sizes the arrays to the
operator's admitted executor count and pays the actual constructor/backing/native
baseline. There is no served resize, free-list search or slot scan. A connection
holder is lifetime custody and gives no turn authority. Stored data has no new cap.

The dispatcher has an installed slot and nonnil symbol role. Internal
`fn-ats-enter-internal(slot, role, slots, pool)` returns word, nonce, slots, pool.
Receipt is SLOT and NONCE as two scalars, never a newly allocated list. The scalar
nonce is actual old shared PRS NEXT, through `fn-aec-collection-issue`; the fixed
identity charge never refunds or wraps, and no PRL binding row is constructed.
Under the same extent/pool lock, entry retains phase 1 before installed Qgate
prepayment/active increment. Definite gate refusal restores idle with no issued
receipt; definite issuer refusal consumes the temporary turn once while retaining
Qgate. Successful issuance records nonce and phase 2 before return. Raw escapes
fence and retain the exact partial transition, roots, identity and allocation debt.

`fn-ats-prepay-body-internal(slot, nonce, body, slots, pool)` is an INTERNAL
representation seam. BODY must come from the actual operation's source evaluator,
including constructors/effects and every allocating epilogue through outer return.
No public supplied BODY or cleanup Boolean exists here. It checks matching receipt
and pays the body once before phase 3. Already prepaid body continuation keeps the
same receipt and A in draining. A gate-owned unpaid body yields in draining and
returns within Qgate, rather than waiting for GC with an active turn. Fresh cleanup
is new entry and cannot bypass draining. Unbounded I/O must not hold an active turn.

`fn-ats-finish-owned(slot, nonce, slots, pool)` returns word, slots, pool. With
matching association/slot/nonce and phase 2, 3 or 4, active/draining mode and positive
active count, it retains phase 5 before one scalar decrement and returns idle,
keeping last nonce and A. A stale, duplicate or reused-slot old nonce leaves the
complete state unchanged. Intent/faulted phases cannot finish. Recovery never
silently consumes a receipt. It must be called at actual outer return, after every
allocating epilogue; an unconditional exception-unwind decrement is forbidden.

Phase tags are immediate: 0 idle, 1 entry-intent, 2 gate-owned, 3 body-owned,
4 finishing, 5 leave-intent, 6 faulted. Normal returned-state correspondence says
active turns equal proof-only issued/retained slot cardinality. Construction and
entry/body/finish preserve it; no served call evaluates that count. A raw escape
between physical updates fences instead of claiming the relation was restored.

PRF-1156 names the actual matching finish subject and each necessary hypothesis.
PRF-1157 names actual shared nonce ownership and local entry/body/finish preservation.
The ordinary manifest `certify-20260930T154935Z-91174` certifies the concrete book and
raw bridge at exact source bytes. Tests use real local concrete stobjs and cover
concurrent slots, duplicates, reuse, refusals, drain between gate/body, prepaid drain
epilogue, and retained-intent raw fencing. `host/allocation-turn-host.lisp` declares
only enter/finish/uncertain compiled callbacks, with actual carried-state and frame
proofs. Source declaration admission is not native execution or image qualification.

Still open: genuine profile/constructor baseline installation; actual source allowance
composition; all concurrent executor/native outer-return joins; full-GC barrier and
qualified return suffix; immutable-image/native allocation measurements and deployment.

## Native scheduler control receipt

The internal `fnn-with-owner-control-turn` wrapper retains a distinct installed
`:owner-control` slot before the actual `fnn-owner-gated` scheduler pre-observation
and entry, and finishes only after that macro's cleanup returns. A nested
connection operation has its own slot and receipt. Definite connection refusal
or drain-time yield can settle that operation without releasing the surrounding
control receipt before scheduler cleanup. A raw escape fences the pool and
retains unresolved receipts; it never executes an unconditional finish.

Entry, finish and fault use extent exclusion, but the wrapper does not retain
that mutex across scheduler waiting or the body. The active receipt prevents
collection from passing quiescence while other admitted workers can finish.
Finishing an already admitted receipt remains permitted during draining.

This wrapper is not selected by a served caller yet. Installation must cover the
complete scheduler control allocation and execution envelope, including wait
machinery, wakeups, queue operations, cleanup and wrapper/runtime costs. It must
establish finite drain progress without requiring fresh admission to finish
already admitted work. The component test's synthetic Qgate is not evidence for
that envelope; retaining a receipt alone does not justify unbounded waiting or
I/O. See `planning/evidence/owner-control-turn-2026-09-30/README.md` for actual-core
composition evidence and its recording scheduler boundary.
