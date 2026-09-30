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
raw bridge at exact source bytes. The ordinary test-root manifest
`certify-20260930T160950Z-9393` certifies the standalone concrete fixtures. Tests use
real local concrete stobjs and cover
concurrent slots, duplicates, reuse, refusals, drain between gate/body, prepaid drain
epilogue, and retained-intent raw fencing. `host/allocation-turn-host.lisp` declares
only enter/finish/uncertain compiled callbacks, with actual carried-state and frame
proofs. Source declaration admission is not native execution or image qualification.

Still open: genuine profile/constructor baseline installation; actual source allowance
composition; all concurrent executor/native outer-return joins; full-GC barrier and
qualified return suffix; immutable-image/native allocation measurements and deployment.

PRF-1164 supplies the proof-only executable source observers `fn-atsc-enter`
(word, nonce, slots, pool, cells, ordered operands, source sites) and
`fn-atsc-finish` (word, slots, pool, cells, ordered operands, source sites). Named
complete-result correspondence connects each to the actual internal callback.
Every entry branch, including failed issuer disposition, is bounded by 40 explicit
source CONS cells and 50 material arithmetic operations; successful current and
legacy reconstruction has 40 and 39 cells respectively and exactly 50 operations.
Finish has zero explicit source CONS and records the actual count subtraction
only when consumed. All five PRS coordinates and actual arithmetic operands are
retained. These counts are not installed tariffs: fixed reader/recognizer and
comparison lowering, concrete stores, native MV/frame/first-use/outer-return
closure and selected request/octet conversion must be assembled separately.
The final ordinary standalone test root proves its fixture view decodes the
complete state and checks actual complete results across reachable positive and
premise-removal branches, with raw/corrupted/mutation cases labeled separately.
