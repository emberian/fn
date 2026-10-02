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
epilogue, and retained-intent raw fencing. `host/interfaces.lisp` declares the
surviving `fn-ats-finish-owned` callback; its carried-state and frame proofs are in
`books/allocation-turn-raw-bridge.lisp`. Source declaration admission is not native execution or image qualification.

Still open: genuine profile/constructor baseline installation; actual source allowance
composition; all concurrent executor/native outer-return joins; full-GC barrier and
qualified return suffix; immutable-image/native allocation measurements and deployment.

PRF-1164 supplies the proof-only executable source observers `fn-atsc-enter`
(word, nonce, slots, pool, cells, ordered operands, source sites) and
`fn-atsc-finish` (word, slots, pool, cells, ordered operands, source sites). Named
complete-result correspondence connects each to the actual internal callback.
Every entry branch, including failed issuer disposition, is bounded by 64 explicit
source CONS cells and 51 material arithmetic operations; successful current and
legacy reconstruction has 64 and 62 cells respectively and exactly 51 operations.
Finish has zero explicit source CONS and records the actual count subtraction
only when consumed. All five PRS coordinates and actual arithmetic operands are
retained. These counts are not installed tariffs: fixed reader/recognizer and
comparison lowering, concrete stores, native MV/frame/first-use/outer-return
closure and selected request/octet conversion must be assembled separately.
The final ordinary standalone test root proves its fixture view decodes the
complete state and checks actual complete results across reachable positive and
premise-removal branches, with raw/corrupted/mutation cases labeled separately.

PRF-1170 observes the actual connection evaluator's complete five-value result,
its bounded input consumption and its ordered material arithmetic operands.
`fn-copod-evaluate-material-operators-fit` establishes that every reached
ADD/SUBTRACT/MULTIPLY/FLOOR operand and result fits the actual descriptor domain,
including checked refusals before an oversized ADD or MULTIPLY could run. The
actual five-coordinate issuer predicate has that envelope when domain >= 5,
which includes its fixed traversal fuel. Malformed input comparisons remain
outside that arithmetic claim.

PRF-1171 connects proof-only `fn-copsc-prepare` and `fn-copsc-start` to all seven
actual results and concrete effects, and `fn-coptc-finish`/`fn-coptc-fault` to all
five actual ticket-wrapper results. PREPARE joins actual ATS entry, evaluator,
body prepayment and definite refusal settlement; START joins actual input checks,
retained ticket updates and the five-coordinate issuer preflight. Its actual
reserve/register/abort call remains named with exact arguments and output, with
its internal census still open. Successful ticket FINISH has four explicit
source CONS cells and three material subtractions; every finish path is bounded
by those counts. The observers' own records are proof scaffolding, never served
allocations. Full composed-state literal teeth, nested callee accounting and the
complete source/native installation contract remain in progress. No source
count supplies an installed tariff or prices native scheduler cleanup.

The PRF-1171 reserve successor reuses the existing actual PRS observer inside
`fn-icrc-reserve`. An actual successful reservation has52 explicit source CONS
cells and36/35 material operators for fresh/recycled candidates, including the
capacity multiplication and token FLOOR/MOD/+1 operations. Guarded complete
result refinements also cover actual registration and its ICS preflight join.
Nested registry event and abort/settle internal census remains named and open;
its absence is not a zero cost assumption.

The readonly internal `fn-ats-role-bodyp(slot, nonce, role, slots, pool)` requires
that exact installed role and phase3 together with the direct current SAMEpool
receipt, actual active/draining mode and positive active count. In particular,
uncertainty retains nonce/role/phase but closes this authority by recovery mode;
a successful finish also consumes it. It creates no receipt, performs no scan,
and supplies no installer or BODY price. An index-writer caller passes its literal
installed role, never a STATE mirror or a caller's family-shaped claim.

Normal203103 adds paired source PREPARE and ticket witnesses for prepared,
unavailable, refused, yield, finish, duplicate finish, fault and repeated fault.
A proved full one-slot/all-ten-field pool decoder, exact changed ticket and
universal MIO/STATE/other-global frames account for complete effects. Fault keeps
phase3 and A/count while fencing mode, not a fabricated phase6 transition.
START's provider effect witness and nested registry event/abort source census
remain open, as does whole source/native allowance installation.

The exact source registry successor observes all four actual recursive
`fn-ibp-node-connection-event` :reserve results and its provider wrapper, then
composes them into the actual register result. Successful segment reserve
constructs7 explicit row CONS cells and executes one ADD(1,active). Traversal
retains actual fuel/depth subtraction and slot FLOOR operands in execution order.
Each reached dynamic child resolution is explicitly unpriced; a BOUNDP check
alone does not establish a non-NIL installed child or exclude fallback construction.
Complete segment literals cover positive reserve, stale current row and refused
invalid token. These source correspondences do not price hash/shape/comparison
helpers, implicit stobj constructors, frames, collector or first use.

The complete abort observer preserves the actual four-value result and effects.
Its charged cancellation branch retains spent identities, constructs24 explicit
source CONS cells with a baseline ledger (23 with a legacy ledger), and records
four actual reusable-coordinate subtractions. Registered close and settlement
remain named unpriced calls. A source-issued token literal checks the whole
provider and pool outputs, charge release, retained NEXT and ordered operands.
Normal215522Z-3462588 certifies the two new roots against the historical
three-field holder coordinate, with114 cached inputs and73 citation gaps.
Fresh normal proof attempts exposed a missing local positive-LEN lemma used by
four-value reconstruction; the explicit local lemma repaired the proof without
changing its statement. Those failures remain archived. Current RX four-field
closure is still a coordinator convergence obligation; neither constructor nor
native qualification is transferred from the historical coordinate.

Kernel13 source successor retains distinct dynamic and physical ceilings. The
observer now records the original three SUBTRACT/FLOOR operations followed by
SUBTRACT(reservation,Gdynamic); MIN remains an unpriced comparison. Gate control
has13 material operations and successful entry51, with the same39/40 CONS cells.
Normal222650 certifies the exact observer and full entry/finish source tests;
normal221219 passing rows cover kernel and unchanged slot/body fixtures, while
that overall run remains incomplete. Connection composed expectations are adapted
to73/52/71 operations but await coordinator replay. Fixtures append zero reserve
only as synthetic logical tests; they are not qualified installations.

The guarded settlement successor observes all four actual `fn-icr-settle`
results. Source-issued registered-abort, charged refusal and completed-abort
refusal witnesses check the entire provider/pool outputs and retained identities.
Its successful suffix constructs23/24 explicit source CONS cells and records
nine material operations, excluding the named actual registry read/release and
generation/child units. No runtime price or allowance is inferred. The exact
component proof world is historical; modern RX/kernel include certification is
pending, and an interrupted broader cache-miss replay supplies no normal claim.


The DATA6 successor joins the actual counter transaction: retained pool intent
and recovery mode precede DATA publication; actual slot nonce and phase2 are
written while fenced; counter finish restores modes last. An unavailable begin
retains the proposed issued ledger/nonce in intent and marks phase6 without
exposing a receipt, decrementing active count or refunding debt. Entry, BODY,
readonly role authority and finish also require pool MODE :served, covering
an escape after the intent write before allocation mode changes. The matching
finish theorem explicitly requires :served; its omission witness retains the
matching receipt, active mode and positive count while asserting refusal.
The entry installed-root frame preserves installation/epoch/occupancy/incoming;
mutable MODE is the retained fence and is not asserted unchanged on failure.

For this exact split source, PRS reconstruction plus ledger4/5, continuation4,
receipt6, intent8 and DATA6 constructs62/64 explicit CONS cells on success.
The recorded material arithmetic sequence remains51 operations. An issued but
unpublished baseline branch retains45 cells and51 operations; these are source
observations, not native requests or installed Qgate tariffs. Prior39/40 and
monolithic50/52 source coordinates remain historical. Complete native fault
cuts, all-writer DATA6 integration and runtime qualification remain separate.
