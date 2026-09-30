# Internal connection operation admission

This implements the connection-start portion of STO-10001. It does not activate
an endpoint or install runtime authority. The selected installer and native
outer closure remain required producers; a well-shaped descriptor is insufficient.

`fn-owner-index-connection-prepare(kind, family, address, peer, slot, slots,
mio, pool, STATE)` returns seven values: error, word, shared turn nonce, slots,
mio, pool, STATE. It enters the actual `:connection-start` worker slot, evaluates
the operation under prepaid Qgate, prepays its allocation-account BODY, and then
constructs a ticket. Success is `:prepared`. A definite post-entry evaluator
refusal or body yield consumes its gate receipt inside prepare and returns NIL
nonce only after actual ATS `:left`. Native never infers receipt liveness from
nonce presence. Ambiguous failures retain the receipt and return recovery.
Draining grants no new body allowance.

The sole immutable `fn-owner-connection-operation-installation` global contains
ten fields: tag `:connection-operation-installation`, installation serial,
SAMEpool association6, complete source-coordinate roster, immediate domain,
logical holder grant5, allocation-account body base, per-input-octet term,
per-registry-level term, and input-work quantum. The serial is a shared PRS OLD
NEXT issued during funded installation. No new counter is introduced. The
installer derives coefficients from the complete actual source/runtime closure
and supported profile; this leaf contains no installer or numeric tariff setter.
Source requests carry both object octets and allocation count before qualified
geometry lowering. Native constructor object rows and the issuer's 30 CONS /
31 ADD source count are contributions, not a complete envelope.

The body base covers ticket creation, bounded comparison, retained consumption
intent, issuer/preflight/registration, capture/open/definite abort, native custody,
and the entire return and cleanup closure, including up to two idempotent fault
callbacks. Input and registry terms come from actual producer bounds. Logical
holdergrant5 is separate from cumulative allocation debit A. Releasing a holder
never lowers A.

`fn-owner-index-connection-start(kind, family, address, peer, mio, pool, STATE)`
returns error, word, holder token, remaining fuel, mio, pool, STATE. The ticket
binds exact arguments, actual owner next ID, slot, shared nonce, current epoch,
installation serial, full descriptor reference, derived holder grant and fuel.
Native holds owner then extent exclusion continuously across publication and
consumption; neither yields. Address and peer matching visits at most the prepaid
input quantum and compares octets, never an arbitrary unbounded object equality.

The start retains `:start-intent` before issuer effects. It validates immediate
domain arithmetic before actual PRS construction. `fn-ics-reserve-register` calls
the existing debit, then registers in an existing physical child. No missing child
is created. Only confirmed registration with the matching retained receipt returns
`:reserved`. Traversal fuel covers registration and the existing open preflight.
Definite unavailable/refused/yield registration outcomes invoke actual abort;
only `:released` permits dropping the new token. Stale or uncertain outcomes retain
the token and fence. Positive holder identity is shared OLD NEXT + 1; scheduling
turn nonce remains shared OLD NEXT.

The sole mutable ticket global retains sixteen fields: tag, phase, kind, family,
address, peer, owner ID, slot, nonce, epoch, installation serial, descriptor
reference, grant, fuel, input quantum, and returned token. A raw escape retains
the current intent and roots. The ticket is not a per-CID lookup table.

`fn-owner-index-connection-finish(slot, nonce, slots, pool, STATE)` returns error,
word, slots, pool, STATE. Only the actual outer closure calls it, after all funded
native cleanup. It retains finish intent before consuming the actual ATS receipt;
`:left` settles the ticket to `:finished`. Completed roots remain until a later
successfully prepaid gate retires them, covering a raw escape between core mutation
and native result receipt. `fn-owner-index-connection-fault(slots, pool, STATE)`
has the same five results. It fences idempotently without clearing the ticket,
association, nonce, A, or count. No unconditional unwind finish is allowed.
Public operation finish requires a present, well-shaped matching operation
ticket. A live ATS receipt alone cannot bypass this requirement; no-ticket,
malformed or wrong-phase calls retain the receipt and return recovery. Definite
pre-ticket refusals use only the separate internal settlement helper.

PRF-1161 tracks the registered receipt boundary; PRF-1162 tracks exact bounded
input comparison and checked allowance arithmetic. Concrete issuer tests cover
existing-child success, absent-child definite abort preserving the spent identity,
insufficient traversal fuel before effects, and raw registration intent retaining
the exact pool charge, spent identity and pending root. Cost tests include literal positive
and hypothesis-removal witnesses, malformed/oversized input and immediate overflow.
These use explicit synthetic descriptors and physical-child fixtures.

The completion callbacks, getters and internal refusal settlement are factored
into `books/connection-operation-ticket.lisp`, with the thin
`host/connection-operation-ticket-host.lisp` declarations and no owner/MIO dependency.
Finish/fault guards and actual `:raw-with` preservation/frame declarations are
admitted. PRF-1163 proves that successful finish consumes one active turn without
refunding A and repeated fault has the exact same full result. Actual STATE/ATS
fixtures cover nonce zero, successful finish/replay, definite refusal cleanup,
retained start intent and double fault; declaration-removal cases fail as required.

Current coordinate: the two core leaves and narrow completion leaf and their
stated tests are source-admitted; prepare/start guards and the public registered-receipt theorem are admitted
in the actual provider/MIO source world. Raw PREPARE preservation declarations
and the actual installed/native operation join remain open. No complete selected-runtime operation
allowance, genuine installation, native activation or certification is claimed.

The public start definitions and registered-receipt theorem live in
`books/connection-operation-start.lisp`; the host companion includes that exact
source. Six actual STATE/ATS/MIO cases exercise prepare through registration,
definite abort and finish in the same pool, including refused evaluator/body
paths and a fault between prepare and start. Synthetic installation is explicit.
The positive case uses scheduling nonce zero, holder identity two and two spent
shared identities; logical abort and turn finish preserve cumulative A.
