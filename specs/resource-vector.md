# The resource vector and the bank (HST-045)

This is fn's internal accounting contract, not an RFC requirement. The
founding goal it serves is ember's warranty: a full up-front accounting of
every resource spent on a user's behalf
(`planning/design-store-representation-2026-10-01.md` section 2, stage 6 of
its order). The precedent is seL4 untyped memory and KeyKOS space banks
(`build/coordinator/scholar-literature-2026-10-01.md` section E.3): the
system never allocates on its own; every request draws on its user's bank;
the owner's own needs are reserved before any user's; teardown destroys the
sub-bank with everything it held. GPT-6's ratified invariant
(`planning/review-2026-09-30-gpt6-log2.md` section 2) is the one this
contract carries: `U + C + R <= B(P)` over a resource vector, `R >= W(P,
Omega(s))`, `dW+` charged before acceptance, and "refusal preserves funded
rescue capability". What the books prove of that last clause, exactly: a
refused step returns the bank itself (`fn-rv-step-refused-keeps-the-bank`,
`fn-rt-step-refused-keeps-the-tree`), so the slack is unchanged at the
operation boundary. The refusal's own transient execution (the allocation of
the refusal path before its verdict) is NOT accounted by these books: it is
the operation layer's obligation (item 4 below), and until that layer
exists the clause is a model-level statement about the ledger, not about an
entry (Codex review r06 F1).

## The vector (`books/resource-vector.lisp`)

A vector is a list of `*fn-rv-k*` naturals, one a resource class, in the
order of `*fn-rv-coordinates*`: `:resident` octets (the collector's copy
included), `:disk` octets, `:descriptors`, `:workers`, then the finite
identity spaces `:read-ids`, `:txids`, `:config-gens`, `:conn-ids`, and
`:work`. The first five are Codex's `fn-prs` vector, so that vector is this
one's prefix (`fn-rv-prs-vector-is-the-prefix`). A class is `:reusable` (a
settle returns it) or `:spent` (an identity or work: drawn once, never
returned); `*fn-rv-reusable-mask*` is derived from the table, and
`fn-rv-reusable` / `fn-rv-spent` split a vector by it. `fn-rv-plus`,
`fn-rv-below` (`<=` coordinate-wise) and `fn-rv-monus` (truncated
difference) are the whole algebra; nothing in the book names a class. A
class is added by a row of the table, never by the host.

## The bank

`(BUDGET DRAWN SLOTS)`: the budget vector; the drawn vector, carried in
state and never recomputed on a served path; and the slots, rows `(PHASE
GEN . DEMAND)` indexed by position, so the executable twin is a direct-index
typed array. Phase 0 idle, 1 drawn, 2 a sub-bank whose demand is its whole
budget: sub-banks partition their parent, and a sub-bank's unused slack is
not its siblings'. GEN is the slot's generation: every charge of the slot
raises it by one and answers it as the draw's **completion token**; an idle
slot keeps it. Every later step on a charged slot names the token, and a
token that is not the slot's current one is `:stale` (Codex review r06 F2:
by slot alone, a completion replayed after the slot was settled and drawn
again would have settled the new draw). The transitions return `(WORD BANK'
[GEN])`, a refused one returning the bank itself:

| transition | effect | refused by name |
| --- | --- | --- |
| `fn-rv-draw slot demand` | charge an idle slot: drawn + demand, phase 1, the new GEN answered | `:invalid-draw`, `:slot-busy`, `:resources-unavailable` (exactly when drawn + demand is not within the budget) |
| `fn-rv-open slot budget` | the same charge; the slot becomes a sub-bank (phase 2) | the same |
| `fn-rv-settle slot gen` | the draw's reusable coordinates return; its spent ones stay drawn; the slot idles | `:invalid-slot`, `:stale` (not phase 1, or not this token) |
| `fn-rv-refund slot gen x` | x of the draw's reusable part returns now; never refused within what it holds | `:invalid-refund`, `:stale`, `:past-what-it-holds` |
| `fn-rv-grow slot gen x` | a sub-bank's budget grows by x (the owner's dW+) | `:invalid-grow`, `:stale`, `:resources-unavailable` |
| `fn-rv-destroy slot gen spent` | the sub-bank's budget returns less SPENT, what it had drawn in the spent coordinates | `:invalid-destroy`, `:stale`, `:sub-bank-overspent` |

`fn-rv-install budget baseline reserve nslots` builds the root: slot 0 the
owner's permanent baseline U (drawn), slot 1 the maintenance reserve R
(a sub-bank), before any user's slot exists; a start that cannot fund both
is refused by the draw's own word. `fn-rv-step` is every transition as one
function over an op `(:draw SLOT DEMAND)`, `(:open SLOT BUDGET)`, `(:settle
SLOT GEN)`, `(:refund SLOT GEN X)`, `(:grow SLOT GEN X)`, `(:destroy SLOT GEN
SPENT)`; `fn-rv-run` a sequence.

`fn-rv-okp` is the carried invariant: budget, drawn and every row are
vectors; drawn `<=` budget (funded); the reusable part of drawn is exactly
the reusable part of the outstanding rows' demands (nothing leaks, nothing
is counted twice); the spent part of the outstanding rows is within the
spent part of drawn (what was spent and settled stays drawn). `fn-rv-slack`
is budget minus drawn.

### The keystones (PRF-1209), proved once over `fn-rv-step`

- `fn-rv-step-keeps-okp`, `fn-rv-run-keeps-okp`: from an okp bank every
  step's result is okp, admitted or refused.
- `fn-rv-step-refused-keeps-the-bank`, `fn-rv-refusal-keeps-slack`,
  `fn-rv-refused-run-keeps-the-bank`: a refused step returns the bank
  itself, so the slack is unchanged, over any run of refusals.
- `fn-rv-draw-admits-exactly-within-the-budget`,
  `fn-rv-draw-charges-exactly-the-demand`: the admission condition, and the
  effect is exactly the charge with the token answered (the check precedes
  every effect).
- `fn-rv-settle-once`: a second settle of a token is never admitted and
  leaves the bank.
- `fn-rv-replayed-completion-is-stale`: the first draw's token, any run, a
  second admitted draw of the slot: the replayed token is `:stale` and
  leaves the bank (the slot's generation never falls,
  `fn-rv-run-never-lowers-a-gen`, and a charge raises it,
  `fn-rv-charge-raises-the-gen`).
- `fn-rv-step-keeps-the-other-slots`, `fn-rv-user-steps-keep-the-reserve`:
  a step on one slot leaves every other row; the reserve at slot 1 is never
  drawn by a user's step.
- `fn-rv-install-reserves-the-owner-first`: the installed root is okp with
  baseline and reserve drawn and nothing else.
- `fn-rv-destroy-returns-exactly-the-unsettled-draws`: destroying a
  sub-bank returns exactly its budget less what it spent, and that covers
  the reusable part of every draw the sub-bank still held.

Teeth: `tests/acl2/resource-vector-tests.lisp` (`defkeystone` per keystone
above, one removal witness a hypothesis, corrupted-state witnesses
labelled, mutations for the hypothesis-free keystones), over a small node's
root, a connection's sub-bank, ten reads that exhaust the read-identity
coordinate while every octet has returned, the replayed completion, the
destroy and the reserve's growth.

## The tree: a node's accounting as one state (`books/resource-vector-tree.lisp`)

A sub-bank that is a value of its own cannot be revoked by its parent's
destroy (r06 F2): so the node's accounting is one state, `(ROOT SUBS)`,
the root bank and, at every slot whose root row is phase 2, the sub-bank
itself (NIL elsewhere). An op is `(OWNER . STEP)`: OWNER `:root`, or the
sub-bank's token `(SLOT . GEN)` as `fn-rv-open` answered it, and STEP a
bank op. A root `:open` names the sub-bank's slot count; a root `:destroy`
is `(:destroy SLOT GEN)` and reads what the sub-bank spent from the sub-bank
itself, never from the caller. One level: a sub-bank holds draws, never
sub-banks (`:no-nested-sub-banks`). `fn-rt-okp`: the root okp, SUBS as long
as the root has slots, at every slot a sub-bank exactly when the row is
phase 2, okp, with the row's demand as its budget. Keystones (PRF-1209):

- `fn-rt-step-keeps-okp`, `fn-rt-run-keeps-okp`,
  `fn-rt-step-refused-keeps-the-tree`.
- `fn-rt-sub-bank-steps-keep-the-root`: a step inside a sub-bank leaves
  the root bank (the partition).
- `fn-rt-destroy-revokes-the-sub-bank`: after an admitted destroy, any run,
  and whatever the slot holds then (re-opened under a new token or not),
  every step addressed to the destroyed sub-bank's token is `:stale` and
  leaves the tree.

Teeth: `tests/acl2/resource-vector-tree-tests.lisp`. This tree is the shape
of the typed ledger the host needs: one table, a row's owner a slot.

## One accounting (`books/resource-vector-relations.lisp`, PRF-1210)

Each existing mechanism is a projection of the vector:

- Codex's cold-read gate (`fn-prs-fundedp B U R C`) is exactly `fn-rv-okp`
  of the root whose rows are U (drawn), R (a sub-bank) and C (drawn)
  (`fn-rv-prs-gate-is-a-funded-root`); `fn-prs-plus` and `fn-prs-below`
  agree with `fn-rv-plus` and `fn-rv-below` under the prefix embedding
  (`fn-rv-prs-plus-is-plus`, `fn-rv-prs-below-is-below`).
- PRF-380's credit ledger is the `:resident` coordinate: `fn-rv-bank-of-
  credits` is the bank whose rows are BASE (drawn), COMPLETION and RUNTIME
  (sub-banks), CACHE and one row an operation, every other coordinate 0.
  `fn-rv-credit-ledger-funded-by-definition` is a projection identity (the
  constructed bank's budget and drawn ARE the ledger's budget and total),
  not a consistency keystone. NOT PROVED, honestly (r06 F5): that a funded
  ledger is an okp bank (the row sum equals the total), and that Codex's
  "release the reusable coordinates only" is `fn-rv-settle`'s split; both
  are NEXT in the lane dump, cited nowhere.
- PRF-198's heap reservation and PRF-223's connection budget as funded
  roots (`books/resource-vector-relations-heap.lisp`,
  `fn-rv-heap-reservation-funds-the-root`,
  `fn-rv-connection-budget-funds-the-root`): DRAFTED, not admitted, not a
  Makefile root, cited nowhere (its include closure is the owner's).

The budgets are not one number: they are projections of different roots
(the launcher's, the owner's, the cold pool's). Unifying them is the
operation layer's work, below. Teeth: `tests/acl2/resource-vector-relations-
tests.lisp` evaluates the projections on concrete values and carries
`defkeystone` teeth (r18 F3) for the prefix, plus and funded-root relations
(the funded-root removals are labelled corrupted dotted-tail inputs);
`fn-rv-prs-below-is-below` has a positive witness only: removing either
shape hypothesis leaves the equality true on every example tried, evidence
that both may be redundant (not removed: that needs the weakened theorem).

## The executable representation (`books/resource-vector-exec.lisp`, PRF-1211 planned)

`fn-resource-ledger` is a stobj with no list: the budget and drawn vectors
as `(unsigned-byte 64)` arrays of `*fn-rv-k*` words; the slots as
direct-index typed columns (a phase column, a generation column, one u64
column a coordinate for the demands); Codex's per-read ownership row as six
more u64 columns by slot; Codex's five-element pool list as typed scalars.
`fn-rl-bank` abstracts it to the logical bank; `fn-rl-wfp` is the
representation invariant (every column holds COUNT slots). The
representation domain is explicit (r06 F4, D27): a profile whose budget
word does not fit a u64, or whose slot count does not fit a u32, is
refused by `fn-rl-install` (`:unrepresentable-profile`,
`fn-rl-profile-representable-p`) before any store, never saturated; a slot
whose generation reached the last u64 refuses its next charge
(`:slot-exhausted`), never wraps. The fresh install boundary is
`fn-rl-install-correspondence` (r18 follow-up): on a fresh ledger
(`fn-rl-freshp`, which `create-fn-resource-ledger` satisfies) the exec
install answers exactly the logical `fn-rv-install`'s word, except
`:unrepresentable-profile`; on `:installed` its `fn-rl-bank` is the logical
bank; on every refusal the ledger is unchanged. `:already-installed` is the
other exec-only refusal (a non-fresh ledger). Source theorems
`fn-rl-draw-correspondence` and `fn-rl-settle-correspondence`, under the typed
recognizer and `fn-rl-wfp`, connect exact result words, draw tokens and bank
effects to the logical transitions, including the generation limit refusal.
Draw/settle guards, representation preservation and syncer receipt scalar
frames are source-admitted, with complete positive and typed/shape removal
witnesses. Bootstrap install/store guards and typed/shape preservation are source-admitted;
matching certification and the remaining export boundaries are owed. PRF-1211 remains
planned. The next
version is the tree layout (one table, an owner column, per-row drawn
columns for sub-bank rows), to be generated by `def-representation`
(marked `; GEN: def-representation`).

## For `definterface :operation` (the next lane)

Every host-called entry that allocates, opens, spawns, spends an identity or
consumes a quantum becomes an OPERATION. The declaration adds one clause to
`definterface` (`books/definterface.lisp`), and the macro emits, per entry,
from the loaded world:

1. **The tariff**: a vector-valued function of the entry's inputs, supplied
   or derived by a census of the body's allocating primitives times the
   body's iteration bound (route A section 3.2 item 1, route B section 3.2b
   item 2); its coordinates are the table's, its spent coordinates the
   identities the entry issues (one txid, one read id, one connection id)
   and the work of its quantum.
2. **Charge before effect**: the wrapper draws the tariff on the entry's
   slot (`fn-rl-draw`) and runs the body only on `:drawn`; a refusal returns
   the named word with the ledger and every stobj unchanged. The slot is the
   role's (owner, extent, mux, checkpoint, bp; Codex's
   `allocation-turn-slots` phases 0..6 collapse to the bank's 0/1/2, the
   nonce to the token row).
3. **Settle once, by token**: the matching completion carries the draw's
   token and settles the slot (`fn-rl-settle slot gen`) exactly once; a
   stale, duplicate or replayed completion is `:stale` and changes nothing
   (`fn-rv-settle-once`, `fn-rv-replayed-completion-is-stale`). A result
   the caller retains (a buffer, a cache entry, a record in the suffix) is
   a refund of the rest and a draw on the owner's slot, never a settle; a
   timeout settles nothing. A connection's close is the root's destroy of
   its sub-bank, and every completion of the connection's draws after it is
   `:stale` (`fn-rt-destroy-revokes-the-sub-bank`).
4. **The bound obligation**: `NAME$tariff-bound`, the body's cost twin is
   within the tariff and its work within the quantum, discharged by the
   census for derived tariffs and proved by the lane for supplied ones.
   The transient allocation of the refusal path itself is within the slot's
   prepaid gate term (GPT-6's "no borrow-then-return"): THIS is where
   "refusal preserves funded rescue capability" becomes a statement about
   an entry; the ledger books prove it of the ledger only.
5. **The dispatch row**: `interface_emit` adds kind, tariff, slot and
   settlement to the entry's `planning/interfaces.json` row; D40's
   dispatcher passes the ledger stobj; the host observes (machine, rlimits,
   free octets, RLIMIT_NOFILE) and never computes a tariff.
6. **Teeth**: the positive witness evaluates the twin on `:witness` and
   asserts value equality and cost within tariff; a hypothesis-removal
   witness per guard conjunct; the refusal witness asserts the ledger
   unchanged; corrupted-state witnesses labelled as such
   (`tests/acl2/generated/<kind>-tests.lisp`).
7. **The build check**: an allocating host-called entry without an
   `:operation` clause refuses the image build (the end of start-time
   gates).

The owner's reserve is `fn-rv-install`'s slot 1: `W(P, Omega(s))` as a
static worst case first (GPT-6: a valid first implementation), then
`fn-rv-grow` by `dW+` before every acceptance that raises it; a user's
operation draws on its connection's sub-bank, opened at accept and
destroyed at close (the destroy returns exactly what the connection had
not spent and revokes its tokens). Nothing of this is wired into a served
path by this lane (MODE 2026-10-01 section 3: no gate before its producer).

## Physical operation custody (HST-046)

A draw's debit remains held until its physical actor has terminated and its
matching operation outcome has been consumed. The resource generation and
operation generation are distinct: replay of either must refuse unchanged.
An observed timeout or failed join leaves custody pending. A spawn refusal
may use an affirmative `:no-actor-created` receipt; an unwind after actor
creation requires the actual terminal join. A connection drains its issued
custody before `fn-rt-destroy`; revocation alone cannot release resources an
issued I/O still physically holds. Retained output additionally requires its
own release or durable funded transfer.

The first concrete slice is `books/resource-syncer.lisp`. Runtime installs
`fn-ros-install-syncer(qualified-threads, observed-stack, ledger)` in the
existing startup `:hold` producer, then calls `fn-ros-issue(operation-gen,
ledger)` before spawning the syncer. Its token is
`(:resource :owner 2 DRAW-GENERATION)`. `fn-ros-physical(token, receipt,
ledger)` and `fn-ros-outcome(token, operation-gen, ledger)` independently
record their receipts; only both authorize `fn-rl-settle`. Tests assert
operation-first and physical-first completion, busy issue, timeout, stale
draw and wrong operation generation.

This is an owner projection of one already-funded syncer worker and its
observed stack plus profile runtime bytes. The parent retains its baseline
and maintenance reserve; historical spare-thread guesses do not fund rescue.
Captured batch buffers retain their existing memory credits. Setup/refusal
work belongs to the parent startup/runtime baseline. Full tariff allocation,
work, descriptors, user principal, supported actor census and environmental boundary
proofs remain obligations; this slice does not claim them. PRF-1252 is planned.

The initial `definterface :operation` contract has stage `:projection`,
funding/tariff/draw/physical/outcome function names, owner principal, fixed
slot, declared covered coordinates and the complete unresolved cost set.
`def-operation-check` first rederives the entry's own `def-cost` row, then
checks those unresolved names exactly, coordinates against `fn-rv`'s table,
and the actual translated draw's slot and tariff call. It refuses missing
logical producers, duplicate keys and attempts to claim `:accounted`.
This is a source linkage check for an enforced projection; it does not prove
funding transfer, total allocation, refusal work or native receipt honesty.
The full operation gate remains owed and cannot be activated by annotation.

`books/resource-operation.lisp` is the logical tree reference for the next
connection/output slice. It uses the existing `fn-rt`/`fn-rv` transitions:
owner baseline/reserve installation precedes sub-bank open; an explicitly
funded gate draw precedes the operation draw; retained reusable output stays
on its draw after transient refund; timeout keeps the tree; close refuses
while any child draw remains. Its three preservation facts unfold the
reference decisions and are not physical-I/O or served-representation
keystones. Input demand construction and gate setup require prior caller
funding; this reference does not derive their tariff. The typed syncer
producer is currently the connected consumer; typed subtree/refund and full
connection/output custody remain owed.

Private ledger allocation requires the registered creator's validated
`:raw-guarded (0 nil (fn-resource-ledger))` route. ACL2's live-stobj
counterpart refuses this private construction; the actual native fixture
caught that refusal before install. `fn-di-raw-creatorp` checks the exact
registered zero-input creator and verified ABI, so ordinary methods cannot
claim this exception. Startup preserves this narrow allocation route even
in developer counterpart mode; install, issue and receipt methods remain
on their normal selected routes. This is a concrete allocation bridge, not
an accounting theorem or an exemption from funding the created object.

The actual syncer issue, physical/outcome receipt and drain observers now
have source-admitted guards. The internal settle helper requires the carried
constant-size shape invariant and slot 2 to exist. Source-admitted
`fn-ros-issue-keeps-representation`, `fn-ros-physical-keeps-representation`
and `fn-ros-outcome-keeps-representation` preserve both typed recognition and
`fn-rl-wfp`; literal positive and each hypothesis-removal witness accompany
them. Bootstrap install guards and the general bank/native boundary remain
owed. These source admissions are not matching certificates.

HST-046 also covers the lifetime of the operation consumer. After successful
launch, every committer unwind before consumption retains a continuation over
that operation's ledger and actual result cell. A later physical return consumes
that result; an already-observed return consumes it during unwind. This includes
raw nonlocal ACL2 escapes as well as conditions. A consumption that has started
may have torn, so cleanup never retries it or manufactures settlement. The outer
committer actor also invokes the service failure boundary when a raw escape
bypasses its inner condition handler. SCN-1087 exercises the native consumers;
these schedules do not establish a new image or host-refinement theorem.

SCN-1089 supplies the matching-image consumer: actual mux startup `:hold`,
POST acceptance, independent literal custody receipts, clean stop and
restart retrieval. The selector is prepared; image execution is pending.
Optional diagnostics cannot change custody if formatting or output fails.

## Shared output pool (HST-047)

The output pool is an explicit heap allowance beyond the composed store,
thread and cold-resource launch reservation. `resources.output_heap_octets`
and `resources.output_quantum_heap_octets` form an optional normalized pair;
the quantum is allocation heap octets, not wire octets or a maximum reply.
Absent policy remains a partial resource frontier. Explicit policy stays
unsupported by operator run until the actual consumer and its allocation
coverage are installed; recognizing grammar does not activate a gate.

`fn-orv-extend-reservation` extends the existing composed launch decision
exactly once and checks the whole observed machine reservation. Startup
`fn-orv-startup-grant(dynamic, store-need, cold, policy, slots)` receives actual
captured dynamic space, the existing pre-extension store need and the exact
normalized cold descriptor. It requires all three allowances to fit, protects
bookkeeping and one owner maintenance lease, and leaves at least one user
lease affordable. Bookkeeping is currently an explicit layout projection;
its runtime allocator/collector refinement and owner rescue tariff remain
owed. Rounding surplus and an old connection machine-memory reply allowance
do not fund this pool.

A separate private `fn-resource-ledger` instance backs the shared pool.
`fn-rlo-install` installs it; `fn-rlo-issue(cid, connection-gen, operation-gen,
dependency, ledger)` draws a fixed lease before semantic materialization and
returns `(:resource (:connection CID CONNECTION-GEN) SLOT DRAW-GEN)`. Row
metadata stores operation generation independently. CID, both generations
and slot must match every receipt. Free rows are reused after settlement;
pressure refuses a new window without truncating stored data.

`fn-rlo-output(token, operation-gen, :drained|:discarded, ledger)` observes
release of the actual output references and no future publisher for that
window. `fn-rlo-physical(token, operation-gen, :terminal|:no-actor-created,
ledger)` observes its actual dependency completion. Issued dependencies
require both receipts in either order. Timeout, failed/torn cleanup, socket
close and stale receipts never release the debit. `:none` is restricted to a
scoped synchronous quantum that issues no physical I/O. Native shutdown also
requires the retained custody roster empty; the fixed typed drain projection
alone is insufficient to establish that fact.

The first native fixture draws before actual `fn-sl-step` rendering through
normal semantic counterparts and retains a second window through a real
worker join. It is a discrimination test of funding and custody, not complete
NEWNEWS allocation coverage. Initial matcher/metadata work, integer widths,
outer plan/mux copies, concrete allocator margins and free-row protocol
validity remain PRF-1259 work. The actual install/draw/receipt methods now
refine the existing typed bank operations; metadata does not alter accounting. The actual install/issue/output/physical
methods preserve typed representation and fixed column shape; their mutation
guards are verified in the source proof world. No accounted operation
gate may be inferred from the serializer's logical cons bound or this pool.

SCN-1097 connects the same accepted cold/output projections through operator,
control and normalized owner entry to service fields. Actual mux startup
`:hold` invokes output installation; `fn-orv-startup-grant` must accept
captured dynamic space, exact pre-extension store figure, cold descriptor,
output policy and ACL2 row count before private allocation.
`fn-orv-startup-slots` adds the bank's two protected rows to the admitted
connection count; it never clamps an unrepresentable profile. Row count is
metadata capacity, not a heap grant for whole replies. Explicit policy stays
staged until actual issue and full allocation/custody coverage are connected.
A response lease must retain its PLAN/selector/renderer continuation and all
output/socket suffixes until operation completion and no future publisher,
plus actual issued dependency termination; clearing OUT alone settles none.

The response identity producer is `fn-rid-connection`/`fn-rid-response` in
`books/response-identity.lisp`. The service retains two ACL2 serials under O;
actual mux admission first retains admitted CID for cleanup, then captures
`(:connection CID CIDGEN)`. Before the first response render factory, mux
reserves `(:response CID CIDGEN OPGEN)`; cursor/cold resumption keeps that exact
object. Both counters refuse at the u64 maximum, without wrap. Response
identity retirement follows the existing all-windows/suffix terminal path.
This capture seam is not a grant or a settlement: the future response lease
consumer must consume the identity before retirement and retain custody until
all continuation/output/dependency/no-future-publication obligations hold.
SCN-1102 covers actual pure producer/native helper/pre-render control flow;
full output activation and cost/refinement remain PRF-1259.

The actual owner cold-result transfer and readiness observation now use the
shared observed E mutex seam. The transfer has no hidden condition-wait: its
actual acquire surrounds retained-condition classification and exact settle,
and release is reserved before physical unlock/completed afterward. The
finite fixture observes acquire, literal `:job-result`, release while preserving
the original condition. Remaining O/P/hidden-wait sites keep complete PageIO
comparison unavailable.

The staged native renderer consumer retains one `fnn-output-grant` across the
whole response. `fnn-mux-render-next` draws before its first factory and binds
that grant across the existing owner renderer; the returned fifth cold-read
value is unchanged. Actual cold issuance attaches its exact read under O.
Actual worker return is observed under E before slot recycling, then the read
transfer activation must end before its pending dependency reference drops.
The grant retains only pending children and an ever-issued physical observation,
not the response's completed dependency history. A completed child cannot
authorize physical completion while later factories may still issue children.

Whole response drain/discard closes future factory authority and clears the
owned reusable render buffer. Physical custody completes only after all
attached children have returned and their transfer ended; no-child applies
only to an operation that issued no child, including literal warm-hit captures.
Issue and each receipt publish their native calling stage before mutation.
Raw/condition escape retains unresolved custody and prevents another semantic
step on that receipt. The root close requires both typed pool drain and an
empty native grant roster. SCN-1107 checks actual native control flow with
recording typed boundaries and actual held children; configured activation,
complete retained graph/allocator tariff and interpreter correspondence remain
open. Declaration of a live caller is not those claims.

## Logical constructor cost dimension (PRF-1274)

`def-cost :conses BOUND :cons-unaccounted (CALLEES ...)` derives a logical
cons constructor twin from the same executed translated body as visit cost.
It preserves independent unknown leaves and reconstructs multiple-value
bindings. Quoted objects are borrowed; fresh conses and copied list spines
are charged. Concrete stobj operations remain unknown without a representation
contract. The actual string renderer's derived count is bounded by its source
recurrence and by `8*nfix(bytes)+2`. This supplies a per-turn constructor bound;
it does not price retained state, native integer/vector allocation, physical
bytes, collector copying or custody of borrowed archive references.

### Direct immutable line windows (PRF-1281, SCN-1109)

NEWNEWS line emission can fill the response's private octet buffer directly.
The actual fn-splan-line-window checks the retained phase, excludes outstanding
dependencies and pending octets, and preserves the captured context/following
cursor. fnn-owner-render-next calls it outside the owner mutex because this
phase reads only the immutable captured string. Scalar loop registers replace
per-byte cursor and output-list construction; a new continuation is constructed
at the window boundary. Other cursor phases retain their serialized consumer.

Buffer reuse requires the previous borrowed output to be consumed before another
render. The mux opts into a borrowed capacity vector plus explicit valid END;
partial socket/TLS writes retain that range and never transmit spare capacity.
The sixth render-quantum value carries END while the fifth remains COLD-READ.
Default non-mux callers retain exact-length vectors. Compression still receives
an exact prefix (copying a short window). Full response termination still controls
settlement. Compression copies, continuation/matcher allocation, pinned roots, register widths
and GC are separate resource obligations; this optimization does not activate an
unsupported output profile or establish complete physical heap coverage.

## Pre-factory output command admission (PRF-1278)

The owner previews its current wire and exact input range with the existing
`fn-wire-scan`, without executing any command factory or changing STATE.
`fn-ocap-preview` returns `(:preview NEXT FAMILY TOKENS)` for the first event;
standard NNTP families, extensions, malformed commands, partial input and
article mode remain distinct. `fn-ocap-admit-preview` requires an actual
ACL2 footprint descriptor `(:tariff FAMILY OCTETS)` matching that family and
fitting captured capacity. The descriptor comes from the selected implemented
footprint producer; operator annotations cannot manufacture one.

The response generation and actual lease must be retained before preview,
since scanning/tokenization also allocate. The native owner then evaluates
only the accepted `NEXT` prefix and retains every suffix byte for a later
operation, so a second unpriced command cannot enter its factory under the
first command's tariff. Unknown families refuse in accounted mode. Absence
of output accounting policy keeps the existing explicitly partial path.
The logical admission theorem does not prove physical footprint, collector
behavior, refusal workspace funding or native issue/settlement authenticity.

The pre-factory caller reads `fn-rlo-capacity` from its installed private
ledger (ready instance: the captured `FILE-LIMIT`; otherwise zero). It does
not reread a mutable service policy to decide an existing lease's capacity.
Until an actual command footprint producer exists, `fn-ocap-unpriced-tariff`
produces an explicit `(:unpriced FAMILY)` and accounted admission refuses
before the command factory; this is not a priced NEWNEWS descriptor.

The actual admitted native reader now calls `fnn-owner-output-begin-locked`
before buffer filling, then `fnn-owner-output-prefix-locked` before the chunk
factory. The holder is discoverable on the mux connection before reader entry;
known returned issuance survives a later refusal, while torn issuance retains
its unresolved native envelope without retry. Capacity comes from the actual
installed private ledger. `fn-owner-output-tariff-preview` currently delegates
`fn-ocap-unpriced-tariff`: every incomplete family remains explicitly unpriced,
and this source does not activate an optional supported profile. The accepted
`NEXT` alone reaches the span helper; cold fallback validates the line end
before dispatch against that same prefix. Every remaining input suffix stays
with the connection for a later response operation. SCN-1111 uses actual
helper/admission bodies, with recording wire/typed boundaries; its positive
tariff is injected to discriminate prefix consumption and is not a produced
physical footprint. Allocator/collector, setup workspace, root/version custody
and complete native realization remain open.
## Retained matcher extent (PRF-1261)

The NEWNEWS matcher continuation has a carried proof-only extent invariant,
not a served whole-state scan. `fn-wml-start-retainedp`,
`fn-wml-one-retainedp` and `fn-wml-step-retainedp` connect the actual matcher
entries to that invariant. With natural decoded-name bound N and a carried
retained state, `fn-wml-retained-owned-bound` bounds control/rows plus shared
decoded target by `38+6P+6M+11N`; borrowed parsed-pattern tree cells are
exactly `3P+M` under the parsed-pattern-list premise and charged once by their
owner. P counts parsed patterns and M their token items. This maximum logical
region extent is separate from cumulative per-step constructor charges and
from native aliasing, physical heap bytes, integer widths, allocator/collector
behavior, retained source pins and outer controller/mux storage. Those terms
remain required in the actual selected output tariff before accounted
command admission can hold.

`fn-rlo-issued-token-is-live` connects an actual successful issue to its
receipt consumers: with typed input and actual `:drawn` result, the returned
token is live against the returned ledger and the same operation generation.
Accepted issue itself establishes input shape; that redundant external
hypothesis is absent. Negative-generation corruption and uninstalled refusal
supply separate removal witnesses. This property does not establish free-chain
completeness or authorize a physical receipt.

Actual `fn-rlo-output` and `fn-rlo-physical` settlement invalidate the token
against the resulting ledger (`fn-rlo-output-settled-token-is-not-live`,
`fn-rlo-physical-settled-token-is-not-live`). The only premise is their actual
`:settled` result. Replaying either receipt with that token returns `:stale`
and preserves the ledger, so it cannot push the same released row onto the
free chain twice. Literal settled-result positives and removal witnesses
exercise both receipt orderings. Complete free-chain membership and the
physical producer's receipt authenticity remain separate obligations.

A settled output row at the final u64 generation is retired; settlement
preserves the previous free head and never resets its generation
(`fn-rlo-exhausted-settlement-keeps-free-head`). Other idle rows remain
issuable in the generic typed protocol. The two receipt orderings have
logical and normal-counterpart native fixtures. These are protocol witnesses:
the current fresh native service also exhausts its independent global
response serial by such a max-draw history, so the subsequent issue witness
is not claimed as reachable served progress. Physical heap funding is
unchanged.

The actual private decoded worker has a separately named partial backing
projection, `fn-dwb-fixed-storage-vector`: `(86928 0 0 1 1)` in the existing
five-component page-read ledger, with `fn-dwb-coverage` explicitly returning
`:partial-fixed-storage`. The selected `fn-crl-array-octets` model counts the
eight-field job, twelve-field carry, sixteen-field digest plus sixty-four
frame pointers, twenty decoder registers, 16384 requested-window octets, and
four two-field octet wrappers. Native constructor observation shows the two
single-array stobjs are direct vectors; the projection conservatively retains
two 32-octet logical parent allowances that native lowering elides. Its selected
backing model before those allowances is 86864 octets. It includes their
four original empty arrays and exact reserved buffers of 64, 65536, 3494 and
64 octets. It does not price pointed-to integers/conses, controller and token
graphs, borrowed sources, registry slots, constructor transients or GC.
Same-pool draw precedes construction; this partial projection cannot authorize
the configured complete-profile issuer. Actual constructor dimension checks
and the physical allocator boundary remain separate from this arithmetic.

Actual output issue and both settling receipt consumers preserve an exact
terminating free-chain witness (`fn-rlo-issued-chain-is-tail`,
`fn-rlo-output-settled-chain`, `fn-rlo-physical-settled-chain`). A successful
issue consumes its head; settlement pushes the reusable row once or preserves
the old chain when that generation is exhausted. The proof-only witness checks
idle phases, reusable natural generations, in-range row identities and exact
links without adding a served scan. Successful actual installation establishes this chain for every user row
from2 through slots-1 (`fn-rlo-install-establishes-free-chain`); its only
premise is the actual `:installed` result. A zero-count input must be genuinely
fresh: padded arrays with old phases/generations are refused before mutation,
even when typed and shape-valid. Positive-count repeat installation keeps
its existing `:already-installed` refusal. Coverage of every reusable idle
row after arbitrary histories remains owed; the issue/settlement boundaries
assume the prior chain is valid and the actual method reports `:drawn` or
`:settled`.

The native decoded issuer reserves its worker before the semantic draw and
publishes that reservation to the retained response read. After an assigned
result, it installs the exact token and response dependency before setting the
worker runnable or notifying its waitqueue. A notification failure therefore
retains a discoverable read/token even if the physical child runs. Ordinary
no-token refusal removes the reservation; an escaped draw or binding preserves
it and is never retried as a fresh issue. This is native custody ordering,
not a proof of a complete decoded tariff or interpreter realization.

The shared native condition-wait observation reserves the release record while
E is owned and completes it only after the actual primitive returns. It emits
reacquisition only when the returning thread owns the mutex. A timeout returning
unlocked has no fabricated reacquisition or second release; an escaping wait or
unobserved unlock invalidates comparison. The executor loop and timed executor
wait consume this seam. Finite actual SBCL contention/timeout schedules check
producer order; remaining O/P coverage, packet/model replay and global schedule
preservation remain open, independently of decoded storage funding.

## Reusable decoded backing (PRF-1298)

A physical cold worker may retain one private decoded job across requests only
when its installer has permanently reserved that backing. The selected partial
layout projection is `fn-dwb-reusable-baseline-vector(workers)`: the existing
fixed constructor backing plus the two-field native activation envelope, with
one copying allowance. `fn-dwj-reserve` reserves input/ring/table/output capacity
before worker launch. These are startup reservations, never refunded merely
because a job finishes. Controller graphs, arbitrary integer widths, collector
behavior beyond that allowance and work tariffs remain separate obligations.

After actual worker return and the last scalar borrow, native code holds E and
calls `fn-owner-page-decoded-job-retire` before settling the pool token. The core
requires the matching returned or cancelled-returned token, stable owned carry
and no pending read. `fn-dwa-retire` removes all prior root/source/token/controller
references and resets assignment metadata; `fn-dwj-retire` retains its private
backing. It refuses running, torn, stale and pending-read states. The retired
job cannot publish a scalar byte even before the old token is settled. A new
assignment must obtain a fresh pool token. Native `:calling` activations are
never candidates for reuse after a failed semantic call.

Only the actual permanent-backing installer can select
`fn-dwb-reused-window-vector`: no resident backing is charged a second time,
but each job still consumes its worker slot and a nonrefundable read identity.
The existing per-job constructor projection stays available for older callers;
a host flag or the existence of a buffer is not reservation authority. Current
source alone does not claim the new startup/retirement consumers have executed.


### DEFAULT page-read startup (HST-048)

Before Store open, `fn-prstartup-default-plan` consumes actual dynamic-space,
occupied usage, sealed Store profile, image observation, nursery, exact cold
and output policies, connection count, root, existing direct-worker count,
cache limit and OS descriptor allowance. A complete cold policy remains
unpriced and refuses. DEFAULT selects an explicitly partial fixed-storage
projection, without inferring global collector, controller or source-graph
coverage from a storage count.

The producer protects the existing composed heap figure and explicit output
pool, then derives an affordable descriptor/table capacity bounded by the OS
allowance and the selected table representation. Its minimum covers the
existing cache insertion overlap. It prepays all five native tables, the
fixed guard cache and reusable decoder backing; per-file registration
working reserve is a minimum affordable root-path quantum. Existing issuers
charge actual paths and integer metadata. Capacity exhaustion refuses further
registration and requires resumable maintenance/backpressure; it is not a
ceiling on stored data or a claim that Store transaction count bounds retired
file incarnations.

`fn-owner-page-read-install-default` installs only into the existing fresh
pool. DATA8 preserves the original five ledger/configuration fields and
binding revision at position five, followed by the reservation/readiness
marker and worker count. Both legacy ledger publication and binding revision
publication preserve that tail. Each native worker constructor must first
pass `fn-owner-page-read-default-worker-constructionp`; successful constructor,
eager reserve and worker startup precede `default-worker-ready` and physical
free-roster publication. Torn startup leaves the bit clear and cannot allocate
an unreserved replacement. Reused decoded-window admission requires the
matching ready slot, charges a slot and read identity, and retains permanent
backing throughout return, retirement and settlement. Installation never
resets or refunds a live pool. SCN-1130 covers the native ordering and orphan
cleanup independently of the numeric projection.

The actual `:run` launcher calls `fn-prstartup-extend-operation-reservation`
to add the minimum DEFAULT persistent backing and registration quantum before
the independent output contribution. Existing direct-worker thread reservation
is retained, not counted twice. The extension validates total process memory
against the captured machine. Offline actions and explicit cold policy keep
their reservation behavior. This additional run requirement is outside the
older base init-to-reopen affordability theorem; init sizing needs the same
next-run producer before that stronger claim can hold.

The full Store figure already protects recovery workspace. Legacy funded
entry/discovery buffers currently draw from the spare pool as well; partitioning
that protected recovery subreserve is still required to prevent double
exclusion during nonempty Store open. A minimum DEFAULT launch contribution
does not establish complete recovery/cache transient funding.

### Independent peer flight pool (HST-049)

Catchup spool flights use a distinct private typed bank. The operator policy
captures heap octets, spool disk octets, maximum flights, maximum workers,
spool allowance per flight and total metered work. Absence creates no grant.
Each flight has separate lifetime and work rows, selected by ACL2. Actual
`fn-rl-draw` precedes private buffer, spool and worker constructors. Lifetime
demand includes the selected direct 512/64/512 byte arrays, digest register
and fixed frame array backing, native stack/runtime, two descriptors, one
worker and a spent read identity. Work quanta draw their actual core-selected
work demand on the companion row; settlement retains spent work. Exhaustion
refuses before cursor mutation and cannot silently truncate an accepted batch.

The independent launcher contribution adds the policy heap and worker threads
with whole-machine validation. Startup checks the actual dynamic capture and
protected other banks. DEFAULT must protect this peer heap rather than consume
it as spare headroom. No output, syncer or page-pool slack grants peer authority.

This initial producer is explicitly `:partial-fixed-storage`: native flight/
request/completion/mutex cells, owned controller/hash frame payload graphs,
transient octet lists and garbage, TLS, integer widths and collector behavior
still require the concrete consumer representation. The flight lease survives
peer ACK, local response, timeout and cancellation. Settlement requires actual
worker return/join, physical socket closure, spool cleanup and no future
publication or owner-close callback custody. Bounds owns the real spool driver.

The optional `peer-flight-profile` file in the Store root is exactly `FNP1`
followed by six big-endian u64 fields in policy order, using the existing
catchup codec. The read bound includes one trailing byte to detect malformed
extra content. Absence gives no authority; malformed or unsupported fields
refuse. A spool allowance must be below 2^63, matching actual signed `off_t`
I/O; a u64 policy that native seeks cannot represent is rejected before install.
The selected storage inventory also includes both native octet wrappers and
their discarded empty arrays, without assuming collection has occurred.

`fn-prstartup-default-plan-with-peer` is additive to the existing twelve-input
DEFAULT API: its final argument is the captured peer policy. It protects the
peer heap before selecting page-table backing, and `fn-prstartup-peer-grant`
checks the other bank's actual selected heap allowance before independent
peer install. The old wrapper remains available for callers without peer
authority. Generic codec round-trip and complete composed allocation bounds
remain proof obligations; source fixtures are not physical qualification.

### Protected Store growth (HST-048)

Live profile growth may transfer idle DEFAULT resident authority to the Store,
without returning installed backing or issued custody. The actual owner/extent
mutex spans preview, publication and apply; the pool reduction frames every
charge, identity, binding and ready marker. Refusal keeps the funded profile at
restart. Lowering a profile does not refund memory without physical retirement.
Runtime protection uses the captured fixed-process collector trigger rather
than recomputing the launcher's least-space trigger. Full allocation/collector
coverage and the native boundary theorem remain open (PRF-1310).
