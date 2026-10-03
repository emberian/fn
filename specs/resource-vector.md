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


## Shared output allocation pool (HST-047)

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
