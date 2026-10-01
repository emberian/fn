# The resource vector and the bank (HST-045)

This is fn's internal accounting contract, not an RFC requirement. The
founding goal it serves is ember's warranty: a full up-front accounting of
every resource spent on a user's behalf
(`planning/design-store-representation-2026-10-01.md` section 2, stage 6 of
its order). The precedent is seL4 untyped memory and KeyKOS space banks
(`build/coordinator/scholar-literature-2026-10-01.md` section E.3): the
system never allocates on its own; every request draws on its user's bank;
the owner's own needs are reserved before any user's; teardown destroys the
sub-bank. GPT-6's ratified invariant
(`planning/review-2026-09-30-gpt6-log2.md` section 2) is the one this
contract carries: `U + C + R <= B(P)` over a resource vector, `R >= W(P,
Omega(s))`, `dW+` charged before acceptance, and "refusal preserves funded
rescue capability" including the refusal's own transient execution.

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
state and never recomputed on a served path; and the slots, rows `(PHASE .
DEMAND)` indexed by position, so the executable twin is a direct-index typed
array. Phase 0 idle, 1 drawn, 2 a sub-bank whose demand is its whole budget:
sub-banks partition their parent, and a sub-bank's unused slack is not its
siblings'. The transitions return `(mv WORD BANK')`, a refused one returning
the bank itself:

| transition | effect | refused by name |
| --- | --- | --- |
| `fn-rv-draw slot demand` | charge an idle slot: drawn + demand, phase 1 | `:invalid-draw`, `:slot-busy`, `:resources-unavailable` (exactly when drawn + demand is not within the budget) |
| `fn-rv-open slot budget` | the same charge; the slot becomes a sub-bank (phase 2) | the same |
| `fn-rv-settle slot` | the draw's reusable coordinates return; its spent ones stay drawn; the slot idles | `:invalid-slot`, `:stale` (not phase 1) |
| `fn-rv-refund slot x` | x of the draw's reusable part returns now; never refused within what it holds | `:invalid-refund`, `:stale`, `:past-what-it-holds` |
| `fn-rv-grow slot x` | a sub-bank's budget grows by x (the owner's dW+) | `:invalid-grow`, `:stale`, `:resources-unavailable` |
| `fn-rv-destroy slot spent` | the sub-bank's budget returns less SPENT, what it had drawn in the spent coordinates | `:invalid-destroy`, `:stale`, `:sub-bank-overspent` |

`fn-rv-install budget baseline reserve nslots` builds the root: slot 0 the
owner's permanent baseline U (drawn), slot 1 the maintenance reserve R
(a sub-bank), before any user's slot exists; a start that cannot fund both
is refused by the draw's own word. `fn-rv-step` is every transition as one
function over an op `(:draw SLOT DEMAND)`, `(:open ..)`, `(:settle SLOT)`,
`(:refund ..)`, `(:grow ..)`, `(:destroy ..)`; `fn-rv-run` a sequence.

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
  effect is exactly the charge (the check precedes every effect).
- `fn-rv-settle-once`: a second settle of a slot is never admitted and
  leaves the bank.
- `fn-rv-step-keeps-the-other-slots`, `fn-rv-user-steps-keep-the-reserve`:
  a step on one slot leaves every other row; the reserve at slot 1 is never
  drawn by a user's step.
- `fn-rv-install-reserves-the-owner-first`: the installed root is okp with
  baseline and reserve drawn and nothing else.
- `fn-rv-destroy-returns-exactly-the-unsettled-draws`: destroying a
  sub-bank returns exactly its budget less what it spent, and that covers
  the reusable part of every draw the sub-bank still held.

Teeth: `tests/acl2/resource-vector-tests.lisp` (`defkeystone`, one removal
witness a hypothesis, corrupted-state witnesses labelled, mutations for the
hypothesis-free keystones), over a small node's root, a connection's
sub-bank, ten reads that exhaust the read-identity coordinate while every
octet has returned, the destroy and the reserve's growth.

## One accounting (`books/resource-vector-relations.lisp`, PRF-1210)

Each existing mechanism is a projection of the vector:

- Codex's cold-read gate (`fn-prs-fundedp B U R C`) is exactly `fn-rv-okp`
  of the root whose rows are U (drawn), R (a sub-bank) and C (drawn)
  (`fn-rv-prs-gate-is-a-funded-root`); `fn-prs-plus` and `fn-prs-below`
  agree with `fn-rv-plus` and `fn-rv-below` under the prefix embedding, and
  "release the reusable coordinates only" is `fn-rv-settle`'s split
  (`fn-rv-prs-release-reusable-is-the-settle`).
- PRF-380's credit ledger is the `:resident` coordinate: a ledger is an okp
  bank whose rows are BASE (drawn), COMPLETION and RUNTIME (sub-banks),
  CACHE and one row an operation, every other coordinate 0, funded iff its
  total is within its budget (`fn-rv-credit-ledger-is-the-resident-coordinate`,
  `fn-rv-credit-ledger-funded-iff`).
- PRF-198's heap reservation is a funded root whose `:resident` coordinate
  is the reservation's octets against the machine's and whose `:workers`
  coordinate is the threads (`fn-rv-heap-reservation-funds-the-root`).
- PRF-223's connection budget is a funded root whose `:resident`
  coordinate is the resident figure of CAPACITY connections
  (`fn-rv-connection-budget-funds-the-root`).

The four budgets are not one number: they are projections of different
roots (the launcher's, the owner's, the cold pool's). Unifying them is the
operation layer's work, below.

## The executable representation (`books/resource-vector-exec.lisp`, PRF-1211)

`fn-resource-ledger` is a stobj with no list: the budget and drawn vectors
as `(unsigned-byte 64)` arrays of `*fn-rv-k*` words; the slots as
direct-index typed columns (a phase column, one u64 column a coordinate for
the demands); Codex's per-read ownership row (the token `(id cid file eoff
elen trailer)`) as six more u64 columns by slot; Codex's five-element pool
list as typed scalars. `fn-rl-bank` abstracts it to the logical bank;
`fn-rl-wfp` is the representation invariant (every column holds COUNT
slots); per export a correspondence theorem states that the abstraction of
the export's result is the logical transition of the abstraction, so the
logical keystones are the typed ledger's. Marked `; GEN: def-representation`:
the hand-written smallest version until the generator lands.

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
3. **Settle once**: the matching completion settles the slot
   (`fn-rl-settle`) exactly once; a stale, duplicate or reused-slot
   completion is `:stale` and changes nothing (`fn-rv-settle-once`). A
   result the caller retains (a buffer, a cache entry, a record in the
   suffix) is a refund of the rest and a draw on the owner's slot, never a
   settle; a timeout settles nothing.
4. **The bound obligation**: `NAME$tariff-bound`, the body's cost twin is
   within the tariff and its work within the quantum, discharged by the
   census for derived tariffs and proved by the lane for supplied ones.
   The transient allocation of the refusal path itself is within the slot's
   prepaid gate term (GPT-6's "no borrow-then-return"), so
   `fn-rv-refusal-keeps-slack` holds of the whole entry, not only the
   ledger.
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
destroyed at close (`fn-rv-destroy` returns exactly what the connection had
not spent). Nothing of this is wired into a served path by this lane (MODE
2026-10-01 section 3: no gate before its producer).
