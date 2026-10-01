# Persistent all-event history directory (STO-10003)

This is the internal concrete component for the architectural design in
`planning/dense-history-epoch-2026-09-30.md`, owned by the dense-history lane.
It records every committed Store event, including NIL and policy events.
Catalog generation C and event-prefix length F remain separate. The fixed
256-reference page bounds a single constructor and append; it is not a limit
on total history (D27).

The immutable Source9 holds source/epoch/root/publication identities, a newest
first forest, maximum height, page count and F. Forest blocks have increasing
power-of-two widths and chronological older/newer branches. A new page creates
one carry leaf; each grow step merges and pops one equal-width head, or finishes
with one cons before the unchanged remainder. The chronological flattening
proof connects this actual cursor to old pages followed by the new leaf.

The read cursor derives page index from ordinal/256, skips one forest cell per
step and traverses one branch per step. Actual begin/step/leaf refinement links
the result to chronological flattening; yield decreases a structural measure.
Whole-tree predicates and flattening are proof models, never served guards.
Physical addressing consumes the issued slot least-significant bit first and
stops at remaining slot zero. A node may own both a fixed page and children.
Read, append and construction derive route depth from `integer-length(slot)`;
the backing global depth is retained metadata, not an address selector. Thus
adding a deeper page neither relocates old pages nor changes their addresses.
This supersedes the unactivated fixed-depth layout; it does not reinterpret an
activated predecessor store.

Physical provider lookup preflights depth+1 fuel, traverses registered children,
and reads the fixed page with exact stamps and captured prefix. It does not
retain an interior child alias between calls. Missing keys return unavailable.
ACL2 requires a creator expression in a nested table binding: the raw bound-NIL
fallback remains an explicit construction-invariant obligation before native
activation; source BOUNDP alone is not its proof.

Private new-page preparation retains its construction intent before raw
creator effects. One call creates at most one missing child or initializes
one fixed page; yields resume that retained path. Once the page is ready, the
actual directory carry cursor builds the next forest privately. A prepared
tail retains that exact forest, page count and maximum height; publication
still waits for actual durable completion. Existing occupied pages cannot be
reinitialized. The complete old captured read result (status, value and fuel)
is preserved by the guarded constructor. This component has matching normal
source evidence in `planning/evidence/history-prefix-page-growth-2026-10-01`;
the high owner PROGRAM composition remains unqualified.

The current internal physical slot is the same APR-issued nonce. Its actual
issuer refuses when NEXT reaches the existing PRL budget identity limit. A
supported installed profile must therefore establish route quantum at least
`integer-length(limit - 1) + 1`, using that positive existing namespace limit,
not live page count or a second stored-history ceiling. Spent identities are
never refunded. Genuine namespace rollover/rescue must preserve old source
and page custody; this component does not provide or qualify that protocol.

Canonical `fn-history-backing` retains the exact pending row separately from
produced6. The builder also retains original producer context/fields, registered
producer token, old immutable Source9, directory cursor and preparation receipt.
Default registration refuses before interning. Actual owner preparation owns
the registered token/transaction and complete next-ready result; this component
has no native setter or genuine allocator-family issuer.

Completion3 is internal: `(:history-completion token actualDurableTxid)`.
Registration compares the retained operation token/txid and epoch. E publication
appends the retained row to the registered page and installs the prepared source
once; C-only publication changes the source association without appending or
incrementing F. Replay returns `:already-completed` or `:consumed` and preserves
the complete backing. Uncertainty fences the producer while retaining candidate
roots, preparation and debt. Logical MV composition is not raw crash atomicity.
The owner must publish Store/CP/config/source together in its serialized action.

Capture retention derives authority from the actual STATE custody slot. It
retains the actual current source pointer and pins the registered epoch once.
Reads of old same-epoch sources use that retained registration, not newer current
source equality. Return requires the actual quiescent slot, NIL continuation and
NIL read state. Retirement requires current/writer/pin references zero and one
registered physical handle return per inventory pop. Inventory exhaustion alone
never retires an epoch or returns retained debt. The physical relinquishment
producer and final settlement remain unavailable.

PRF-1190 and PRF-1191 are conditional source components. SCN-1071 exercises actual
directory kernels and concrete page publication under explicitly synthetic test
registration. No native route, image, deployment, whole operation tariff or
served completion is qualified by these fixtures.

The registered census uses guarded LOGIC BEGIN and STEP transitions. Their
PROGRAM boundary functions delegate once and return the actual backing/STATE
results. PrepareIntent reads the committed count from its same captured base
Store and retains it with that base and the current source before semantic
work. Census BEGIN consumes that retained count and checks its APR association;
it does not recompute the history or accept a host count. The actual source
constructor establishes its five natural cursor fields. STEP checks that fixed
scalar domain before source Tick, and retains returned source/remap frames in a
fenced job on refusal. The original-prefix/remap relation remains a carried
proof invariant, not a served validation walk. Source-only guard/effect proofs
and normal capture-component certification do not qualify an installed
canonical allowance or the authenticated cold row/byte worker.
