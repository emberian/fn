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
Physical provider lookup preflights depth+1 fuel, traverses registered children,
and reads the fixed page with exact stamps and captured prefix. It does not
retain an interior child alias between calls. Missing keys return unavailable.
ACL2 requires a creator expression in a nested table binding: the raw bound-NIL
fallback remains an explicit construction-invariant obligation before native
activation; source BOUNDP alone is not its proof.

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
