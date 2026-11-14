# Transaction child callback integration

This candidate starts at `e4f74c279` and merges corrected init and shared
compiler foundation `b7b1f77af`. It connects the production transaction
operation declarations to the shared lowering compiler and provides
`books/assembly-callbacks-d-txn-children.lisp`, an alternative callback root
that actually instantiates `:children` arms, their `:wrappers`, and the machine
run interface. It must not be included alongside the core-arm callback book.
The main assembly still selects the core-arm book until the candidate's
composition and evidence gates pass.

All 35 original txn function bodies are unchanged; `core.lisp` and
`profile.lisp` match the corrected `b7b1f77af` foundation exactly.
The current stop-success and issue-effect changes are therefore retained.
The compiler prerequisites are the previously source-tested modular reader,
mutable product and scalar-recursive implementations, plus the fixed-length
accessor guard bridge. Their old 22-book fixture records do not certify this
candidate or its served callbacks.

## Concrete production evidence

`tests/txn-child-extraction-unit.lisp` consumes the actual child callback root.
Its wake-upload constructor initializes the real core and upload partition,
sets a draining upload's transaction identity and generation, and clears the
wake handoff. Shared `fn2-test-core-snapshot` captures every child as an
ordinary value. The runtime witness compares source and generated face outputs
and full effects, checks the wake occurred, and checks a stale generation
changes nothing. A same-ABI, same-guard identity mutant drops the wake.

The existing `fn2-square-evidence-events` API receives quoted literal bindings
from that complete snapshot. It must prove the actual live statement's whole
guards, antecedent and conclusion, plus the false mutant conclusion. Both the
unconditional face equality and guarded executable equality are bound, then
rechecked through `fn2-assert-square-evidence`. This is a connection to the
existing evidence store, not a constructor extension or a second ledger.
Runtime teeth remain separate from the generated ground proofs.

The shared evidence implementation is exactly `57ab79c04`'s
`books/square-evidence.lisp` (including the live-statement fix from `6cff53bc0`).
Snapshot support is exactly Sol's `2e3567ba9` version. Neither is newly claimed
certified in this candidate. The new production witness has only passed source
parsing and static connection controls so far; no ACL2 result is claimed.

## Remaining qualification

First load the complete child callback candidate, resolving any missing child
mapping, row/table effect, guard, ABI, or arm composition failure. Then run the
wake witness and its formula-bound controls. Promote the main callback only
after these and the remaining operation evidence pass at the integrated source.

The fourteen newly connected root operations are claim-release, offer,
count-next, add-group, xref, put-post-for, put-evidence-for, prebind,
authority-allows, principal, authority-depend, group-of, wake-upload and
groups-limit. Eleven return core and expose both unconditional face and guarded
execution squares; three are read-only and expose whole-result equality.
Thus at least 25 root square evidence pairs are required. The wake candidate
supplies two pairs whose proofs remain unrun; the other 23 root pairs still
need meaningful success/refusal states and designated mutations. Transitive
generated helper squares must also be audited in the actual resulting ledger.
An extraction equality alone does not establish authorization policy adequacy.
The membership lane's later add-group semantic changes require fresh evidence.

No remote compute was started for this candidate. The local static control
compares every original txn defun byte-for-byte with the integrated base,
checks current core.lisp is unchanged, and checks the child callback route.
Named-file secrets scan and diff whitespace checks pass.

## Shared operation frontier discovered from actual arms

A structural walk of every txn `:do` identifies eight further dependencies
without child mappings in the integrated base: commit-admit-txn,
identity-decide, successor-bind/release/resolve/stage, upload-extents-of and
upload-post-owner. These are now named in their original `defcost` declarations
and derived through the same product family before child arms are emitted.
No consumed cost row is mutated: declaration sealing remains authoritative.
The family planner uses declared names for new boundaries and reuses an
already-proved matching boundary when a previous dependency generated it.
All original definitions in the four owning books remain unchanged.

The earlier 25-square count covers only the fourteen local operations, not
this additional shared frontier. These eight operations need their own actual
result/effect evidence; the final resulting ledger is the authority for the
complete count. Generated reclaim/link operations and table-effect consistency
must also pass the actual child-arm callback gate. The frontier is not closed
by the presence of declarations or by the old generator fixture records.
