# Cold checkpoint installation evidence — source milestone

Boot now investigates each candidate's authenticated role5 arena before moving
to the next candidate. `checkpoint-recovery-evidence-boot.lisp` binds the actual
boot phase/index/generation, root and RX workspace, arena tag and current exact
candidate descriptor. One authenticated ordinal yields an extent/epoch/allocation
through `fn2-checkpoint-restore-arena-target`; no host chooses a physical tuple.
Three existing 4096-byte units are retained in the existing 64KiB root workspace.

`fn2-checkpoint-recovery-evidence-physical` reuses the actual frame/seal/page
checkers. The seal frame binds exact extent/allocation, namespace and commit. Its
canonical body binds immediate predecessor, records and dependencies; final seal
must equal the anchor's retained batch hash. The immediate predecessor is parsed
from these sealed bytes, **not** from the anchor's previous-checkpoint hash. The
records frame commitment and dependency Ref/page hash are checked before the
record workspace is copied to RX and opened. Other nonmatching arena entries are
skipped, so reserved/unwritten/older entries need not be the final batch.

`fn2-checkpoint-recovery-evidence-record` consumes one record using the shared
actual journal decoder, checking the event range/order, occurrence, domain and
incarnation envelope. Exactly one installation member must match the candidate's
checkpoint and complete descriptor Ref/hash, after its descriptor cut. Unknown or
malformed records refuse evidence. A second matching physical batch is rejected.
All arena ordinals must finish before `fn2-checkpoint-recovery-evidence-ready-p`
returns true; finding a member alone is insufficient.

The concrete child `fn2-core-checkpoint-recovery-evidence` has row0 for one job and
rows1..4 for the four fixed physical anchor slots. For candidate c, row(c+1)
retains installation commit/event, actual journal extent/epoch/allocation, arena
tag/ordinal, checkpoint/cut and complete descriptor tuple. Its hash stripe starts
at `256 + 160*c`: batch hash, previous-checkpoint hash, anchor hash, descriptor
hash, immediate seal predecessor (32 bytes each). The previous-checkpoint hash
is unresolved linkage evidence. Zero does not authorize a genesis inference.
There is no selected-base bit, largest-number selection, live builder ledger
requirement, allocator reconstruction or live checkpoint installation here.

Source checks only: forms balance and diff whitespace pass; named-file secrets
scan is run before commit. The prepared actual-entry negative fixture checks that
wrong boot phases cannot consume or create evidence. It is not a positive cold
recovery witness. No ACL2 admission, guard/preservation proof, certification,
simulator, native or remote computation was run. Actual physical positive and
hypothesis-removal controls remain pending qualification.

Parent owns linkage/selection, exact allocator reconstruction, root restoration
and ordered suffix replay. Nonempty boot still stops at :checkpoint after all
candidate investigations. Evidence collection does not enable serving, phase2,
publication or FREE. Selection must also account for the current publisher's
unresolved previous-checkpoint producer semantics and reread a selected map/arena
if the retained private intake ledger belongs to another candidate.
