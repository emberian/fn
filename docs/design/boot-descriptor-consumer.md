# Bounded BOOT descriptor continuation

`checkpoint-boot-descriptor` connects the qualified current descriptor reader
to the actual BOOT owner and retained anchor candidate. Its new functions are
source only; their guards, composed BOOT path and producer-driven fixture have
not run. The reader34 record does not qualify this addition.

The physical-family owner materializes `fn2-boot-descriptor-operations` after
the real BOOT kind, CORE and `fn2-boot-bootstrap-current-p`. That gate must check
the live machine snapshot/generation and full semantic and physical namespace
against a receipt minted after persisted-bootstrap verification. Packing an
expected bootstrap and final startup-Fence readiness cannot mint this receipt.
The lower shared `fn2-boot-bootstrap-receipt-p` is the owner/full namespace
comparison used by the descriptor callback and intended CORE gate.

`boot-bootstrap-pack` mechanically extracts the existing generated geometry
and bootstrap constructors with an explicit owner kind. The bootstrap encoder
retains its geometry source instead of resetting the owned destination.
`fn2-boot-bootstrap-pack-pool` uses the first sector of BOOT's existing 64KiB
page for expected bootstrap bytes and the next 32 octets for its geometry
hash. It cannot write a receipt. `fn2-boot-bootstrap-verify-pool` rebuilds these
bytes, compares the entire sector against the separate owned read window,
saves geometry and the complete namespace, and publishes receipt generation
last. A mismatch cannot mint authority. It needs no third lease.
Before construction it checks the two backing extents are apart using the
same base/capacity relation as `fn2-pool-extents-apart`. Distinct slot numbers
alone are insufficient in arbitrary well-typed pool tables; alias refusal
leaves all carriers unchanged before expected bytes can overwrite the read.

The CORE verification wrapper must enforce the actual persisted bootstrap
read's address, complete count, no pending operation and prior verified genesis
namespace. The bootstrap wire format itself binds geometry; the earlier
genesis comparison and actual BOOT phase chain establish namespace provenance.

`fn2-boot-checkpoint-descriptor-target` requires the descriptor phase, matching
candidate and no pending read. Its lower target uses the authenticated anchor's
actual descriptor Ref and canonical restore target function. The resulting
sector must lie within the retained image size. The actor owns read issue,
saved address/count, completion validation and its retained receive lease.

`fn2-boot-checkpoint-descriptor-check` requires descriptor-step, matching
candidate, receive slot/generation and no pending read. Before writing context,
the lower callback validates the actual owned input window. The first visit
loads the candidate hash and saved bootstrap geometry and captures context.
Continuation visits retain that evidence. The existing CHECK-STEP alone checks
candidate Ref location/epoch/allocation, namespace and expected hash against
that context before FORMAT; this callback does not replicate those checks.
Only its authenticated success path captures roots and marks the candidate
CHECKED. A zero grant returns unchanged before seeding.

FORMAT's generated header decoder resumes; its page-span and B3 byte fallback
also accept small positive grants. A turn nevertheless includes fixed context
setup or, on authentication completion, semantic descriptor decode and root
capture. The BOOT operation's declared charge must cover that fixed work plus
its parser grant; the grant is not the total callback work. The owning routing
and cost registration remain with the physical-family owner.

`checkpoint-descriptor-input` contains the exact original restore target and
hash loader. Apply `checkpoint_boot_input_extract.remove_from_restore` to the
owning physical restore source at composition so it includes this provider and
does not define a second copy. The frozen before source and five source
controls check extraction, retained producers and input/callback ABI.

`boot-anchor-admission` consumes the same retained receipt and actual physical
anchor index. Its first visit checks an empty sector or generated anchor span
plus canonical zero tail, retains the span/context and yields. Later visits
resume the existing authenticated anchor intake without reseeding. A candidate
records the actual batch/predecessor/anchor digests before the checked mask is
published. Empty and rejected nonempty observations have separate masks;
owner/source/context refusals do not record successful census evidence.
`checkpoint-anchor-input` and `checkpoint-zero-range` move the original
physical-family functions unchanged; the extraction tool removes their old
definitions at composition.

The next executable fixture must create persisted bootstrap and checkpoint
bytes through real producers, crash and drive actual BOOT read completions to
descriptor-step. It must cover the actual routed small grant, zero-grant full
frame, expected hash and Ref changes on resume, namespace change refusal,
retained lease and all five captured roots. It must observe the real phase and
receipt; it cannot initialize them to simulate successful verification. The
new lower bootstrap producer, anchor admission and CORE routing are still
being composed, so this file does not register a fictitious fixture or
claim current served BOOT adoption.

The f849 author pilot accepted seven complete prerequisite books, including
the constructor book and its guards. It stopped at the explicit guard proof
for `fn2-boot-bootstrap-pack-pool`: the caller lacked output WFP facts and the
successful constructor's checked result-digest row. No component assertion or
anchor admission ran, and no certificate was recorded.

The proof-only `boot-bootstrap-pack-contracts` successor exports stored-guard carrier contracts
and the exact image/result-row facts established by successful construction.
Explicit instances connect the actual returned carriers to the verifier's
guard. The receipt setter bounds also follow from the existing successful
construction branch. These additions do not change any runtime body or stored
guard, and still need an author run.

Standalone certification then exposed the constructor's missing proof
dependency: the first author world had supplied `fn2-pool-read-byte-type`
through its unrelated reader import. Six prerequisite books actually
certified; the constructor did not. Its source now explicitly imports that
proof provider locally and uses the exact byte-return fact in the two copy
helpers' guard hints. Runtime and stored guards are unchanged, but the
constructor and descendant keys change and need a new author/record gate.
The next author ENTRY uses only this root's declared imports, including its
explicit private proof import, so the unrelated reader cannot mask the gap.
