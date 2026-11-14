# Checkpoint publication and recovery integration

`books/checkpoint.lisp` is source work, not an admitted or served checkpoint
machine. It cannot advance the allocator cut or mark a candidate promoted.
`books/checkpoint-kind.lisp` declares its four concrete core children but is
not yet included by `assembly-index.lisp`. No persistent release is enabled.

## Implemented boundary

`fn2-checkpoint-prepare` records a candidate locator, copying its expected hash
out of scratch digest rows. Six concrete reference rows and 192 owned digest
bytes belong to each active candidate: the descriptor and its five roots.
The profile limits simultaneous candidate work, with admission refusal; this
is not a retained-history limit. No directory slot is recycled yet.

`fn2-checkpoint-check-step` compares the checker context against that exact
locator, runs the physical page checker, decodes the descriptor payload only
on the checker's successful return, and copies all root identities and hashes
before returning. Exact payload consumption and the checkpoint identity are
checked. The caller must own the checker row and immutable input lease through
all resumptions. Preparation and edge attachment reject foreign storage domains;
the current native backend serves domain 0, matching B's format writers. The current function does not issue that read.

`fn2-checkpoint-retain` acquires one selectable-checkpoint edge per call.
`fn2-checkpoint-retainedp` rechecks six exact holder/allocation tuples;
cached flags alone do not establish protection. These six root-page edges
are only the direct roots. Their complete dependency closures must be retained
before promotion; six protected pages do not imply protected descendants.
The physical profile uses three units per extent, as the existing B readers do.

`fn2-checkpoint-install` consumes the existing decoded checkpoint-installation
record and the verified containing commit supplied by the journal installer.
It compares the full descriptor reference, including all 32 hash bytes, and
rechecks the six direct edges. Its containing commit must follow the cut;
there is no adjacency requirement until actual planner serialization proves
one. The operation records installation only. It neither authenticates a
caller-supplied record nor establishes anchor durability. Repeated installation
is idempotent only at its original containing commit; a conflicting containing
commit is refused.

## Publication transition still required

The producer reserves every metadata allocation before serializing the
allocation map, including the map's own storage. It freezes C's installed root
and materialization generation, builds the metadata manifest, allocation map,
proof directory, event frontier and successor arena through bounded machines,
and journals checkpoint installation through the existing batch writer.
No preparation, decode or journal-install return authorizes discarding roots.

`books/checkpoint-publication.lisp` now implements the lower publication protocol:
BEGIN copies installation seal, predecessor checkpoint and geometry digest bytes
into owned state, PACK builds each anchor using the generated codec, and
CHECK-PACKET runs the actual anchor checker and checks the full descriptor and
seal evidence. `fn2-checkpoint-publication-seal-step` runs the existing `:anchor t`
checker on that same owned output lease through bounded resumptions before
CHECK-PACKET can run `:anchor nil` and set a verified bit. Packet stages and a
stored checker row/base/packet identity bind both continuations; a fresh phase
requires an idle checker, and PACK refuses any live checker interval. No verification boolean is
accepted. Two separately owned immutable output leases survive through the fence.

STEP issues the first write, waits for its exact slot/generation at validated
harvest, issues the second write, then issues a covering fence. Short completions,
failed completions and uncertain issuance retain uncertainty. Only the final
matching successful fence records I/O completion. It does not mark the descriptor
promoted or advance the allocator cut. The harvest extension is declared on the
publication child; registration remains held outside assembly-index.

BEGIN derives the other bank from stored state and requires boot-owned checked
layout state. No operation currently binds that layout-ready field, so these
operations cannot yet issue served writes. After dependency retention and startup
selection compose, a coordinator must mark the established bank promoted.
Uncertain completion retains old and new candidates and their dependencies.
Only that promoted state may request bounded allocator cut advancement.
Old checkpoint/recovery protection is released one owned edge per step after
that advancement is complete. No boolean supplied by a host or a caller can
stand in for the issued-operation and completion evidence.

## Concrete image geometry

The native worker already accepts ACL2-selected byte offsets and ordered fences;
there is no backend restriction to journal offsets. The old image geometry reserves
only two epoch slots at `image-size - 8192` and `image-size - 4096`. These use
`fn2-boot-record`, not checkpoint-anchor encoding. They cannot serve as the four
checkpoint slots.

`books/checkpoint-geometry.lisp` defines the new shared layout in physical units:
`[3*extents arena][genesis + groups][bootstrap][four checkpoint anchors]`
`[optional slack][two epoch records]`. Its minimum is
`4096 * (3*extents + groups + 8)`. Bootstrap is unit `3*extents + groups + 1`;
anchors are the next four units. The helper refuses the old minimum and states
nonoverlap/distinctness theorems. These are source statements, not admitted facts.
Boot init/read, image admission and recovery must adopt this geometry together;
shared-file ownership is being coordinated before those edits. The host must not
repeat this arithmetic.

## Recovery must reconstruct current claims

The present `payload-begin` and replay start in `recovery-machine.lisp` start
at commit 1. Payload discovery claims every historical article location before
ordered replay. That cannot safely coexist with physical reuse: an old article
record may name extent E at allocation A, while a later record names E at B.
Choosing whichever record was visited last would conceal conflicting history.

Recovery must instead select compatible candidates from all four checked
anchors, including newer singletons; validate each descriptor and dependency
closure; restore its allocation map and C metadata into a private recovery
view; and seed chain verification from its named frontier. A damaged newer
candidate cannot be discarded merely because an older bank has two copies.
The allocation map requires checked coverage of the arena and uniqueness of
its extent entries, not a missing-entry-is-free convention.

Suffix replay begins after the selected cut, in containing-commit order.
Allocation/relocation/retirement/release transitions update that private map
before the corresponding current metadata claims are consumed. Old locations
are historical references, not fresh allocation requests. The source helper
`fn2-checkpoint-location-code` distinguishes `:historical`, `:current` and
`:conflict` against a restored map; it is not wired into genesis recovery.
Skipping old records without restoring metadata and allocation state is not
an implementation of checkpoint recovery.

An encountered checkpoint transition introduces its successor recovery arena.
Unresolved candidate identities remain quarantined, and backend exclusion of
pre-crash physical I/O precedes orphan release. A journaled writer-epoch
transition and its fence precede ordinary mutation. Current in-memory epoch
initialization does not fulfill that condition.

## Evidence status

`tests/checkpoint-unit.lisp` prepares a local physical reuse/frontier control
and a cut-removal control through the actual allocator API.
`tests/checkpoint-publication-unit.lisp` prepares stale-generation and short-write
harvest controls plus old/new geometry controls. These are source only, not
executed. Actual SBCL READ with `*read-eval* nil`, Lisp structural parsing and
named-file secrets scans pass for these source milestones. Reader checks do not
evaluate the source forms. Admission, guard proofs,
physical-page positive/corruption/truncation controls, full installation and
anchor crash cuts, dependency protection, restored-map coverage and composed
served lifetime/progress witnesses remain outstanding. The product reclamation
requirement remains unbound.

## Concrete writer dependencies before promotion

The packet producer/checker is lower-level work, not an assertion that a caller
will preserve packet bytes. The actual generated worker must own all three pool
leases, admit PACK only in preparation, keep both output leases private and
immutable after verification, and release them only after validated completion
or backend exclusion. Its arms must establish that interval and frame unrelated
mutations; a caller assertion cannot replace this invariant. The lower PACK
entry already refuses every phase after preparation, but worker reachability
and lease ownership still need composition.

`fn2-checkpoint-installation-seal-row` in the registration book derives the
installation's seal digest row from the actual installed commit directory,
checks the saved seal-ready marker and predecessor, and uses the same stripe
as `fn2-commit-seal-context`. The actual worker must call that operation rather
than accept BEGIN's low-level batch-hash input from a caller. Its predecessor
checkpoint hash must come from the selected retained anchor, and its geometry
hash must come from the checked bootstrap/profile binding. Those two sources
are still absent in current genesis-only boot. No caller-provided matching
hashes can close those dependencies.

## Geometry hash frame and served boot source

Geometry hash v1 is BLAKE3 of the exact 21 ASCII bytes
`fn2/image-geometry/v1` followed immediately by the generated
`fn2-checkpoint-geometry-record` encoding. No newline, NUL, padding, Lisp
printing or host serialization enters the preimage. That record names version,
image byte size, 4096-byte sector/page sizes, three-unit extents, extent/group
counts, bootstrap and four anchor unit addresses, the final two epoch unit
addresses and storage domain 0. All integer encodings come from the generated
codec. This is a specified geometry frame, not the genesis record checksum.

The source boot path now uses the shared geometry for image admission, writes
this generated bootstrap during init, and compares it byte-for-byte against
its canonical configured encoding on reopen. It writes/scans all four distinct
checkpoint units before the two existing epoch records. Until full candidate
selection and physical plus semantic restoration exist, a nonempty checkpoint
unit refuses startup with `:checkpoint`; it never silently recovers genesis.
The empty-anchor path binds checked geometry in boot-config only after the
actual final startup fence succeeds. The bootstrap hash is copied into an
owned 32-byte boot-config array before scratch buffers can be reused.

These boot/executor changes are source only and await qualification together.
No existing image is read, rewritten, migrated or deployed by this work.
`tests/checkpoint-geometry-unit.lisp` supplies an exact all-fields generated-codec
roundtrip and truncation control, awaiting admission/execution.

`books/checkpoint-boot.lisp` now binds publication layout from the actual checked
boot-config state and loads its owned geometry hash into a worker-owned digest
row. Neither operation accepts a readiness flag or geometry hash from a caller.
Current boot's explicit empty-anchor restriction justifies an initial absent
base; supporting a selected nonempty base must change both startup and this
binding. The live checkpoint batch seal is separately derived from the installed
commit directory. Private packet leases and predecessor evidence still need the
actual generated worker and recovery selection before any promotion operation.

Candidate preparation/retention/check/install and publication begin/pack/seal/
check/issue now declare exact multi-child WFP/row preservation contracts for
core composition. These source contracts are shape statements, not admitted
proofs or lifetime/durability guarantees.
