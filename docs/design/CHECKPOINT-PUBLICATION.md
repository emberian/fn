# Checkpoint publication and recovery integration

`books/checkpoint.lisp` is source work, not an admitted or served checkpoint
machine. It cannot advance the allocator cut or mark a candidate promoted.
`books/checkpoint-kind.lisp` declares its three concrete core children but is
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
all resumptions, and must bind the reference's storage domain to the actual
read device. The current function does not issue that read.

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
caller-supplied record nor establishes anchor durability.

## Publication transition still required

The producer reserves every metadata allocation before serializing the
allocation map, including the map's own storage. It freezes C's installed root
and materialization generation, builds the metadata manifest, allocation map,
proof directory, event frontier and successor arena through bounded machines,
and journals checkpoint installation through the existing batch writer.
No preparation, decode or journal-install return authorizes discarding roots.

After journal durability/install, a coordinator issues both writes to the
other anchor bank, retains their actual operation identities, waits for both
validated completions and a covering fence, then marks that bank promoted.
Uncertain completion retains old and new candidates and their dependencies.
Only that promoted state may request bounded allocator cut advancement.
Old checkpoint/recovery protection is released one owned edge per step after
that advancement is complete. No boolean supplied by a host or a caller can
stand in for the issued-operation and completion evidence.

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
and a cut-removal control through the actual allocator API. It is source only,
not executed. Lisp structural parsing and named-file secrets scans are the
only checks run for this checkpoint source milestone. Admission, guard proofs,
physical-page positive/corruption/truncation controls, full installation and
anchor crash cuts, dependency protection, restored-map coverage and composed
served lifetime/progress witnesses remain outstanding. The product reclamation
requirement remains unbound.
