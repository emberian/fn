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
The physical profile uses the shared 64 KiB storage extent (16 physical units), independently of the three journal I/O resources.

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
`[storage-extent-units*extents arena][genesis + groups][bootstrap][four checkpoint anchors]`
`[optional slack][two epoch records]`. Its minimum is
`4096 * (16*extents + groups + 8)`. Bootstrap is unit `16*extents + groups + 1`;
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
image byte size, 4096-byte sectors, 65536-byte pages, sixteen-unit extents, extent/group
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

`books/checkpoint-member.lisp` supplies pure checkpoint-installation member
serialization to the existing B singleton planner. Its capacity includes 32
staging bytes plus both codec maxima. The descriptor hash is staged in that
same owned workspace, the generated frame/body encode after it, and the shared
overlap-safe copy moves the complete member down before fill shrinks. It neither
chooses a containing batch nor authorizes a checkpoint. Production admission
must require actual builder-produced evidence tied to the frozen C root and
materialization generation; a merely checked/read descriptor cannot substitute.

## Generated packet worker

`books/checkpoint-writer.lisp` declares one generated writer kind. Its arm
language owns an atomic three-window pool bundle, derives the real installed
seal and checked boot geometry, builds/seals/checks both private packets, then
uses the existing operation-tracked Write/Write/Fence protocol. It never returns
to PACK or context mutation after verification. Only actual final fence completion
and zero pending physical operations allow the bundle's release; uncertainty
retains ownership and stops for recovery. The private checker context operation
refuses live continuations, uses the final reserved stripe, and derives its
geometry from actual checked boot state.

Pool reservation preflights cached class counts for both 4 KiB outputs plus the
160-byte scratch window in one atomic operation. It does not hold one window
while waiting for another of the same D0 rank. Ordinary exhaustion changes
nothing; an invariant failure returns every allocated prefix handle for retained
uncertainty. Actual pool accounting still charges each concrete slot.

This worker is **unreachable-in-composition** until the actual frozen C root,
materialization generation, persisted metadata/allocation/arena builder and B
checkpoint-installation producer activate it. No generic activation API from a
caller's checked descriptor exists. The registry include and callback event
materialization remain held for coherent qualification. No theorem about an
unreachable worker is claimed. I/O completion still does not promote a checkpoint,
drop recovery roots, advance the allocator cut or release an extent.

The C snapshot seam must expose logical entries or owned resident source windows.
Physical storage extents now align with existing 64 KiB C run pages: one
allocation identity owns all sixteen physical units. The bounded adapter still
transfers at most 4 KiB per operation. Journal batches retain three I/O resources;
the initial unused journal extent space is an explicit efficiency cost. No
fragmentation/indirection format or smaller metadata-record ceiling is introduced.
Resident cache identities still cannot substitute for actual physical references;
page headers and child Refs must be built with the allocator-provided identity.

The checkpoint/boot physical-stride class was changed with
`tools/rewrite_checkpoint_storage_geometry.py`, using the shared structural Lisp
rewriter. Fixtures check comments/strings, unchanged commit-resource indices and
byte-work budgets, exact geometry probes, malformed input refusal and idempotence.
Run its narrow controls directly with `python3 tests/test_checkpoint_geometry_rewrite.py`;
the package discovery hook loads unrelated surface tests despite a filename filter.

## Descriptor construction carrier

`checkpoint-build-state.lisp`, `checkpoint-descriptor.lisp` and
`checkpoint-build.lisp` now hold the concrete descriptor job. BEGIN checks the
actual held C owner/token, checks the owned page/scratch leases, and calls
the real shared storage reservation operation before any
codec sees its physical identity. The job stores that exact extent/epoch/
allocation, workspace handles, cut from C, private checker stripe and aggregate
completion evidence. The shared worker owns the physical write cursor. No caller supplies a cut, reservation identity or readiness
boolean to this admission. BEGIN enters `:await-roots`: the descriptor identity
is available before the allocation map seals its construction set. The separate
ROOTS-READY transition requires completed actual C traversal and all five
physically completed same-token root carriers before entering `:pack`.

The generated descriptor and common reservation-checked physical-header codecs
produce a padded 4 KiB descriptor inside its 64 KiB allocation. The source binds
that actual page once, then the same generated page worker used by every root
owns sealing, verification, physical issuance and exact harvest. After actual
completion and ownership handback, descriptor consumption decodes and compares
the complete checkpoint/cut and five root references against the held source
job, loads the retained verified hash, and performs owned preparation followed
by CHECKED/root0 READY in one transition. The old descriptor-only physical
issue/harvest/checker path is deleted; ledger completion comes from the common
worker. Source bind/consume budget zero yields unchanged. None of these steps
commits the allocation, releases C or asserts durability.

The existing B lifecycle producer must consume READY with exact owner/token,
record allocation and checkpoint installation through its actual batch/fence,
and own durable installation. Selected-base restoration and retained descendant
closure still precede promotion and allocator-cut advancement.

The five root carriers now have construction token, source-complete and intended/
completed-byte fields. Their real metadata/map/proof/frontier/arena constructors
remain required; no generic setter authorizes those flags. Until those producers
connect, ROOTS-READY refuses `:roots-pending`. A decoded descriptor clears
construction provenance, so a read candidate cannot inherit prior readiness.
This is source implementation and shape-contract work, not admission, completed
root construction, certification or a served reclaim path.

## Physical construction ledger

`checkpoint-construction.lisp` retains one record per actual allocator extent.
Its reservation operation verifies the held C owner/token and atomically calls
the shared B allocator, then stores the returned epoch/counter, root role, page
ordinal and intended physical byte count. Descriptor BEGIN uses this operation.
Roles 0 through 5 identify descriptor/root descendants; role 6 identifies a
pre-reserved journal-arena ticket. There is no caller-supplied handle registration
or completion setter. Uncertain reservation identity is retained by the job.

This ledger permits bounded extent-by-extent map construction without keeping
an arbitrary-length resident handle list. It does not yet seal the construction
set, freeze foreign allocator mutations, project reservations into durable map
ownership, issue arena tickets to B, or reclaim ledger rows. Those lifecycle
steps and actual write-harvest completion precede root2/root5 readiness.

The physical construction columns remain in B and include only the allocator.
The C-aware reservation admission is in `checkpoint-construction-owner.lisp`;
descriptor state/codec/job and their construction registration are C-layer
orchestration over B leaf APIs. `checkpoint-kind-b.lisp` registers physical
B children without including C. This preserves the C-to-B dependency direction
and passes the actual C carrier rather than a caller-supplied ownership flag.

`checkpoint-map-format.lisp` declares the generated linked-page body header
for allocation maps, recovery arenas and retained event directories. The body
carries its type/version, exact C cut, total entry count, page/entry ordinals,
entry count, terminal bit and next full Ref. Header storage is padded to a
32-byte boundary after the page header. Allocation-map slots are 56 bytes and
arena slots 27 bytes, their existing codec maxima; entries and unused page
bytes require zero padding. Page counts include one terminal page for an empty
sequence. Actual readers must check the exact calculated count/continuity/link
shape, decode every slot and verify padding, then authenticate the linked child.
These format and local shape controls do not replace that reader or restoration.

`checkpoint-map-read.lisp` reads one actual extent per call behind the allocator's
exact retained `fn2-alloc-copy-ownerp` authority. Allocation entries copy every
persistent field, including foreign RESERVED rows. Arena entries come only from
same-token/owner role-6 construction rows whose ordinal and current Reserved
identity match. Non-ticket and nonrequested-ordinal rows return `:skip`; changed requested
ticket identities return
`:conflict`. The arena page builder must count only `:entry`, preserve ordinal
continuity, and compare its final count to the closed reservation plan.
The passive allocator gate alone does not establish that closure.

## Reservation closure before map copy

`checkpoint-plan.lisp` admits only the actual held descriptor job after roots
1, 3 and 4 have physically completed with matching construction identities.
It counts one ledger extent per step, including every completed descendant
and the already reserved descriptor. It calculates map pages from the actual
allocator row count. Arena/ticket demand reaches a monotone fixed point using
the actual commit allocation-record packing capacity; the arena pages themselves
need allocation records, while journal tickets allocate themselves through the
existing commit installer. Checkpoint installation gets its separate final ticket.
Each size step yields; insufficient actual free space retains the job as uncertain.

The planner then reserves every map page, arena page and journal ticket through
the same actual owner-checked adapter, one extent per step. A second bounded
scan checks exact Reserved identities, completed prior sources, role counts and
per-role ordinal uniqueness. Its extent-sized mark table detects duplicates.
It exposes reservation-closed state only after the complete scan. BEGIN resets
the actual journal-ticket scan/next controls, and reservation clears ticket claims.
No caller supplies counts, an identity list or a closure flag. The actual allocator
copy gate remains disabled until its coordinator consumes that state; closure
is distinct from physical completion of map, arena and descriptor or installation.
Whole lifecycle/closure assurance and actual generated composition remain owed.

The concrete freeze child now checks reservation closure, the unchanged held
descriptor owner, the B token retained at phase 0, and exact proposed/installed/
published commit and event equality with C's cut before entering phase 1. It
refuses a stopped core and never enters install or thaws. Its generated operation
is declared but has no production caller while source-root construction remains
incomplete. `checkpoint-map-pack.lisp` serializes one exact frozen source entry
into its calculated fixed-width page slot and zeroes its bounded slot padding;
page jobs still must initialize the whole page and authenticate headers/links.
Arena ordinal lookup scans physical extents because free-list order is independent
of ticket order; only the requested ordinal can produce an entry.

## Frozen map and arena source jobs

`checkpoint-map-build.lisp` builds role-2 and role-5 linked pages backwards from
the actual closed plan. It finds each pre-reserved page by exact role/ordinal,
zeros at most one sector per source step, and serializes one actual allocation
row or exact journal ticket per entry step. Every page carries the calculated
coverage header and a full next Ref copied only from a physically completed
child's retained verified hash. The common reservation-checked physical header
codec preserves the body. The source state then binds the page once and enters
`:bound`, where it has no packing/reset transition while the shared worker owns
the bytes. The composed source actor still must call TAKE and wake its actual
worker target, then wait for its ownership handback.

Consumption requires the exact retained completed extent plus the returned source
workspace, and advances to the previous ordinal. Only completion of ordinal 0
captures a role-2/5 root and its actual hash/source-complete carrier. No caller
supplies completion. These are concrete source/callback declarations, not a
registered coordinator, admitted ownership proof, authenticated selected-base
restoration or allocator reclamation. Candidate builder claims now bind the reservation to its nonselectable candidate;
root0 shared worker integration remains the next required ownership connection.

## Candidate construction ownership

Actual descriptor BEGIN now atomically claims its candidate as nonselectable
`:building` immediately after successful physical reservation, retaining C's
builder token/owner tuple. Refusal or uncertainty never releases that claim.
`fn2-checkpoint-builder-ownerp` requires the exact tuple and BUILDING state;
`fn2-checkpoint-builder-claimp` recognizes the retained tuple across later
non-FREE states and confers no durability. Source root captures and map freeze
check actual candidate ownership. Ordinary recovery prepare remains FREE-only.
Owned preparation requires the exact claim and uses the same serialization/
expected-hash preparation body, preserving its tuple. A decoded recovery
candidate clears builder provenance and cannot acquire a construction claim.
The local claim fixture controls ownership/refusal only, not actual cut or
physical construction. The composed claim invariant remains unqualified.


## Allocator freeze leaf qualification

At source `802da825c8e7b94e684294d20ea622a349b1b043`, the actual allocator
and `books/alloc-freeze.lisp` loaded under the record ACL2 executable with five
compatible cached dependencies. The nine target forms include seven literal
unchanged-stobj frames for begin-epoch, reserve, adopt, allocation commit,
retirement, cancellation and checkpoint drain while frozen. The source load
used 8.76 ACL2 seconds and 938,035 prover steps. This is source admission,
not a certificate-cache record, executed freeze control fixture, or checkpoint
composition proof. The prior `b6a907eeb` attempt refused allocator declaration
metadata before submitting the frame book; correcting the ownership rationale
strings preserved that ratchet.

The isolated actual allocator controls passed at `b911d26d4c66ae24fc760e87a65e22cd144bd20a`:
eight frozen lifecycle refusals preserve the observed state and epoch; a stale
owner generation refuses; actual physical pins can acquire and release with
ownership intact; removing the freeze permits reservation/cancellation and changes
the state. Both assertions executed in a six-form target load (8.85 ACL2 seconds,
938,035 prover steps including allocator/frame source). The phase-1 token is a
synthetic premise, so this tests the primitive gate rather than C-cut acquisition.
The first isolated attempt lacked its direct B* import and refused before these
assertions; adding the system dependency fixed the fixture without changing it.

The next installation connection is a bounded producer that packs the actual
completed construction ledger into the existing commit planner's allocation
record capacity. It must keep one member's workspace, batch and event until the
persisted installer consumes that exact member. A separate allocation per ticket
would violate the planner's reserved ticket count. Allocation installation does
not establish selectable checkpoint publication or authorize FREE.

## Shared linked page encoding

`checkpoint-linked-header.lisp` now owns the single linked BODY encoder used
by roles 2, 3 and 5. It derives the tag and terminal bit, checks the current
actual reservation, and copies a next Ref only from the same-role next ordinal's
completed verified extent with matching namespace. Terminal Ref fields and digest
are canonical zero. Producers supply their actual cut and calculated sequence
counts; this serialization helper cannot stamp coverage or source completion.
The map job now delegates to it, avoiding separate field-setter implementations.

## Retirement FIFO reconstruction

Allocation-map entries now carry `next-retired` (maximum entry width 56 bytes).
For RETIRE-PENDING rows the source copies the actual frozen FIFO successor;
other states serialize canonical NONE. The linked body header carries the
actual allocator retired head and total-retired count on role 2, and canonical
NONE/0 on other roles. No host or caller supplies the chain. Authenticated
restore must walk/mark this chain, require every target retired, nondecreasing
retirement commits, no cycles and exact coverage/count before rebuilding the
FIFO through the same allocator retire operation. This preserves real queue
order without an independent sort. Widths/page counts derive from new codecs.

C and B consumers now use the single B `fn2-checkpoint-production-roots-p`
body, moved unchanged from the construction state book. The scoped structural
rewrite preserves comments/strings and is idempotent; its two Python fixtures
run without evaluating ACL2 decisions. The descriptor budget fixture now checks
actual BEGIN/pack/bind zero-versus-positive control with explicitly synthetic
eligible root carriers; it does not witness actual cut/source construction or
replace the generated worker's IO budget assurance.

## Current integration boundary (2026-11-14)

The boot machine now reads checked descriptors and linked allocation-map pages,
retains every decoded row in a candidate-bound ledger, and validates the actual
retirement FIFO one link per step. It still refuses checkpoint startup before
selected-base evidence and ordered replay exist; map validity is not selection
or permission to mutate the live allocator. Encoded mixed-state intake controls
include stale candidate/ordinal, premature completion, cycles, decreasing
retirement commits and short chains. These ACL2 controls remain unexecuted.

Candidate preparation clears stale anchor mask, bank, installation commit and
previous identity while retaining the actual builder ownership. Verified boot
anchor intake establishes new anchor provenance independently. The shared run
writer now refuses an empty full leaf or index page with existing `:length`,
instead of allocating empty pages and retrying forever. Six focused source
controls cover the shared capacity arithmetic and writer refusal, including
arena-omission and empty-guard-removal mutations. They are not ACL2 admission.

The connected format closure at source `78f29b78317277159d60f9456e01afed347f2e6e`
passed source admission for `books/checkpoint-map-format`: 13 local books,
seven unchanged cached dependencies and five source parents, 15 target forms
through `FN2-CHECKPOINT-ARENA-PAGE-SLOT-FITS`. ACL2 reported 74.51 seconds and
10,709,063 steps for loading this closure. This admits linked map/arena packing
and its assertions under the changed geometry and retirement entry width;
it is not certification, encoder roundtrip, restored allocator or served reuse.
The detached outer PID26980 and server27006 were absent after explicit stop.
Logs and state are `/tmp/reclamation-format-union-78*` on Forge.

The remaining implementation work is the real C master/source actor, arena and
installation evidence intake, selected-base allocator reconstruction, ordered
allocation/retirement/release replay, and journaled writer exclusion. Anchor
previous-checkpoint descriptor identity must not be substituted for the immediate
predecessor seal. Dynamic foreground maintenance headroom also remains open:
the minimum profile admission bound does not reserve enough space against later
growth. Both upload and ordinary journal allocation must respect that policy,
while checkpoint maintenance consumes its already reserved tickets. FREE remains
disabled until this chain is implemented and qualified.
`checkpoint-metadata-resources.lisp` atomically tries the complete working
bundle only after the C cut is held. A refusal that acquired no bundle releases
that exact cut immediately; it never waits for pool room while holding C. Its two builders, twelve writers, cursor and
field stripe are distinct from the resident sealer, which may be frozen in
mid-build. The stable nonwriter windows remain owned through later root and
descriptor production. `checkpoint-metadata-driver.lisp` composes the actual
ordered selector, existing run assembler, authenticated semantic/payload
walkers and manifest scan. PAGE stops source mutation until the generated
physical worker returns the exact workspace. READ is a separate per-use,
one-descriptor operation; its actual retained operation tuple drives harvest.
Only the completed manifest/ledger scan sets the snapshot COMPLETE field.
These source declarations and boundary controls are not ACL2 admission,
runtime checkpoint qualification, recovery installation, or activation.
The root1 window-release operation consumes the actual same-candidate publisher
COMPLETE phase, retained builder claim, READY descriptor and positive installed
commit. It releases one still-owned window per turn through the existing pool
release operation. The publisher must return borrowed windows without releasing
them separately. Only the final successful release resets directory state for
another construction; uncertain writes and ownership failures retain resources.
Root1 read completion is delivered once by the core's exact prefinish harvest
extension to the semantic/payload lower job. The actor observer only wakes the
source continuation: its smaller ABI cannot reconstruct operation identity.
The public READ maps only the lower queued `:issued` result to the issue DSL's
`:ok`; all refusal and uncertain outcomes pass through unchanged.


The B lifecycle now consumes actual physical construction entries one per step,
retaining every constructed page and reserved journal ticket before changing
copy phase 1 to installation phase 2. It retains the six root edges separately.
After the actual installed member, it traverses the candidate's dedicated source
edges and atomically changes prepared protection to selectable protection. The
publisher start operation checks that actual lifecycle state. Thaw requires the
same candidate's completed bank publication and released writer bundle; it
changes only the physical freeze phase, retaining the C owner token for normal
snapshot release. It does not advance checkpoint coverage or permit FREE.
These source operations and their shape obligations remain unadmitted; the
master is connecting them and primitive controls are being prepared.
Root1 callbacks retain all required child inputs but return only each operation's
assigned and nested-callee result carriers. The largest result is STEP's code
plus 27 carriers (28 values); READ returns its three scalars plus 14 carriers
(17 values). The declaration drives body projection and positional shape
contracts together. A source control compares that declaration with actual
assignments and family calls, including a removed-manifest-result mutation.
This stays below ACL2's 32-value limit without treating readonly inputs as
outputs; it is a source check, not admission of the generated callbacks.
## Maintenance actor source integration

`checkpoint-master-kind` registers the actual singleton C maintenance owner,
shared page worker and bank writer before the assembly index is consumed.
Executor genesis creates the maintenance row and ordinary `fn2-turn` dispatch
runs it. Its source activation constant remains NIL: recovery selection,
ordered semantic/physical replay and combined maintenance headroom are still
qualification requirements. Registering these bodies does not enable FREE.

The maintenance owner closes and drains C before atomically trying the protected
27-window bundle. It then drives the existing metadata, authenticated event,
reservation closure, map/arena and descriptor callbacks. All producers bind once and use
one generated page worker's destination-derived HAND/ACCEPT and completion
handback. READ is a separate budgeted issue arm. The B lifecycle owns bounded
construction/source retention, the only copy-to-install transition and thaw;
B's actual journal owns allocation members and final installation. Publication
borrows its three dedicated future leases. C rearm and snapshot release follow actual
bank completion, source-window release and B thaw; uncertainty retains state.

The pressure source uses actual blocked retirement progress, cached complete
working-bundle room and the derived resident-directory budget as hints. The
held-cut admission rechecks permission. This does not guarantee physical
construction headroom or maintenance liveness. Source arity, dispatch and gate
controls are static checks; these actor books have not been admitted or run.

The subsequent 20-book map roundtrip probe at `60d49ddff` refused at
`FN2-CHECKPOINT-FROZEN-MAP-ENTRY-PRESERVES-TYPE`, before the packer/reader and
target assertions ran. The generated TYPE formula assumed only destination
shape and omitted the readonly allocator's domain. The repair preserves that
original formula in explicit malformed-logical-source controls, names the
replacement's actual guard domain, and retains the stronger valid WFP and
unconditional row effects. Operation bodies are unchanged. The controls and
replacement contracts are source obligations awaiting the revised narrow gate;
a failed proof search alone is not their counterexample evidence. The refused
probe used 108.16 seconds; recorded PIDs 121267/121292/121293 were absent after
cleanup, and its allocation was released.

Working-memory admission now reserves root19 plus future8 as actual leases in
one atomic per-class TRY at the exact held C cut. The future bundle contains
one maximum-sized staging window, four serialized journal windows, and three
anchor windows. The anchor writer waits for journal handback, borrows its exact
three leases and returns them after its covering fence. Central cleanup frees
future8 before root19 and reports the abstract bundle released only after all
27 are gone. Journal/staging consumer integration and the D0 bundle/loan
composition remain in progress; these source changes are not a liveness proof.
The pre-construction directory check runs only at the settled held C cut,
before descriptor BEGIN. Its resident commit budget is derived as one final
installation plus the ceiling of actual extent rows divided by the actual
allocation-record capacity per batch. This covers any physically feasible
construction's allocation records, but can conservatively refuse a smaller
snapshot near directory exhaustion; it is not physical free-space headroom.
The same hint in the pressure source prevents immediate abort/retry churn.
Startup's actual completed-fence layout binding is required before admission.

A refused pre-construction directory check releases the exact C snapshot token
first, then calls the sole shared working-release body over future8 and root19,
one actual owned lease per step. Its authority comes from the actual master
abort phase, FREE candidate, IDLE descriptor builder and untouched zero-token,
no-loan bundle. It cannot cancel allocations or release persistent edges, and
cannot authorize cleanup after descriptor BEGIN. Normal publication and this
abort share the physical release loop with separate permission guards.
These actor guards and controls remain source-only and unadmitted.


The resource order avoids stranding an existing STAGED transaction: the served
transaction can park after C staging when B cannot admit its journal workspace.
Capturing maintenance leases before closing C could exhaust the journal class
and then wait for that same transaction. The master now drains first without
holding working leases, and never parks on a pool wait while C is held.
Retirement debt is captured at HELD and marked seen only after successful
publication; a transient failed TRY therefore remains eligible when room returns.

The revised map roundtrip probe at `c524dc32e` source-admitted the repaired
readonly map-entry contracts, then refused the actual map packer's guard:
the encoder's field-capacity bound was not carried through the reader's
unchanged-row-count theorem. The 20-book attempt used eight cached parents
and eleven explicit source parents; total ACL2 loading cost was 94.91 seconds
and 12,973,186 prover steps. The failing guard itself used 0.06 seconds and
8,463 steps. Restore-reader loading and all target malformed-source and
roundtrip controls remained unrun. This clears the earlier source-reader
admission obstruction, not the end-to-end map recovery obligation.

A subsequent retained source session at `40de976fb`, with the proof-only
changes committed in `5e59fd022` and `0d1d55fcf`, admitted the actual map/arena
packers and restore reader. The unchanged roundtrip assertion then passed
after `94382fa6f` declared two unused reserve outputs: actual allocator
reserve/commit/retire state was packed and read back, with its original stale,
corruption and FIFO controls. The fixture runs ACL2 logical controls; it is
not a host crash/recovery or complete checkpoint-selection witness.

The missing-source-shape ground theorem still refused after 0.33 seconds and
90,203 prover steps; the corresponding missing-source-type theorem was not
sent. A proof refusal does not establish either malformed-source witness.
The restore book's 56.44-second, 13,236,134-step source admission also leaves
a proof-cost defect. The retained session was explicitly stopped and its
three recorded lifecycle PIDs were absent. No certificate, full recovery,
reclamation activation or FREE claim follows from these results.

The shared semantic-page decoder was source-admitted in the 24-book `e7c67652f`
closure with the proof-only row-frame hint committed in `d9959fe21`. This
covers the actual header/child-Ref predicates, header reader guards, carrier
frames, reader-context preservation, exact decoded-field/code observations,
and retained entry-count implication. The seven remaining contract forms
used 0.21 seconds and 17,516 prover steps after the source-parent load.
It does not authenticate a cold candidate by itself: the composing binder
must retain and check the authenticated descriptor and allocation-map
identity, including replacement of a descriptor in the same candidate slot.

The runtime publication child now retains two fence-owned bank occupants and
one displaced-candidate debt. Each identity includes the catalog row, checkpoint,
history, incarnation and all 32 bytes of the descriptor Ref's expected hash.
The existing BEGIN snapshots those hash words from the actual installed
candidate; only the matching successful covering Fence transfers that attempt
into its bank. Replacing an occupied bank first retains its complete old
identity as debt. Unrelated, failed and ambiguous completions preserve the old
occupants and attempted identity; no completion may overwrite existing debt.
Both lower publication BEGIN and actual writer rearm refuse outstanding debt.

This is the first candidate-lifetime connection, not candidate recycling.
There is deliberately no debt-clear operation. The next bounded post-C-release
teardown must exclude both banks, persist retirements of exact owned construction
allocations through the existing journal producer, remove only this candidate's
root/source edges, and preserve other candidates and read pins. Borrowed sources
are not retired by this operation. Cold boot must reconstruct both authenticated
bank occupants and retained installation evidence before teardown is authorized;
runtime fields do not establish cold authority. Bounded debt inspection/retirement scheduling now exists; terminal
catalog reuse remains unimplemented. Activation and FREE remain disabled.

The master now reaches a bounded displaced-candidate inspection after normal
C snapshot release. Each call checks one actual physical row under the retained
latest lifecycle/candidate owner, published descriptor identity and exact old
debt identity. An owned role0..5 construction may be eligible only with its exact
victim source edge, its counted exact six-root edges and no nonvictim durable
protector. Physical read/I/O pins remain untouched; role6 journal tickets,
borrowed sources and shared/archive-protected extents are not retirement input.
The candidate and B lifecycle provenance remain retained across this traversal.

The actual submit wrapper rechecks the full eligibility gate and calls the
existing ordinary retirement producer in the same ACL2 call. That producer
binds the actual containing batch and installs the allocator retirement intent
before txn admission. New durable protectors are refused during the asynchronous
wait and after persisted retirement; physical pins may still complete. Exact
accepted/refused settlement releases the staging lease, while uncertainty
retains it and the intent. The master tracks that one lease separately from the
already released working27 bundle, including the uncertain-acquisition path.

Only exact accepted batch/event settlement reaches the edge-drop arm. That arm
checks the same owner/debt, exact allocation and actual RETIRE_PENDING retirement
commit, then invokes the existing allocator edge-drop for the victim's source
edge alone. It preserves all six roots, borrowed/shared/archive references,
other candidates and transient pins. Submit, settlement consumption and edge
drop have explicit zero-budget no-effect branches. EOF retains debt and catalog
state: archive/ancestry reachability must be settled before root/source teardown
or catalog reuse. The source actor and primitive controls remain unadmitted;
activation and allocator FREE remain disabled.

Cold semantic closure uses an extent-indexed DFS stack, replacing the pending
FIFO. A GRAY page is an active ancestor, and encountering it again refuses a
cycle. Only a CLOSED page at the exact physical handle, hash, schema, run,
level, expected count and directory/source/filter interpretation can be reused.
A parent remains GRAY while its child or article payload is outstanding.
Its successor cursor becomes active only after that child closes. The single
64KiB lease is then reset, the exact parent is read again, and the existing
physical verifier and typed decoder reauthenticate its hash and header before
restoring the cursor and count. Directory entries visit their run and optional
filter separately; payload completion stays with the shared physical engine.
Constructor pages require RESERVED map rows; authenticated borrowed semantic
sources require ALLOCATED or RETIRE-PENDING through the common reach role.
Depth is bounded by the actual extent table, with one constant-work transition
per call and no chronology assumption. The source fixtures keep their explicit
synthetic authentication premise and are not evidence of a persisted boot.
The generated codec maximum supplies the charged bound for restart-based entry
decoding; it does not impose a new limit on stored entries or nesting depth.
