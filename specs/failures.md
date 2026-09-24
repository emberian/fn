# Failure model and assumptions

Status: named assumptions for conditional proofs and qualification. Actual fn
host/process/fault tests now exercise portions of the boundary; they do not
qualify physical power-loss behavior or establish the assumptions universally.
See the [store refinement contract](store-refinement.md) and the
[BP exchange evidence](../tests/evidence/2026-09-18-bp-exchange.md).

## Named assumptions

| ID | Assumption and scope |
| --- | --- |
| A-DURABILITY | A completed platform barrier preserves the named bytes and necessary namespace updates across a modeled crash. |
| A-WRITE-ISOLATION | Later incomplete writes cannot damage previously durable committed storage outside the modeled write unit. The adapter/layout must establish that isolation. |
| A-HOST | The adapter preserves event identity/order contracts, reports outcomes honestly, and does not mutate logical data behind the core. |
| A-CRYPTO | Selected primitives meet the stated integrity/authentication assumptions for the deployment; no universal digest-injectivity axiom. |
| A-PEER | A peer whose retention undertaking is relied upon follows that undertaking within the declared node-failure model. |
| A-IDENTITY | Origin/incarnation allocation and restore procedures avoid unrecognized reuse, subject to their explicit freshness assumptions. |
| A-POLICY | The evaluated policy context is authorized and identified; accepting one signed statement does not establish arbitrary authority. |
| A-FAIRNESS | For liveness only: useful contacts, capacity, scheduling, retries, and permitted routes eventually occur as stated. |

## Crash-only storage model

FLR-001: permit a crash between any modeled write/barrier/publication actions.
Unsynced writes may be absent, torn, or reordered as allowed by the selected
device model. Completed durability barriers constrain what survives. Do not
assume an entire append is atomic or that unsynced data always survives as a prefix.

The write unit matters. Appending after a committed record in the same physical
sector may threaten that earlier record on some devices. The chosen alignment,
generation scheme, or platform guarantee must justify A-WRITE-ISOLATION. File
creation/renaming also has namespace durability requirements; a file flush alone
is not automatically a directory commit.

FLR-002: disk-full, known failure, and indeterminate completion are modeled
outcomes. A crash loses volatile session state and may lose receipt transmission
without losing the underlying committed obligation. A restarted node recovers
obligations, not just article bodies. Stale host completions are rejected.

## Beyond crash-only

FLR-003: separately model detectable media corruption, unavailable objects, and
whole-node loss. State precisely which copies/anchors must survive for recovery.
No single-node proof promises survival after all copies are destroyed. Hashes
do not establish hardware reliability; checksummed checkpoints do not establish
freshness against replacement of the whole store by an old valid snapshot.

Damaged committed history must cause an explicit fault/repair path. Normal
crash recovery and administrative salvage are different operations with different
claims. A salvage command must not silently report ordinary successful recovery.

FLR-004: tolerate delayed, duplicated, reordered, and replayed network inputs,
arbitrary contact gaps, and clock errors within explicit policy. Safety must not
require a synchronized global clock. Liveness claims name A-FAIRNESS and their
resource/route assumptions. Bundle or message expiry requires explicit clock/age
semantics; “timeout” does not prove remote non-acceptance.

## Required platform evidence

Before a durability claim, record OS/filesystem/device scope, write unit and
overwrite assumptions, barrier and namespace behavior, error handling, and the
fault tests performed. Simulated crash proofs and process-kill tests alone do not
establish actual power-failure behavior. D14 selects the first qualification
profile and the boundary between proved algorithm and trusted platform.

The [isolated hbox device-EIO observation](../planning/evidence/t16-private-eio-2026-09-23.md)
uses ext4 on a disposable tmpfs-backed loop device and a private `dm-flakey`
mapper. It exercises a failed transaction-directory `fsync` after the final
link. It is an error-handling profile only: it does not qualify hbox's ZFS,
physical power loss, write-cache behavior, completed-barrier survival, torn
writes, or A-DURABILITY/A-WRITE-ISOLATION for a deployed node.

The opt-in `tests/campaign/native_block_fault.py` successor profile uses only
new tmpfs backing files, positively identified loop devices, and a private
ext4 mapper on hbox.  It has four distinct cases: `frontier-dir-eio` stops at
the `fn-bs-frontier-program` pair-12 root replacement before its directory
barrier; `record-dir-eio` stops at `fn-bs-record-program` pair 10 before the
transaction-directory barrier and observes the pair-11 error; a
`record-dir-sigkill` case kills that stopped process without injecting I/O
failure; and `record-cut-snapshot` copies the private backing bytes while its
mapper is suspended, then reopens only that copied image to simulate loss of
volatile writes.  Each case checks prior durable transaction bytes, the
allowed old/new namespace outcome, and a fresh native recovery.  An EIO is a
failed syscall outcome, SIGKILL is process death, and the copied backing image
is an explicit simulated write-loss experiment.  None represents an actual
power cut or qualifies hbox's ZFS, hardware write cache, or a deployed node.
No automatic release of retained history follows from this profile.
