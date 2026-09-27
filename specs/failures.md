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
| A-HOST | The adapter preserves event identity/order contracts, reports outcomes honestly, and does not mutate logical data behind the core. Constrained as `fn-assume-host-report` and `fn-assume-host-events` (`books/assumptions.lisp`); no theorem takes them as a hypothesis yet, so no row with events cites A-HOST (the citations were dropped, keystone audit 2026-09-27 G3-9). A row cites it again when a statement is over those functions. |
| A-HOST-EXCLUSIVE-READ | While a store is open under its lock no other writer changes the files a range read covers, so the concatenation of range reads equals one whole-file read (P3; `books/assumptions.lisp`). |
| A-CRYPTO-TRAILER | The tears the platform produces of a written frame are tears of the byte model, and none validates as a frame unless it is the exact write (`fn-assume-crash-tearp`, `fn-assume-crash-tear-never-validates-unless-exact`, `books/assumptions.lisp`). Qualification is statistical: a validating tear is a garbled region whose 32-octet trailer is the SHA-256 of its own prefix; the pessimistic figure is the collision bound, about 2^-128 per chosen pair (the record log, PRF-244). |
| A-CRYPTO | Selected primitives meet the stated integrity/authentication assumptions for the deployment; no universal digest-injectivity axiom. |
| A-CRYPTO-NATIVE | The served images' SHA-256 primitive (the EVP SHA-256 of the libcrypto the TLS pair pins: OpenSSL 3.0+ or LibreSSL 3+, `host/native/digest.lisp`) computes FIPS 180-4 SHA-256, so the raw `fn-sha256-stobj`, `fn-sha256-of-string` and `fn-sha256-of-prefixed-buffer` it installs answer what the ACL2 definitions (proved equal to `fn-sha256`: `fn-sha256-stobj-is-sha256`, `fn-sha256-of-prefixed-buffer-is-sha256`) answer. A trust-boundary entry (HST-004), not an ACL2 constraint: no theorem mentions the native code, and every theorem about `fn-digest`, `fn-frame-digest` and `fn-frame-digest-buffer` is about the ACL2 attachment. Qualified at every start (known answers, every length 0..300 and longer messages against the ACL2 references; a disagreement refuses the start) and per image by `tests/test_native_digest.py` (100,000 inputs, lengths 0..1 MiB, list, buffer and string forms). A non-octet element leaves the fast domain and runs the reference. HMAC-SHA256, HKDF-SHA256 and RFC 8315 Cancel-Lock run over the list model `fn-sha256` and are untouched. The collision figure for the frame trailers stays A-CRYPTO-TRAILER's: about 2^-128 per chosen pair (a birthday bound over 256-bit digests), not the 2^-256 second-preimage figure. |
| A-PEER | A peer whose retention undertaking is relied upon follows that undertaking within the declared node-failure model. |
| A-IDENTITY | Origin/incarnation allocation and restore procedures avoid unrecognized reuse, subject to their explicit freshness assumptions. |
| A-POLICY | The evaluated policy context is authorized and identified; accepting one signed statement does not establish arbitrary authority. |
| A-FAIRNESS | For liveness only: useful contacts, capacity, scheduling, retries, and permitted routes eventually occur as stated. |
| A-BP-CONTACT | For liveness only: a base contact to a peer sustains `(fn-assume-bp-contact-asks peer)` of the driver's asks with its gate open, every publication it proposes answered within its ask (`books/assumptions.lisp`; the base-job-offer reading of A-FAIRNESS and A-BP-PERSIST, spec bp-node-machine 4.9). |
| A-DURABLE-EXTENT | A durable file holds, at an extent the host durably wrote and never rewrites, the octets written there, and the host's extent realizer answers them: `fn-durable-octets`, `fn-durable-octet`, `fn-durable-realize-octet`, `fn-durable-realize-octets` (the whole payload in one read) (`books/assumptions.lisp`; the payload arena's extent handles, PRF-294; the commit's reseat after the log's barrier takes the faithful WRITE -- the file holds, at the entry's record position, the record the log wrote there -- as its hypothesis, PRF-309). A read that does not match the entry's recorded trailer is refused by name (`arena-extent-digest`), never served. |

### fn obligations stated as constrained functions

Not assumptions: properties fn proves of its own owner, stated as an
`encapsulate` in `books/assumptions.lisp` so that a theorem is proved once
over the obligation and each caller discharges it by functional
instantiation. No registry row cites them as assumptions.

| Obligation | Stated | Used by | Discharged by |
| --- | --- | --- | --- |
| `fn-assume-log-sole-pending-writer` | while the log recovers, no store operation but the segment's own writes is pending | `fn-lgk-recover-establishes-relation` (`books/store-log-recover.lisp`) | `fn-owb-recover-establishes-relation` (a related state, `books/owner-batch.lisp`, PRF-254). `fn-lgob-recovered-segment-fence-is-identity` (PRF-273) used it until 2026-09-27; its weakened statement needs only the segment's inode. |

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
