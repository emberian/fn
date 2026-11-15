# CNS source-window packet

This source-only packet binds a selected published article to a retained CNS
job, verifies physical units and the complete stored-source digest, and keeps
whole-query allocator promises until transport handback. It is not an executed
FETCH or a certified closure. Actual CNS/CTL actor composition remains required.

The delivery base is `86f919a16`. The current pool, columns, core, machine
compiler, machine arms and pinned I/O leaf remain byte-identical to that base.
The accompanying receipt records the exact provider source and named blobs.

`cns-source-capture` copies all location commitments, original SOURCE and stored
SOURCE from the same live typed READ into an initialized 160-byte prefix. It
claims the root extent in the same callback before the READ may be released.
The existing item lease fits this prefix and two disjoint 4096-byte windows;
no new pool loan is introduced. The original workspace declaration is moved
unchanged to `cns-source-workspace`; the actor donor removes its old two forms.

`cns-source-raw` issues actual pinned reads and retains exact operation identity.
Its global prefinish hook routes only the matching ReadResult/cell/generation.
Unit verification and <=1024-byte stored-stream hashing are CNS actor phases.
`source-next` only appends <=1024 already verified/hashed bytes to CTL staging;
it rejects an old destination offset and does no hidden I/O or hashing. EOF
requires all selected bytes both copied and hashed, the actual stored-source
comparison and the current request/lease generations.

`cns-source-manifest` authenticates each full location unit before the existing
header/entry decoder. Header identity is original SOURCE, not stored SOURCE.
A bounded preflight claims every authenticated descendant before output begins.
READY replay only confirms existing exact claims; it cannot extend coverage.
The manifest/proof unit remains unchanged while data is read into the second
window. The shared cursor decoder tail is factored once in
`source-manifest-entry`, and the old cursor API calls that implementation.

The allocator region appends E*N rows after the existing checkpoint region,
where E is the actual configured extent count and N the CNS count. Each query
has one exact claim per extent; duplicate references reuse it, while another
identity in that slot refuses. After real SEND or cancellation handback,
RELEASING scans one owned row per actor step. RELEASED retains the tuple;
HANDOFF acknowledges transport before CNS releases its lease through its
existing operation and finally clears the job.

Format/hash geometry adds N rows before the five existing tail jobs. CTL rows
use the four-argument runtime selector; CNS stream hash rows are separate from
CTL frame hashes and ordinary block verification. The native donor must migrate
all actual CTL callers together and compare FC/B3 row geometry. The source actor
must match its job count to the actual CNS count.

The producer prerequisites are the existing `fe9f761ab`, `dfc12386f` and
`0943d496f` donors: physical stride16, three-write grouping and the shared raw
threshold12288. The source reader introduces no private threshold or data cap.

The Python controls and advisory arity/MV checks pass. The capture, hash
interleaving and retention ACL2 fixtures are authored but unexecuted; their
synthetic selected-READ or authenticated-CLAIM premises are stated in the tests.
The actual CNS/CTL adapters, transport cancellation review and composed 6144-byte
physical-reader fixture must be joined before any executable serving claim.
