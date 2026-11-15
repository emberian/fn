# Selected RELEASE completion — source decision, 2026-11-15

Owner: GPT-6, `/root/reclamation_assurance/sol_release_trace`.
Source base: `c62b3e0bd7e9e1e3e5ae0a419aa53b7581c456ac`.
This records the implementation contract; activation and physical FREE locks
remain unchanged until the actual generated path and crash cuts qualify.

The existing root4 frontier gains `inventory-count` and a full authenticated
`INVENTORY-` Ref. It always names a real linked inventory page, including a
canonical empty terminal page for zero entries. No sixth descriptor root is
introduced. Root3 event/archive semantics remain independent.

Inventory pages use kind `:merkle-node`, body tag `:release-inventory`, and the
existing linked-page codec and owned page writer. Construction role4 ordinal0
is the frontier root; inventory pages have construction ordinals1+, and local
linked-header ordinals0+. Exact count, next Ref, page order, padding and terminal
coverage are authenticated. Work and page allocation yield; no stored-data cap.

The actual E ledger records EMPTY/CLAIMED/PERSISTED/SETTLED separately from its
three-edge ownership bit. It captures release event, target identity/retirement
and the original journal namespace from the real producer/decoder. CLAIMED is
not persistence. PERSISTED comes only from the exact covering Fence/member.
SETTLED comes only after exact indexed logical FREE and ownership-ledger cleanup
in the same no-yield success branch. Ambiguous outcomes retain their identity.

Csnapshot BEGIN already calls allocator snapshot prepare, closing new RELEASE
submission before journal START/claim. Claims precede member exposure in the
same call; HELD drains proposed/published/installed. Frozen enumeration walks
actual E rows ascending, emits only PERSISTED obligations at or below C, refuses
CLAIMED at or below C, and leaves later batches alone. SETTLED is omitted by this
complete source enumeration; absence of a recovery row or changed physical
handle never supplies that proof. Settlement cannot change membership mid-cut.

Cold restore follows the authenticated root4 Ref through the existing physical
page reader. It binds the selected descriptor, physical namespace, common reach
generation and cuts; checks complete sorted entry coverage and exact map
identities; and restores only listed pending descriptor/J/self obligations.
A settled historical target is neither reheld nor freed again. Pending prefix
settlement finishes before chronological suffix replay; suffix RELEASE stage8
advances the original record offset only after exact settlement succeeds.

The current LIVE allocation identity index is authoritative. Settlement uses
prepare-free, bounded index steps, exact free-ready receipt and commit-free
under selected generation G. It never calls raw allocator FREE. Construction
ownership preflight precedes the index commit; infallible ledger clear and
E SETTLED stamp follow success without yielding. All protector vetoes remain.

Old descriptor/J/self claims survive enumeration and persistence. They may be
transferred only after the exact new inventory/allocator summary and covering
Fence substitute the source proof. Metadata ACK, census head and copied hashes
are not discharge. This transfer must precede old checkpoint root withdrawal,
so obligation-count zero cannot form a cycle with checkpoint disposal.

Required controls include complete positive producer/restore/replay, claimed
and ambiguous refusal, post-freeze late-claim refusal, duplicate/omitted/
truncated/foreign inventory, old settled target reuse, repeated recovery,
wrong owner/generation and same-length substituted source. Source checks are
not ACL2 qualification or a nonseeded productive-recovery witness.
