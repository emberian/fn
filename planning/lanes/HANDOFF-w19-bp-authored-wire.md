# W19 immutable authored-wire publication handoff

Functional source: `a9c07b487b118308832545565444e8ff31a697bf`.

`bp send` no longer writes `authored-N.wire` through a raw staged rename.  The
durable FNBS reservation token now enters
`fn-bpn-authored-wire-authorize`, which derives the compatible
`authored-N.wire` name with the existing byte-store decimal renderer, authors
the bundle with `fn-bpn-send`, and returns the exact name, wire, operation
label and `fn-jpub` initial state the host must consume.  The native caller
checks that the exact ACL2 preview was absent while it holds `.spool.lock`,
checks the returned echo, and executes the shared
`fnn-immutable-publish-effect`.  It never substitutes a host-formatted name or
host-authored wire value.

An authored wire is immutable evidence for one durable creation-sequence
reservation.  `bp send` has no same-name retransmit operation: a later
operator retry takes another durable reservation and therefore another name.
If the exact next name already exists, equal bytes and different bytes are
both conflicting recovery evidence.  The command returns uncertain, leaves
the existing file untouched, and a restart advances to the next sequence.
It never replaces the name or treats visible equal bytes as proof that this
operation became durable.

The shared publication outcomes retain their existing boundaries.  A staged
file or file-barrier failure before link begins is refused.  Once the link
attempt begins, a link error or final-directory barrier error is uncertain;
the caller does not inspect the final bytes to change that answer.  A
successful final-directory barrier is durable, and post-authority stage
cleanup remains best effort.  The durable FNBS sequence reservation precedes
this operation, so refused, uncertain and collision exits all burn that
sequence.  Recovery therefore cannot reuse its wire identity.

`fn-bpn-authored-wire-authorize-carries-reservation` is a correspondence
projection for the called operation: under valid configuration, endpoint,
ADU, observation and reservation, plus the trusted lock-held and exact-name-
absent observations, it returns the reservation sequence, the name derived
from that reservation, and exactly `fn-bpn-send`'s wire.  It is not promoted
as a registry keystone.  Its test book supplies reachable sequence/name/wire
witnesses and `must-fail` teeth for lock ownership, final absence and the
reservation-token premise.  The existing sequence-fidelity proof remains the
owner of cross-operation nonreuse; this packet consumes its actual reservation
token rather than creating another allocator.

## Evidence

The recovered persvati manifest
`certify-20260921T112508Z-3251134.json` records a passed 129-of-129 source
closure in 1003.158 seconds with 16 slots and ACL2 8.7.  Its recorded digests
match the functional source, including `books/bp-authored-wire.lisp`; the
manifest has no test-book root because the submitted command requested the
authored-wire book with closure.  The branch test book had certified earlier
while developing the packet, but no recovered exact manifest supports a new
standalone claim for it.  The recovered manifest's `git_revision` is null, so
source identity comes from its per-file digests.  The executable was
`/home/ember/fn-tools/acl2-8.7/saved_acl2`, SHA-256
`c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163`.

No native build or runtime command was recovered for this source.  The Python
scenario is therefore an executable test specification, not current evidence
that collision, restart, or publication-failure branches passed in an image.

The native evidence is DTN-profile evidence.  It does not claim the default
deployment image, a successful TCPCL peer exchange, filesystem or hardware
persistence, or protection against hostile raw Lisp forging the trusted lock
and absence observations.  The failed-connect runs deliberately stop after
durable wire publication so the publication outcomes are isolated from peer
behavior.
