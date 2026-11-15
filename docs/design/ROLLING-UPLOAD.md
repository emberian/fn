# Rolling upload completion

Decision owner: Sol allocation coordinator, 2026-11-15. This is an implementation
plan with named source milestones, not a claim that the rolling path is served.
The current two-4096-byte-window input still stops at 8159 bytes, even when the
configured article maximum is larger.

The implementation will hash and persist each bounded source window once,
with two explicitly allocated upload hash contexts: original SOURCE and stored
bytes (including an injected Message-ID). This avoids a temporary spool plus
prepublication readback and its additional I/O, fencing and cleanup protocol.
No context may be borrowed by guessing a currently unused numeric row. The
shared B format/B3/digest/field geometry must allocate both contexts and preserve
sealer, CTL, per-CNS streaming contexts and the final reserved jobs. The current
FETCH owner confirms that the shared penultimate block-check row retains no
state across callbacks; a writer may use that same atomic scratch only if it
copies every result to its owned page before returning. A short-block CV must
therefore copy the saved block hash rather than reread a shared digest row.

The header remains in a carrier sized from the existing 16384-byte protocol
header limit plus digest/overview scratch, independently of article size. A
body window has a retained absolute source range. Feed, hash and storage cursors
must refer to that same range while the window is busy. Reset is permitted only
after its actual Write and Fence complete, physical loans return, pending I/O is
zero and no query holds the workspace. The allocation reservation and exact
physical identity stay retained until journal settlement. Ambiguous issued I/O
must preserve the bytes, reservation and continuation for recovery. A phase or
caller boolean is not a substitute for the actual completion/loan predicates.

Source milestones are separate reviewable packets:

- `fe9f761ab`, `dfc12386f`: physical extent identities use sixteen units; a
  resource count is not a physical address stride. Manifest recovery and
  settlement consume the same physical identities. Their assertions are unrun.
- `0943d496f`: raw commitment capacity is three units/96 digest bytes; longer
  stored sources use manifests. This changes representation selection, not the
  supported article maximum or the still-limited input feed.
- `9a02f58d8`, `12c046652`, `c77acfec8`: retain LF counts before window reuse;
  the original shared counter and its existing theorem forms are unchanged.
  New machine/EOF composition remains unqualified.
- `34a679896`: save original SOURCE in the unused second half of the existing
  64-byte store-page digest area before B3 reuse. Manifest headers consume that
  saved identity. Stored bytes have a distinct digest in the first half. The
  actual-turn source control stops at the encoded manifest header; transaction
  offer/evidence/POST consumers still require their fixed-reference migration.

Outstanding connected work is the authoritative paired hash geometry, stable
transaction identity references, header/body cursor representation, actual
streaming Write/Fence/loan receipt and ambiguity states, feed backpressure and
reset, and a complete configured-size APPEND with small reusable windows.
The input bound must not be widened until those consumers are connected.
Changing payload allocation grouping from three to sixteen physical units is
an independent capacity correction; raw vectors and manifest root size remain
three units. Its actual 16th/17th-block control is owned by the allocation codec
peer. No ACL2, native or deployment qualification is claimed for these packets.
