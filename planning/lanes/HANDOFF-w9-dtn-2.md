# Handoff: w9/dtn-2 — fn encodes and decodes BPv7 bundles, and originates them

Branch `w9/dtn-2`, worktree `build/lanes/w9-dtn-2`, from `dev` at `34f5a95`.
Box: hbox, `/tank/fn/lanes/w9-dtn-2`, ACL2 `/tank/fn/acl2-8.7/saved_acl2`,
cache `/tank/fn/certcache`. No ACL2 ran on the laptop.

This lane answers the question
[HANDOFF-w9-dtn-e2e](HANDOFF-w9-dtn-e2e.md) §2 left open: "nothing in this
tree encodes or decodes a BPv7 bundle, only its primary block", and "the one
thing not to do is add a `bp send` verb that wraps `tcpcl send`".

## 1. What landed

**`books/bp-bundle.lisp`** — RFC 9171 §4.3, the bundle around the primary
block. The canonical block of §4.3.2 as an `fn-defrecord` (type code, block
number, processing control flags, CRC type, block-type-specific data); the
§4.2.2 CRC computed over the block's own zero-filled encoding, reusing
`fn-bpp-crc16`/`fn-bpp-crc32c` (a CRC is a checksum, not a digest: it is
computed in the logic and there is no seam); the payload block of §4.3.3; the
indefinite-length bundle array; the three §4.4 extension blocks as canonical
blocks over `books/bp-primary`'s block-type-specific data.

**The primary block inside a bundle is `fn-bpp-decode`'s, not a second
decoder's.** `fn-bpc-dec` locates the end of the primary block's CBOR item;
the octets up to there are handed to `fn-bpp-decode` unchanged. So
`fn-bpp-decode-of-encode`, `fn-bpp-accepted-input-is-canonical-by-construction`
and `fn-bpp-accepted-block-has-valid-crc` are about the function this book
calls, and there is no twin to keep in step.

**`books/bp-node.lisp`** — `fn-bpn-send` (an ADU plus this node's
configuration become a whole bundle: this node's ID as the source, the clock
observation as the creation timestamp, the configured lifetime, a hop count
block and a bundle age block), `fn-bpn-receive` (a peer's octets become an
accepted bundle, a refusal or an uncertain outcome), and the two §5.4
forwarding questions — lifetime expiry through `fn-clock-expiry-decision`,
hop count through §4.4.3. It is **not** the processing machine of
`specs/bp-design.md` §1.5; §1.5.1 of that spec now says exactly what is
missing.

**The image.** `host/bp-node-host.lisp` is the ACL2 bridge: endpoint IDs, the
configuration, the clock observation, the bundle octets, the receive outcome
and the ADU are computed there, so `host/native/bp.lisp` computes no protocol
value. `host/native/tcpcl.lisp` gains one hook, `*fnn-tcl-deliver*`, bound by
the `bp` verb so that a completed inbound transfer becomes a decoded bundle
instead of a spool file — inside the barrier that already holds the XFER_ACK
until the record under it is durable. Verbs: `bp send`, `bp receive`,
`bp decode`.

**`tools/tcpcl_lab.py` gains the `adu` scenario**, which is what makes the
distinction testable: neither side is handed bundle octets, only an ADU, and
the assertions are that the ADU journalled at the far end is the ADU given at
the near end, both ways, and that the bundle on the wire is strictly larger
than the ADU inside it. A `bp send` that wrapped `tcpcl send` fails at the
first assertion.

**`tests/bp-dtn7/run_fn_bp_interop.py`** — the interoperability harness with
fn-authored bundles: dtn7 authors and fn decodes in leg 1, fn authors and
dtn7 decodes and delivers in leg 2.

## 2. Evidence

See §4 below for what ran and what did not. Nothing in this handoff is a
claim that a theorem was proved unless §4 names the run that proved it.

## 3. The three outcomes, at every boundary

`fn-bpn-receive` returns `(:accepted bundle)`, `(:refused reason)` or
`(:uncertain bundle reason)`; `fn-bpn-host-receive` returns them flat;
`fnn-bp-deliver` writes `.adu`, `.refused` or `.uncertain` records; and
`fnn-bp-exit-code` returns 0, 1 or 3. The interesting case is the one the
lab exercises: a node with no wall clock receiving a bundle whose creation
timestamp is the zero of §4.2.6 decides its lifetime from the Bundle Age
block, and a bundle with neither is **uncertain** — not refused, and not
accepted.

## 4. What ran, and what is open

Filled in by the lane's final report; see `planning/deputies/BOARD.md` for
the CHANGE entries.

## 5. What the next lane should take

1. The FNBS record family and the `(:bpn-sequence n)` durable frontier
   (`specs/bp-design.md` §1.3). Until it exists, a restarted `bp send` can
   reuse a (source, creation time, sequence) triple, and `host/native/bp.lisp`
   says so in its own header rather than hiding it.
2. `fn-bpn-step` and the state of §1.5, so that T1 to T6 of §1.6 have a
   subject. They are unproved today and nothing claims them.
3. Joining the accepted ADU to `books/bp-receipt`'s receiver path: today the
   host journals the ADU and stops.
4. The outbound-suffix obligation of `specs/tcpcl.md` §6, untouched by this
   lane.
