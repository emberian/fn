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

## 2. Evidence, and the three measured traps

Nothing in this handoff is a claim that a theorem was proved unless §4 names
the run that proved it. What §4 does record is three failures that cost this
lane most of its budget, each of which the next lane would otherwise repeat.

**An `ld` probe that passes can still exhaust the control stack under
`certify-book`.** `fn-bpb-decode` written as one nested `let*` admitted and
proved under `ld` on hbox in 11 minutes, then died in `certify-book` with an
`IF-COMPILE` backtrace and no error message
(`build/acl2/certify-20260920T193841Z-1121774`). ACL2 inlines every branch
into one guard conjecture and its size is the whole cause. The cure is three
functions, not a hint.

**A guard obligation that looks arithmetic is usually a missing rule.**
`take`'s non-negative count — that the scan's remainder is no longer than what
it scanned — is a corollary of `fn-bpc-dec-reencodes-consumed-prefix` plus
`fn-bpc-len-of-append`. Left to induct over `fn-bpc-dec`, the prover hits the
induction-depth limit.

**A closed callee needs its fact as a rule before the fold over it.**
`fn-bpb-decode-blocks-yield-blocks` inducts over the fold with
`fn-bpb-decode-block` closed; with the one-block fact still in the invariants
book above it, the induction had nothing to apply and the run was killed at
the 2400 s cap (`build/acl2/certify-20260920T195958Z-1136779`). The one-block
fact moved down into `books/bp-bundle`.

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

**`books/bp-bundle` CERTIFIES.** hbox, ACL2 8.7 under `swarm-build`,
evidence `build/acl2/certify-20260920T204124Z-1174239`, **3.06 s**
(`book_wall_seconds`), 5.91 prover seconds over the whole book. The 11- and
30-minute runs before it were the prover flailing on the two forms of §2,
not the book's cost.

**`books/bp-bundle-invariants` is OPEN at one form**, and the form is named:
`fn-bpb-decode-blocks-of-encode-blocks`, the round trip of the fold over the
block sequence. Everything before it proves, including the keystone it rests
on: `fn-bpb-decode-block-of-encode-block` closed in the run
`build/acl2/certify-20260920T210105Z-1191520`, which then hit the 1200 s cap
with the fold still open (the log reaches
`fn-bpb-block-listp-of-append`, the form immediately before it). What closing
it wants, in the order to try: `tools/proof_profile.py` on that form first,
because the induction is over `fn-bpb-decode-blocks` with
`fn-bpb-decode-block` closed and the one-block keystone is already a rule, so
the cost is in what the induction hypothesis carries rather than in a missing
fact.

Because that book is open, **the four books above it did not certify**:
`tests/acl2/bp-bundle-tests`, `books/bp-node` and `tests/acl2/bp-node-tests`
fail at `(include-book "bp-bundle-invariants")`
(`build/acl2/certify-20260920T204435Z-1177466`). Their content is on disk and
their statements are unchanged; none of it is claimed proved.

**Not run, for the same reason**: the DTN image
(`host/native/build-dtn.lisp` now includes `books/bp-node`, which needs that
certificate), so `tools/tcpcl_lab.py --scenario adu` and
`tests/bp-dtn7/run_fn_bp_interop.py` have not executed. **No claim about the
`bp` verb, the lab scenario or dtn7 interoperability follows from this
lane.** The commands are:

```sh
ssh hbox 'cd /tank/fn/lanes/w9-dtn-2 && FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
  FN_CERT_CACHE=/tank/fn/certcache FN_ACL2_TIMEOUT_SECONDS=2400 \
  swarm-build python3 tools/certify_books.py --jobs 2 \
  books/bp-bundle-invariants tests/acl2/bp-bundle-tests \
  books/bp-node tests/acl2/bp-node-tests'
ssh hbox 'cd /tank/fn/lanes/w9-dtn-2 && FN_NATIVE_BUILD=host/native/build-dtn.lisp \
  FN_NATIVE_IMAGE=build/fn-host-dtn FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
  swarm-build sh tools/build_native_host.sh \
  && swarm-build python3 tools/tcpcl_lab.py --image build/fn-host-dtn \
       --work build/bp-lab --scenario adu \
  && swarm-build python3 tests/bp-dtn7/run_fn_bp_interop.py \
       --image build/fn-host-dtn --dtn7-repo /tank/fn/dtn7/repo --work build/bp-interop'
```

`make check` is green on this tree (scaffold OK, ledger OK, 220 lint
warnings, down one because `nthcdr` joined `tools/acl2-builtins.txt`).
`python3 tools/ledger.py --write` has been run.

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
