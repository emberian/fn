# Design summary: fn as a BPv7 node

Full design: [specs/bp-design.md](../../specs/bp-design.md). Branch
`w4/bp-design`, worktree `build/lanes/w4-bp-design`, from `9321344`. No
certification was run; every `defun`/`defthm` in the design is a commitment
for the packets below, not a claim.

## The judgment it answers

The current BP path is an application polling a co-located dtn7-rs over HTTP
on loopback (`tools/bpa_dtn7.py`: `/status/bundles`, `/download?BID`,
`/delete?BID`), an opaque BID, an upstream Rust decoder, and certified books
(`bp-primary`, `bp-fragment`, `clock`) with no caller. That is theater. The
design makes fn the node: the bundle protocol agent is fn's core, the bundle
store is fn's Store, the scheduler routes by contact plan, the receiver and
relay machines are delivery and forwarding, and fn owns its convergence
layer. dtn7-rs and ION become peers.

## Shape

1. **Node** (`books/bp-node.lisp`, `fn-bpn-*`): RFC 9171 §5.2–5.11 and
   §6.1.1 kept verbatim (table in the spec); deliberately dropped: forwarding
   back to the previous node, passive registrations and delivery abandonment,
   §5.12 cancel, lifetime overrides, custody. Bundle records are an FNBS
   record family in the one Store journal, keyed by `fn-bpp-bundle-id`,
   with retention constraints `:dispatch-pending`/`:forward-pending`/
   `:reassembly-pending` kept distinct from fn's obligations (the archive and
   `:forward` pins, released only by receipts). Status reports are typed
   statements that become transport observations and nothing more.
   Theorems T1–T6: no `:deliver` without a validated primary and a complete
   (reassembled) payload; an undelivered local bundle is deleted only by
   `fn-clock-expiry-decision = :expired` or `:block-unintelligible`, and
   discard refuses while an obligation is open; expiry only by the clock
   book; cut-then-reassemble is the identity (needs the two open
   `bp-fragment` lemmas); administrative records yield only `:transport`
   effects, which `fn-bp-observe-transport` cannot turn into a release.
2. **TCPCLv4** (`books/tcpcl.lisp`, `fn-tcl-*`): exact octet grammar with
   every length checked against fn's own MRUs before `take`; the §3.3
   session machine (contact header, SESS_INIT negotiation = min/and/peer's
   MRUs, segments, cumulative acks, refusals with Table 6 reasons,
   keepalive/idle timeout, SESS_TERM, MSG_REJECT). Theorems C1–C4:
   partition independence with an unconsumed carry (the shape of
   `fn-wire-drive-partition-independence`); a `:bundle-received` event
   implies START..END with cumulative ack equal to the data length; inbound
   outcomes are exactly complete/refused/failed and TCP close never
   completes; no interleaving, MRU bounds, ending refuses new transfers.
   Host: `host/native/tcpcl.lisp` on the w3-native-host `sb-bsd-sockets`
   surface; the final XFER_ACK is sent only after the FNBS record is
   barriered. Sessions are bound to the contact plan's configured peer, not
   the announced node ID. No TLS in wave 4 (`CAN_TLS = 0`), slot kept.
3. **Interop**: I1 fn–fn in two netns on hbox with netem and link cuts; I2
   dtn7-rs peer over its `tcp` CLA; I3 ION `tcpcli/tcpclo`; I4 fn relay with
   non-overlapping windows; I5 hbox–persvati. LTP (RFC 5326) later through
   ION; MTCP and UDPCL noted, not built.
4. **Security**: BPSec BIB/BCB as a profile slot (`fn-bps-verify` an
   `encapsulate`d constrained function; host HMAC under A-CRYPTO); policy
   table `:none` today; `fn-bpn-deliver-under-policy-requires-verified-targets`.

## Packets (owner; gate)

0 bundle frame `bp-bundle` (core; round trip, canonicality, block numbers)
→ 1 FNBS records and replay (core+host; crash cuts) → 2 fragment lemmas
(core) → 3 node machine T1–T6 (core) → 4 TCPCL books C1–C4 (core) → 5 native
host, lab I1, **delete** `bpa_dtn7.py`, `bpa_payload_extract.rs`, the FNBI
inbox, the dtn7 lab drivers, `test_bp_receive*.py` (host) → 6 transport
status set without the BPA-era statuses, scheduler opens/closes sessions
(sender-proofs+scheduler) → 7 labs I2–I5 (lab) → 8 BPSec (core+host) → 9 LTP
(core+w3-ltp-ion).

Books surviving unchanged: `bp-adu`, `bp-primary*`, `clock*`, `bp-receipt*`,
`bp-receiver-*`, `bp-release*`, `relay*`, `wire*`. Edited with
re-certification: `bp-fragment-invariants` (two lemmas), `bp-workflow*`,
`scheduler*`, `bp-ingress`, `frame`. Kept as peers: `tests/bp-dtn7/bootstrap.sh`,
`pin.json`.

## Not decided here

D01/D09 and the receipt authority; routing beyond the contact plan; any
flight claim; ION's actual TCPCL and RFC 9758 `ipn` behaviour (lab I3
measures them).
