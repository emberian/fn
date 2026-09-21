# Captured bundles: fn and dtn7-rs, each way

Two files, and each is the exact octet string one implementation put on an
RFC 9174 session that the other accepted. Nothing here is constructed, and
nothing here is fn's own encoder checked against fn's own decoder — that
distinction is why the directory exists.

| File | Author | Octets | SHA-256 |
| --- | --- | --- | --- |
| `dtn7-rs-0.21.0-authored.bundle` | **dtn7-rs 0.21.0** | 132 | `3ba1d435188867c7f5b184cbb90dacacb73ec40865b60ece080af524583616df` |
| `fn-authored-accepted-by-dtn7-rs-0.21.0.bundle` | **fn** | 138 | `f6688bdea94aa138b4fd338ecb171b1486dbde0d439a2756cde9a067b29b11b7` |

## The run

`tests/bp-dtn7/run_fn_bp_interop.py`, hbox, 2026-09-21, under `swarm-build`,
worktree `/tank/fn/lanes/w11-bp-node` (lane `w11/bp-node`).

- fn image `build/fn-host-dtn`, the DTN-only build list
  (`host/native/build-dtn.lisp`), 272,527,376-octet core, built by
  `tools/build_native_host.sh` with `FN_ACL2=/tank/fn/acl2-8.7/saved_acl2`.
  Every book in its 60-book closure is certified in that tree; `books/bp-node`
  certified for the first time in `run-20260921T021131Z-1eb0`.
- dtn7-rs 0.21.0 at revision `4daf02d7ea927e9293753b2a5c4497457f6e5a40`,
  `/tank/fn/dtn7/repo`, `dtnd -n dtn7x -e incoming`.
- The harness's DTN time for that run: `843272138572` ms.

Both files were journalled by the fn image itself — `bp receive` writes the
inbound transfer's octets under `.wire` **before** the node decides anything,
and `bp send` writes the bundle it authored **before** it reaches a socket —
so neither is a re-derivation after the fact.

## What each one is

### `dtn7-rs-0.21.0-authored.bundle`

dtn7-rs authored it for `dtn://fn-b/incoming`, source `dtn://dtn7x/`. Primary
block: no CRC (type 0), flags 131076 (`no-fragment` 4 plus `report-delivery`
131072), lifetime 3600000 ms. Two extension blocks in this order:
previous-node (type 6, block number 3) and hop count (type 10, block number
2). Payload: `dtn7 -> fn, decoded as a bundle\n`, 32 octets.

fn accepted it: `BP accepted xfer=1 adu=32`, and the ADU equals the payload
`dtnsend` was given.

**These octets are inlined in `tests/acl2/bp-bundle-tests.lisp`** as
`*bpb-dtn7-0-21-0*`, where the certified codec asserts that it decodes them,
that the fields it recovers are the ones above, and that `fn-bpb-encode`
reproduces them byte for byte.

### `fn-authored-accepted-by-dtn7-rs-0.21.0.bundle`

fn authored it with `fn-bpn-send`: source `dtn://fn-b/`, destination
`dtn://dtn7x/incoming`, creation time 843272138572, sequence 1, lifetime
3600000 ms, CRC32C on every block, a hop-count block (limit 32, count 0) and
a bundle-age block, payload `fn -> dtn7, a bundle fn authored\n` (33 octets).
138 octets on the wire.

dtn7-rs decoded it and delivered the ADU to its `incoming` endpoint;
`dtnrecv -e incoming` printed the payload back.

## What is NOT claimed

Neither file is a conformance suite. One bundle each way with one peer at one
revision says that these two implementations agree on these octets; it says
nothing about fragmentation, BPSec, status reports, or any field neither side
exercised. The canonical-block CRC is still exercised only against fn's own
encoder in the outbound direction, because the bundle dtn7-rs authored
carries no CRC at all.
