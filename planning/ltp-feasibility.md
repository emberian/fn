# LTP feasibility against the modeled BP path

Packet C1-12 asked whether LTP is reachable for fn against a real second bundle
protocol agent, once the BP primary block is modeled. It is. A pinned ION-DTN
build carried an ACL2-projected fn request ADU over an LTP/UDP link and fn's own
receiver accepted it, with interruption and expiry cases behaving as the
[BP path spec](../specs/bp-path.md) requires. The
[evidence](../tests/evidence/2026-09-19-ltp-feasibility.md) and every
configuration file in [`tests/ltp/`](../tests/ltp/README.md) are the record.

This is feasibility. It does not begin C3-04, and it does not close `REP-006` or
`SCN-010/017`.

## The adapter route

An fn node submits an ADU to ION by opening a `BpSAP` on its own endpoint and
calling `bp_send()`. The shipped `bpsendfile` utility works and was used here,
but it is not the route for a durable sender: see LTP-B2 below. Receipt is
`bp_receive()` on the destination endpoint, followed immediately by fn's own
durable staging write — ION offers no alternative: see LTP-B1.

EIDs are `ipn:<node>.<service>`; this laboratory used `ipn:1.1` and `ipn:2.1`.
ION also registers the `dtn` scheme through `dtn2fw`/`dtn2adminep`, so fn's
`dtn://` application EIDs are representable, but `ipn` is what ION's utilities,
routing (`ipnfw`) and plan syntax (`a plan 2 ltp/2`) assume.

Restart constraints: ION state lives in a SysV shared-memory working area and an
SDR keyed by `wmKey`/`sdrName` per node, with `ION_NODE_LIST_DIR` mapping node
numbers to working directories. A node restarts through `ionadmin`/`ltpadmin`/
`bpadmin`; ION's bundled `killm` pattern-kills every ION process on the host and
must never be used on a shared machine. An endpoint declared `q` retains
undelivered bundles across an application restart; the bundle is lost to the
application the moment `bp_receive()` commits, not when the application is done
with it.

## Blockers, exactly

**LTP-B1 — no non-destructive receive.** `bp_receive()` deletes the delivery
queue element, zeroes `bundle.payload.content`, destroys the bundle and commits
the SDR transaction before returning. `bprecvfile` then writes `testfile<N>`
with no `fsync`, no rename into place, and a per-process counter that restarts
at 1. fn's `inventory`/`download`/`delete` contract in `tools/run_bp_receive.py`
therefore cannot be served by ION; `tests/ltp/fn_ltp_stage.c` serves it from an
app-level staging copy whose `delete` removes fn's own file. The window between
ION's commit and that staging `fsync` is irreducible through the public API. It
is covered at the fn layer by durable sender work, retry and receipt
idempotence. An adapter that called `bprecvfile` and treated its output as
staging would be unsafe; an adapter that acknowledged before its own `fsync`
would be lying about restart safety.

**LTP-B2 — no bundle identifier to the sender.** `bpsendfile` prints none;
`bp_send()` returns an in-process `SdrObject` address. fn's durable attempt
record has no observed transport handle to bind, which is why no receipt return
leg was attempted here. Closing this needs a C-API adapter that reads the
RFC 9171 bundle id (source EID, creation timestamp, sequence) out of the new
bundle object before it is destroyed, and a decision about what fn stores when
that read fails.

**LTP-B3 — EID mapping.** fn's configured `peer-eid` is an application identity
ACL2 binds inside the ADU; ION needs its own registered destination EID. The
first run failed outright until the mapping was made explicit. `fn_sender_lab`'s
`CONFIG` conflates the two because dtn7-rs is natively `dtn:`-scheme; an fn
adapter config must separate them.

## What ION owns, and where that stops

ION owns LTP session establishment, red-part segmentation, checkpoints,
reception reports, retransmission, bundle lifetime expiry and BP forwarding over
the contact/range plan. Its repair budget is finite — `maxTimeouts 5`,
`maxRepairRounds 8` per session — so an outage past that budget cancels the
session, and BPv7 has no custody transfer to recover it. Recovery is fn's job.
This is the concrete shape of the spec's rule that a transport ACK, status
report, deletion or expiry cannot perform an obligation release.

## Suggested next work

1. A C-API ION adapter closing LTP-B2, so a sender attempt binds a real bundle
   id and the receipt return leg can run.
2. Separate application-peer-EID from BP-destination-EID in the fn workflow
   config, rather than in a lab driver.
3. The interruption campaign C3-04 wants: outages past the LTP repair budget,
   backpressure, staging quota exhaustion, reordering and duplicates, under a
   non-trivial contact plan with real one-way light time via `owltsim`.

## What this is not

Not interoperability qualification and not a mission profile. One
implementation, one host, IPv4 loopback UDP, zero light time, no BPSec, no
authenticated peer, no author signature, no power-loss qualification. LTP
reliability is not fn application acceptance.
