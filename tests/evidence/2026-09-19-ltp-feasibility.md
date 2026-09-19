# LTP feasibility with a real second BPA — 2026-09-19

A pinned [ION-DTN](https://github.com/nasa-jpl/ION-DTN) build carried an actual
fn request ADU across an LTP convergence layer, and fn's own receiver accepted
it. The [machine-readable record](2026-09-19-ltp-feasibility.json) holds the
revision, commands, parameters and digests; every configuration file is in
[`tests/ltp/`](../ltp/README.md) with its [pin](../ltp/pin.json).

ION was built from tag `ion-open-source-4.2.1-a.1`, commit
`4912bf82de7d03a9a11bf5d68614cc002f9ac911`, with `autoreconf -fi`,
`./configure --prefix=…`, `make -j8`, `make install` on Linux/gcc 14.2.0. Two
nodes `ipn:1` and `ipn:2` ran in separate working directories with distinct
shared-memory keys and SDRs, joined by one LTP span each way over UDP on IPv4
loopback with `ltpclock`, `ltpmeter`, `ltpdeliv`, `ltpcli` and `ltpclo`.
`bpsource`/`bpsink` confirmed BP-over-LTP before any fn code ran.

## What ran

The fn sender work is the same ACL2 path as the pinned TCP laboratory: an
article is published, work is enqueued, attempt intent is persisted, and ACL2
projects the 449-octet request ADU. That ADU crossed the LTP link, was durably
staged, and arrived byte-identical
(`781f7ff3…4016` both sides). `tools/run_bp_receive.py`'s
`receive_bpa_request` then accepted it: outcome `accepted`, one record, one
article, one pin, exact article bytes, receipt `f2cbfa70…ae3e`, and the staged
copy deleted only after the receipt decision was durable.

Interruption: with a 60,000-octet ADU in flight and a 600-second lifetime, the
receiving node's LTP/UDP datagrams were dropped for 20 seconds with one named
`iptables` rule. Nothing was staged while the link was cut. After the rule was
deleted, LTP resumed the session, repaired the lost red-part segments, and the
ADU arrived byte-identical to its source.

Expiry: a 4,096-octet ADU with a 20-second bundle lifetime was submitted into a
60-second outage. Forty-five seconds after the link returned, nothing had been
staged. The bundle's lifetime had elapsed and ION deleted it. The fn job and its
archive obligation are untouched by that transport event.

## What did not run, and why

No receipt was returned over BP. ION gives the sending application no bundle
identifier — `bpsendfile` prints none and `bp_send()` returns only an in-process
`SdrObject` address — so fn's durable attempt record has no observed transport
handle to bind. The return leg is blocked behind that seam rather than faked.

## The receive seam

**ION has no non-destructive receive.** `bp_receive()` deletes the endpoint's
delivery-queue element, zeroes `bundle.payload.content`, destroys the bundle and
commits the SDR transaction *before it returns*. Afterwards nothing redelivers
the ADU, and `bp_release_delivery(&dlv, 0)` only leaks the ZCO without making it
reachable through any endpoint API. `bprecvfile` compounds this: it writes
`testfile<N>` with no `fsync`, no rename into place, and a per-process counter
that restarts at 1, so a restarted receiver silently overwrites earlier files.
Neither is restart-safe in fn's sense.

`tests/ltp/fn_ltp_stage.c` is the app-level staging copy this forces: take
delivery, write the exact ADU to a temporary file, `fsync`, rename into the
staging directory under the RFC 9171 bundle id, `fsync` the directory, then
release. `IonStagingInbox` serves fn's `inventory`/`download`/`delete` from that
copy, so `delete` removes fn's own staged file, never an ION-retained bundle.
The window between `bp_receive()`'s commit and the staging `fsync` cannot be
closed with ION's public API; it is covered at the fn layer by durable sender
work, retry and receipt idempotence, not by the BPA.

## Delegated behavior and its limits

ION owns LTP session establishment, 1,200-octet red-part segmentation,
checkpoints, reception reports, retransmission, bundle lifetime expiry, and BP
forwarding over the contact/range plan. Its repair is budgeted: `maxTimeouts 5`
and `maxRepairRounds 8` per session. An outage longer than that budget cancels
the session, and BPv7 has no custody transfer to recover it, so recovery falls
back to fn's own durable retry. `sessionInactivityLimit` was 0 and one-way light
time was 0 in this profile.

## What this is not

Not interoperability qualification: one implementation, one host, one profile,
no cross-implementation vectors and no errata audit. Not a mission profile: IPv4
loopback UDP, zero light time, no contact plan, no asymmetry, no rate limiting.
No BPSec, no authenticated peer, no author signature; the A_POLICY premise is an
explicitly trusted local test input. No power-loss or physical-media
qualification. No relay topology, backpressure campaign or staging-quota
exhaustion. LTP reliability is not fn application acceptance, and none of these
results closes `REP-006` or `SCN-010/017`.
