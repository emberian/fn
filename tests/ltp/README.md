# ION BP-over-LTP feasibility laboratory

This directory holds every configuration file, helper and driver used to run
fn's request ADU across an actual LTP convergence layer, using a pinned
[ION-DTN](https://github.com/nasa-jpl/ION-DTN) build as the second bundle
protocol agent. `pin.json` records the exact revision, tag, configure flags and
node parameters. It is a feasibility experiment on one Linux host, not
interoperability qualification and not a mission profile.

## What runs

Two ION nodes, `ipn:1` and `ipn:2`, in separate working directories with
distinct shared-memory keys and SDRs, joined by one LTP span in each direction
over UDP on IPv4 loopback (`udplsi`/`udplso` on 127.0.0.1:41113 and :42113).
BP uses `ltpcli`/`ltpclo` ducts and `ltpclock`/`ltpmeter` run the LTP sessions.

```sh
. tests/ltp/env.sh                      # ION_ROOT, PATH, LD_LIBRARY_PATH, ION_NODE_LIST_DIR
bash tests/ltp/start_node.sh $ION_ROOT/cfg/node1
bash tests/ltp/start_node.sh $ION_ROOT/cfg/node2
python3 tests/ltp/run_fn_ltp_lab.py --run $ION_ROOT/run/fnlab
bash tests/ltp/interrupt_expiry.sh $ION_ROOT/run/interrupt
bash tests/ltp/stop_node.sh $ION_ROOT/cfg/node2
bash tests/ltp/stop_node.sh $ION_ROOT/cfg/node1
```

ION ships a `killm` script that pattern-kills every ION process on the host.
`stop_node.sh` never calls it; it shuts down exactly the daemons that node
started, through `bpadmin .`, `ltpadmin .` and `ionadmin .`.

`interrupt_expiry.sh` cuts the link with one named `iptables` rule on the
receiving UDP port and deletes that rule by specification. It never flushes the
ruleset, because the build host is shared.

## Files

| File | Role |
| --- | --- |
| `pin.json` | Pinned ION revision, tag, configure flags, node parameters |
| `env.sh` | Shared environment; ION multi-node state lives in `$ION_NODE_LIST_DIR` |
| `node1/`, `node2/` | Complete `.ionconfig`/`.ionrc`/`.ionsecrc`/`.ltprc`/`.bprc`/`.ipnrc` sets |
| `start_node.sh`, `stop_node.sh` | Single-node start and graceful shutdown |
| `fn_ltp_stage.c` | ION receiver that writes a durable staged copy of one ADU |
| `ion_bpa.py` | `IonLtpSender` and `IonStagingInbox`, the adapter surfaces fn needs |
| `run_fn_ltp_lab.py` | fn sender work → LTP → staging → `tools/run_bp_receive.py` acceptance |
| `interrupt_expiry.sh` | Link cut mid-transfer, restoration, and a lifetime-expiry case |

## The receive seam, stated exactly

ION has no non-destructive receive. `bp_receive()` (bpv7/library/libbp.c) takes
the oldest element of the endpoint delivery queue, deletes that list element,
sets `bundle.payload.content = 0`, calls `bpDestroyBundle()` and commits the SDR
transaction *before it returns*. After it returns, the bundle is gone from the
endpoint and the payload ZCO survives only as a reference in the receiving
process. A crash between that commit and any durable application write loses the
ADU permanently: nothing redelivers it, and `bp_release_delivery(&dlv, 0)` only
leaks the ZCO in the SDR without making it findable again through any endpoint
API. There is no ION analogue of the pinned dtn7-rs inventory/download/delete
triple that `tools/run_bp_receive.py` is written against.

`bprecvfile` is worse than the raw API: it `write()`s the payload to
`testfile<N>` with no `fsync`, no rename into place, and `N` is a per-process
counter that restarts at 1, so a restarted receiver overwrites earlier files.

`fn_ltp_stage.c` is the app-level staging copy this forces. It takes delivery,
writes the exact ADU to a temporary file, `fsync`s it, renames it into the
staging directory under a name derived from the RFC 9171 bundle id
(source EID, creation timestamp milliseconds, creation sequence), `fsync`s that
directory, and only then releases the delivery. `IonStagingInbox` then serves
fn's `inventory`/`download`/`delete` from that staged copy, so `delete` removes
**fn's own staged file**, never an ION-retained bundle — ION destroyed its copy
inside `bp_receive()`. The residual window between that commit and the staging
`fsync` cannot be closed with ION's public API. It is covered at the fn layer by
durable sender work, retry and receipt idempotence, not by the BPA.

## The send seam, stated exactly

ION's `bpsendfile` prints no bundle identifier, and `bp_send()` returns only an
in-process `SdrObject` address for the new bundle. There is no transport handle
for fn's durable attempt record to bind. `IonLtpSender.submit()` therefore
returns a local `ion-unreported:<label>` name and records that as the seam. A
real adapter would have to read the bundle id out of that SDR object before the
bundle is destroyed, through the C API, not through any shipped utility.

fn's configured `peer-eid` (`dtn://fn.lab/inbox`) is an *application* identity
that ACL2 binds inside the request ADU. ION registers only the `ipn` scheme in
this laboratory, so the BP-layer destination must be `ipn:2.1`. An unmapped
first run failed with `bpsendfile: failed to send`. `IonLtpSender` carries the
mapping explicitly. ION does accept the `dtn` scheme (`a scheme dtn 'dtn2fw'
'dtn2adminep'` was registered and removed during this work), so the two strings
*can* be unified, but the conflation in the dtn7-rs lab was an accident of that
implementation being natively `dtn:`-scheme.

## What this is not

Not interoperability qualification: one implementation, one host, one profile,
no cross-implementation vectors, no errata audit. Not a mission profile: IPv4
loopback UDP with zero light time, no contact plan, no asymmetry, no rate
limiting, no BPSec, no authenticated peer, no author signature. Not a
power-loss qualification. Not a receipt-return demonstration: the return leg is
out of this packet's scope precisely because of the send-seam blocker above.
LTP reliability is not fn application acceptance.
