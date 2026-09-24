# M4 application receipt through dtn7-rs: transport once, the application refuses a relayed request

Lane `m4-app-receipt`, 2026-09-24 21:00Z to 21:50Z, on hbox. The source is
branch `lane/m4-app-receipt` at `39eb05fb` (dev `00d291d0` plus this
lane's commit). Everything ran under `/tank/fn/scratch/m4-app-receipt/`.
Reports, fn logs, runners and the mock-lab diagnosis are in
[`m4-app-receipt-2026-09-24/`](m4-app-receipt-2026-09-24/), with a
`SHA256SUMS` that verifies. dtn7-rs is the pinned 0.21.0 checkout
`/tank/fn/dtn7/repo` at `4daf02d7ea927e9293753b2a5c4497457f6e5a40`.

## Result in one paragraph

Through a real BPA, an fn request is delivered **once** to fn B's
`bp-node serve` (one kind-5 custody, `BP accepted`), and B's application
decides **once**: `request-refused`. No receipt is authored, none reaches
A, and A's forwarding obligation stays `outstanding pinned=yes`. The
three outcomes stay distinct at every step: step 1 is `uncertain`, step 2 is
`accepted` by the CL, and step 3 is custody `accepted` with the
application `refused`. The refusal comes from the machine, not from the
host. ACL2 trusts a request only when its bundle source EID is the enrolled
EID of the TCPCL neighbour that carried it. So a request relayed by any BPA
is refused, whichever EID B enrols. The identical lab with A as B's direct
TCPCL peer (the control) goes all the way through: `request-accepted`,
receipt queued, `receipt-accepted` at A, `pinned=no`.

Two host defects had kept dtn7-rs from ever reaching B's application. This
lane fixes both (`39eb05fb`).

## Host changes (commit `39eb05fb`)

1. **`bp-node serve` demanded the application peer as the TCPCL neighbour.**
   - `host/native/bp-node.lisp:506-517`: the listener passed PEER-ID, the
     configured return EID for receipts, as the TCPCL expected peer.
   - ACL2's session machine then refuses any other SESS_INIT node ID
     (`books/tcpcl-session.lisp:518-519`). dtn7-rs announces
     `dtn://dtn7-r1/`, so B sent SESS_TERM plus MSG_REJECT (first run,
     `lab-r1/b-serve.log`).
   - The neighbour decision already belongs to ACL2:
     `fn-bpaj-session-principal` (`books/bp-session-admission.lisp:62-83`)
     decides from the announced EID and the observed channel, called
     through `fnn-bp-deliver-node`.
   - `bp-service` (`bp-service.lisp:414`) and `bp receive -`
     (`bp.lisp:552`) already pass no expected peer. The listener now does
     the same.
   - The active `fnn-bpnode-forward-contact` (`bp-node.lisp:225`) still
     expects PEER-ID. See finding 3.
2. **A peer that closes after its SESS_TERM killed the node.**
   - dtn7-rs closes its socket straight after sending SESS_TERM.
   - B's SESS_TERM reply then failed with EPIPE, raised from
     `fnn-tcl-flush` as an OS error, and ended `bp-node serve` with
     **exit 4** (`store: [Errno 32] Broken pipe`, `lab-r1b/b-serve.log`).
   - This happened after durable kind-5 custody and before the
     application dispatch.
   - Fix: `fnn-tcl-flush` (`host/native/tcpcl.lisp:221-237`) catches an
     OS or socket error on the session's own socket and marks the
     connection broken. `fnn-tcl-session` (`:415-416`) then hands the
     machine `fn-tcl-host-tcp-closed`, and ACL2 decides what the closure
     means for each transfer. Journal I/O is not inside that handler.
   - The session now ends with `TCPCL bp-node event peer gone before
     send: [Errno 32] Broken pipe`, `summary accepted=1`, and the node
     continues to dispatch.

The lab is `tests/bp-dtn7/run_fn_dtn7_app_receipt.py`. `run_four_node_lab.py --dtn7-repo`
now runs it with two relays; it no longer raises `NotImplementedError` at
the old line 462.

## Images (unfrozen scratch, from `git archive` of the lane tree)

Built with `build-images.sh` (the dtn-node-image recipe: `proof_artifacts.py acquire`/`validate`
for `dtn` and `default` against `/tank/fn/certcache` with w28 ACL2, then
`swarm-build sh tools/build_native_host.sh`). No book changed; every
certificate came from the cache. The build logs have no `undefined` line.

| image | launcher SHA-256 | core SHA-256 |
| --- | --- | --- |
| `fn-host-dtn` | `14134daa777754f5…` | `28dc0fcc829aebfe…` |
| `fn-host-dtn-developer` | `6c2cb94c886869f1…` | `face0c5204077184…` |

The full hashes are in `final.log`. Launchers point at `/tank/fn/sbcl`, and the runtime
needs `LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib`.

## Commands

From `/tank/fn/scratch/m4-app-receipt/tree`, with `FN_ACL2`, `FN_OPENSSL_PREFIX` and
`LD_LIBRARY_PATH` set as in [`final.sh`](m4-app-receipt-2026-09-24/final.sh):

```sh
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image build/fn-host-dtn-developer --relays 0 --work $R/control
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image build/fn-host-dtn-developer --relays 1 --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-neighbour
python3 tests/bp-dtn7/run_fn_dtn7_app_receipt.py --image build/fn-host-dtn-developer --relays 1 --b-trusts source --dtn7-repo /tank/fn/dtn7/repo --work $R/dtn7-source
python3 tests/bp-dtn7/run_four_node_lab.py --run-base $R/four-dtn7 --revision lane-m4-app-receipt --dtn7-repo /tank/fn/dtn7/repo --image build/fn-host-dtn-developer
python3 tests/bp-dtn7/run_four_node_lab.py --run-base $R/four-mock --revision lane-m4-app-receipt
```

**What the lab does:**
- **Setup:**
  - A's Store holds the article, and A's FNWF has it enqueued and
    undertaken (`bp-obligation undertake`, `pinned=yes`).
  - Each side enrols one BP boundary on its listener.
  - B also enrols the inbound scope `fn.test 32768 16`.
- **Request authoring:** the request ADU (6314 octets, `fd1a3bd9c33af270`)
  is ACL2's `fn-bpa-make-request`, evaluated by the certified books
  through the lab's ACL2 bridge, as in `tests/test_bp_node_native.py`.
- **Step 1:** `bp-service run` offers the request through a byte relay.
  The relay forwards 600 bytes of A's transfer (contact header,
  SESS_INIT and part of the segment) and holds the rest. The lab then
  SIGKILLs the first hop by PID.
- **Step 2:** the first hop restarts (dtn7: same sled store, same CLA port)
  and `bp-service resume` re-offers A's durable job.
- **Step 3:** B's `bp-node serve` admits, takes custody and dispatches.
- **Step 4:** `bp-contact tick` on B's FNBS forwards any owed receipt.
  A's `bp-node serve` listens for 40 s, and `bp-obligation status` reads
  A's obligation.

## Per-step table (final run, `fn-host-dtn-developer`)

The log SHA-256 values are 16-hex prefixes of the files in the record
directory. "custody" means `BP accepted` lines (one each).

| step | control (A to B direct) | dtn7, B trusts neighbour `dtn://dtn7-r1/` | dtn7, B trusts source `dtn://sender/` | four-node: A, dtn7-r1, dtn7-r2, B |
| --- | --- | --- | --- | --- |
| 1 held mid-transfer, first hop SIGKILLed | **uncertain**: `TCPCL uncertain outbound-failed`, `BP forwarding retained reason=uncertain` (`206f7afb3b4b0677`) | **uncertain** (`9c1a668c253762d8`), dtnd PID 1960011 SIGKILL | **uncertain** (`9c1a668c253762d8`), PID 1961129 SIGKILL | **uncertain** (`9c1a668c253762d8`), relay-a PID 1963257 SIGKILL |
| 2 restart, `bp-service resume` | **accepted** `status=forwarded` (`dbe021246b4eef5e`) | **accepted** (`b035921c4b05815a`) | **accepted** (`4670fc9460603a8b`) | **accepted** (`ada9957e296ca6ca`), relay-b window opens after this |
| 3 B custody | 1, admitted (`73284a6ebdbc31ab`) | 1, admitted (`011a99cf446914e8`) | 1, `admission refused reason=eid-mismatch`, custody with no principal (`156e153ed354072a`) | 1, admitted (`50cc99c79f7d088b`) |
| 3 B application | **request-accepted**, `receipt queued id=receipt:work-bp-node` | **request-refused** | **request-refused** | **request-refused** |
| 4 receipt at A | **receipt-accepted** (`250616318707b9ba`); tick `88d7f010f7e423ee` | **no-receipt** (`e3cf36d4c589be5c`) | **no-receipt** (`fdde50f7c644460b`) | **no-receipt** (`13bd03c695013518`) |
| A obligation after | `receipted pinned=no` | `outstanding pinned=yes` | `outstanding pinned=yes` | `outstanding pinned=yes` |
| report | `30eeb48fb26cecbf` | `e739a50b341caf04` | `e9844c1af9ea0308` | inner `577fc788cd2e8726`, evidence `32f25206ad04e565` (status passed, 5/5 assertions) |

In the four-node run, relay-a's epidemic routing also handed A's own
request back to A when A's listener came up (`BP accepted xfer=1 adu=6314`,
`BP received carrier dispatch durable`). A holds it as transit for
`dtn://receiver/`. This is an observation, not a failure: fn keeps
custody, and B's duplicate handling is not exercised by this run.

## Native modules on the final images (`run.sh`, one module at a time)

| module | tests | result | s | log SHA-256 (16) |
| --- | --- | --- | --- | --- |
| test_bp_node_native | 17 | OK | 341.8 | `f9dd875abbe73323` |
| test_bp_service_native | 16 | OK | 14.1 | `c8a5a9dee253ddcf` |
| test_bp_contact_relay_native | 1 | OK | 2.5 | `19aee3bf4daa1b4e` |
| test_bp_contact_native | 2 | OK | 0.5 | `8a122f0f54a214fa` |
| test_bp_receive_integrity_native | 4 | OK | 0.9 | `ccfc94377ca31675` |

`tcpcl.lisp` is also in the default image, which this lane did not rebuild
or run. `make check` passes on the lane tree; `planning/ledger.json` was
regenerated, with only line-number shifts.

## Findings

1. **The machine refuses every relayed request and receipt.** This is ACL2,
   and it is reported, not changed.
   - `fn-bpah-request-trustedp` (`books/bp-app-handoff.lisp:104-114`) and
     `fn-bpah-receipt-trustedp` (`:116-136`) require
     `fn-bpaj-current-peer-eidp cfg principal generation source`
     (`books/bp-session-admission.lisp:106-113`). The principal is the
     boundary chosen by the channel, and it must have exactly one
     `transport-bp` row equal to the bundle's **source** EID.
   - Session admission (`:62-83`) requires the same unique row to equal
     the **announced neighbour** EID.
   - Through a relay these are two different EIDs, so no configuration
     passes both checks. The two dtn7 columns above show each choice
     failing.
   - Smallest ACL2-visible change: give a boundary a finite, enrolled
     set of originator EIDs that it may carry. Today that is the single
     literal `bp-boundary-originators all-co-resident`. The trust
     predicates would then check that `source` is an enrolled originator
     of the admitted principal, instead of requiring it to equal that
     principal's transport EID.
   - This is a transitive-trust decision (D01/D09, authenticated
     identity) for ember, with its own teeth. It is not host plumbing.
2. **No native verb authors the request from A's workflow.**
   - ACL2 has `fn-bpo-request-adu` (`books/bp-outbound.lisp:69`). Its only
     native caller is the ION helper path
     (`host/native/workflow.lisp:384`, via
     `fn-workflow-ion-request-adu`), which needs an ION attempt/route
     record and an external helper.
   - The lab therefore evaluates `fn-bpa-make-request` through the ACL2
     bridge, as the native test module does.
   - Smallest host change: a `bp-obligation request` verb. It would
     publish ACL2's attempt record (`fn-bpiw-attempt-record`) and take the
     `:submit` effect (`fn-workflow-take-submit`), then enqueue
     `fn-bpo-request-adu` into A's FNBS keyed by (work, attempt,
     generation).
   - Not implemented. With an attempt in `:intent`, it is unverified
     whether A's receipt acceptance still matches, and the attempt record
     is ION-named.
3. **`bp-node serve`'s own forwarding still expects the application peer
   as its TCPCL neighbour** (`bp-node.lisp:225`). With a BPA at
   CONTACT-HOST:PORT, a receipt forwarded by the serving node itself would
   be refused at SESS_INIT. `bp-contact tick`, which the lab uses, passes no
   expected peer. The smallest change is the same as fix 1, but for an
   outbound check. It is left for the coordinator because it widens what an
   outbound session accepts.
4. **Mock-mode four-node JournalError: a real defect in the fn workflow
   journal replay (ACL2), not in the lab.**
   - relay-a is killed at `postlink` of its `enqueue` publication, and
     recovery publishes `outcome txid=101 phase=recovery result=committed`.
   - `fn-workflow-preflight-history` (`host/workflow-host.lisp:103-108`)
     rejects that record, and so does `committed`/`absent` in any form.
     A preflight of the record alone is `ready`.
   - Installing `[config, enqueue, outcome(recovery)]` is rejected
     (`ACL2 rejected workflow journal`).
   - Live `apply_record` of the same outcome on the installed image is
     `ready`, and it unfences
     ([`diag_mock.out`](m4-app-receipt-2026-09-24/diag_mock.out)).
   - Cause: `fn-bpiw-replay-records` (`books/bp-ion-workflow.lisp:123-134`)
     applies every record with live semantics (`fn-bpiw-apply`, `:105-121`,
     through `fn-bprl-apply-journal-record`) and restarts only after the
     last record. A recovery outcome needs a fenced pending
     (`fn-bp-recover`, `books/bp-workflow.lisp:~531`), so mid-history it is
     a no-op, which counts as rejection.
   - The disk replay `fn-bp-replay-records`
     (`books/bp-workflow-records.lisp:182-203`) fences first (complete
     `:indeterminate`) and then recovers.
   - Consequence: a recovery outcome can never be published through the
     history preflight. Any path that publishes one by live apply leaves a
     journal that `fn-workflow-install-replay`
     (`host/workflow-host.lisp:9-17`) can no longer reopen.
   - Smallest fix: make `fn-bpiw-replay-records` fence before a
     `:recovery` outcome, as `fn-bp-replay-records` does, or delegate the
     BP records to it. This is a book change for a lane with a farm slot.
     Mock evidence: `fe2ae6ea3113662f`.
5. **Kill-and-restart does not duplicate.** The held first transfer never
   produced a bundle at the first hop, and B took custody exactly once in
   every run. dtn7's sled store logged `already in store, updating it` for
   the resumed bundle.

## M4's exit clause, now

*Interrupted exchange and restart preserve accepted responsibilities;
application acceptance remains distinguishable from transport delivery.*

- **Has, on the DTN developer image, through dtn7-rs 0.21.0 (one and two
  relays):**
  - An fn request survives a SIGKILL of the carrier mid-transfer. A's
    send is `uncertain` rather than sent, and its durable job is resumed
    and `accepted`.
  - B's node takes custody once and its application decides once.
  - Transport delivery (`BP accepted`, kind 5) and the application
    verdict (`request-refused`) are separate lines and separate outcomes.
  - A's obligation stays pinned because no receipt came back. Nothing is
    inferred from transport.
  - On the direct control, the full native loop runs through the same
    lab: request accepted once, receipt authored by B, receipt matched at
    A, pin released.
- **Lacks:**
  - An application receipt through a real BPA. This is blocked by
    finding 1, a trust decision in ACL2.
  - Native request authoring from the workflow (finding 2).
  - `bp-node serve` forwarding through a BPA (finding 3).
  - A four-node mock run past relay-a's recovery (finding 4, an ACL2
    replay defect).
  - Frozen DTN images from a shared cut. These images are scratch.

## Stopped and released

- **Stopped by PID:**
  - dtnd: 1915453, 1939947, 1946948, 1960011, 1961129 and 1963257 by
    SIGKILL (the cut); every restart by SIGTERM.
  - fn nodes: by SIGTERM, or SIGKILL for the control's cut (1959558).
- **Ports:** only ephemeral ports were used, and all are released. The
  fixed exchange ports 32401/32402/32411/32412 were not used.
- `/tank/fn/node` was not touched.
