# multi-peer-relay (2026-09-26): an fn relay serves every admitted BP neighbour at once

Lane multi-peer-relay (dev lane, Opus 5.5), brief
build/coordinator/queue/done/w4-multi-peer-relay.txt; ids PRF-176, SCN-105,
PKT-464, PKT-465. Base dev bc774574.

## What now works

- `bp-node serve -` binds ACL2's listener set: one listener per transport-bp
  boundary listener row of the live configuration that admits a session
  (`fn-bpaj-listener-ports`, books/bp-listener-set.lisp, through
  host/bp-native-app-host.lisp `fn-owner-bp-listener-ports`), and accepts
  from any of them through poll(2) (host/native/io.lisp
  `fnn-accept-any-loop`): one session to its end before the next, no
  threads (spec 9.1). A numeric PORT is the old one-row case.
- Held transit is dispatched per destination: the :progress event carries
  the route table (`fn-bpnp-host-routes` -> `(:table TABLE)`), and each row's
  next hop is the EID of the boundary `fn-bprt-outbound-choice` names for its
  own destination (books/bp-node-progress.lisp `fn-bpnp-route-peer`).
- After each pass the host opens one outbound session per next hop with
  forward-pending transit (`fn-bpnp-forward-plan`,
  books/bp-node-forward-plan.lisp; host/native/bp-node.lisp
  `fnn-bpnode-forward-contact`).
- The four-node mission driver has no listener turns and no direction
  restarts (tests/bp-dtn7/run_mission_four_node.py).

## Assurance chain

native entry (`bp-node serve -`: fnn-command-bp-node) -> executed ACL2
subjects (`fn-bpaj-listener-ports`; `fn-bpaj-session-principal` inside
`fn-bpaj-tcpcl-ingress-result` per session; `fn-bpnj-step` -> `fn-bpnp-step`
-> `fn-bpnp-progress-step` on the (:table TABLE) :progress event;
`fn-bpnp-forward-plan`; the routed :session event's `fn-bpnp-forward-scan`)
-> behavioural theorems below -> observed result (the native gate and the
mission, below). The listener set is read once at open (the relation is
established by the open's configuration and holds while the configuration
does; a reconfiguration while serving is not re-read: PKT-464).

## Theorems (PRF-176) and host lines

Keystones, each over the function the host calls:

- `fn-bpaj-listener-session-is-admitted-under-its-row`
  (books/bp-listener-set.lisp): for PORT in `(fn-bpaj-listener-ports CFG)`
  and an EID ANNOUNCED, `fn-bpaj-session-principal` on the loopback channel
  of PORT is `(:admitted NAME GEN)` for the port's boundary NAME when
  ANNOUNCED is NAME's unique transport-bp EID, else `(:refused
  :eid-mismatch)`; never `:ambiguous-peer` or `:no-trust-profile`. Host:
  fnn-command-bp-node binds the set (`fnn-owner-core
  'fn-owner-bp-listener-ports`, the `(fnn-tcl-listen port)` loop before
  "BP NODE LISTENING"), then `fnn-accept-any-loop`; the session's admission
  is `fn-owner-bp-tcpcl-ingress` in `fnn-bp-deliver-node`.
- `fn-bpaj-admitted-session-arrives-on-a-bound-listener` (the converse) and
  `fn-bpaj-listener-ports-are-distinct`.
- `fn-bpnp-progress-dispatch-names-the-routed-hop`
  (books/bp-node-forward-plan.lisp): when `fn-bpnp-progress-step` under
  `(:table TABLE)` proposes `:persist-dispatch`, the record applies, its
  peer (the row's next hop after `fn-bpnp-dispatched-held`) is an EID, and
  its text is the EID of the route `fn-bprt-outbound-choice` selects for the
  named row's own destination (`:hop`; that route is a live matching one by
  the carried `fn-bprt-next-hop-names-a-live-matching-route`). Host:
  `fnn-bpnode-dispatch-one`'s `(:progress node obs (fn-bpnp-host-routes
  table peer) 0)` through `fn-bpnj-step` (`fn-bpnj-step-delegates-every-
  other-event`) to `fn-bpnp-step`.
- `fn-bpnp-forward-plan-offers-a-row-on-one-session` and
  `fn-bpnp-forward-plan-has-one-session-per-peer`: two plan entries whose
  sessions' `fn-bpnp-forward-scan` select the same held row are the same
  entry. Host: `fnn-bpnode-forward-contact` opens one
  `fnn-bpnode-forward-session` per `fn-bpnp-forward-plan` entry; the routed
  :session event's `fn-bpnp-routed-start` runs the scan. PRF-103's
  once-per-contact for base jobs is carried unchanged (the base contact
  driver did not change).
- `fn-bpnp-table-route-peer-is-the-routed-hop` (the lookup itself).

Teeth (tests/acl2/bp-listener-set-tests.lisp,
tests/acl2/bp-node-forward-plan-tests.lisp): reachable witnesses with the
complete antecedent and conclusion (X's two boundaries on two ports, both
arms; two held bundles routed to two neighbours, the dispatch, the plan and
the scans), and a must-fail per hypothesis (the shared port is unbound and
answers `:ambiguous-peer`; a malformed EID answers `:channel`; an admitted
session on port 0 is not bound; an empty table proposes no dispatch; a
forged entry with the same peer selects the same row but is not a plan
entry; two entries' scans select different rows; a scan that is not ready
carries the row in its second field).

Certification (hbox, 2 jobs, 300 s): run-20260926T120217Z-818d
(certify-20260926T120259Z-1578084: the BP closure of bp-node-progress, 93
books green, the forward-plan test book red on a defconst over the frame
digest, fixed by make-event), run-20260926T121348Z-8bc4
(certify-20260926T121417Z-1605075, green) and run-20260926T121859Z-4344
(certify-20260926T121940Z-1614524, green at bbd9bb9d; books/bp-node-forward-plan
10.3 s at 2 jobs, 0.3 s over D26: PKT-464 (b)). The manifests are in
planning/evidence/manifests/.

## K6 (PKT-202)

Answered in specs/bp-node-machine.md section 6 ("K6 answered"): the Store
admission is one decision with two carriers (`fnn-owner-attempt-transit`,
with `fn-peer-decide-transfer` shared before it); the principal is decided
twice, and that is the exact difference (NNTP: the session peer and the
carried list inside `fn-pcb-admission-verdict`; BP: `fn-bpaj-ingress-peer`
at the bundle, `transitp` nil, so a refused present carrier reports the
plan's reason, not the `fn-pcb` class). The equating keystone is not proved;
PKT-202 is narrowed to it. The two writer locks stay: each is its Store's one
owner process, and a relay serving NNTP and BP at once carries two Stores.
In the mission, K6 requires exactly B's step-5 stop (B's owner serves the
consumer) and step-6 restart (to hear A's receipt).

## The mission without turns (SCN-105)

tests/bp-dtn7/run_mission_four_node.py (sha256 aea092e4...) on this lane's
images (hbox, /tank/fn/scratch/multi-peer-relay/, each run under
systemd-run MemoryMax=24G; dtn7-rs /tank/fn/dtn7/repo at 4daf02d7):
fn-host-dtn-developer d874e81e74366e567f49170af2ea44809c379b30b99438bffe3bf7d33faebbc0,
fn-host-developer e396d924a6e00eedc2d6d7a68d832bfdc90d27145c51f7c9e7fe90ca75ec0230
(built at e3236a47; bbd9bb9d changes proof hints only, no definition).

| case | steps held | log sha256 | report sha256 |
|---|---|---|---|
| `--report signed` | 7/7 | c0caf6a0... (signed.out) | fcc0bea24f16882d78bdc3f228622c86b2834e5263018f3de30ecf85c4e66f55 |
| `--report unsigned` | 7/7 | 3a7ca79459602f6eae6cffed11b25f2b727395cee92b440e839a0639d2e1b826 | 8a3346d3f3a85dc2869ad56e024be0370ff8c0eb62325475e709f1a38bbb4582 |
| `--case ambiguous-peer` | 2/2 (X refuses, no custody) | 99ba9c97b8365c6b483d3e227b9652c3b1369310ccda9ea2949432a62bead1e4 | ceade7628e22d1980202770bf339841050495fd13f8977abc2fd8e989cbe97ea |

Incarnations (signed): Y one (`y-serve-1`, the whole mission, both
directions); X three (`x-serve-1`; `x-serve-2` after the step-2 SIGKILL;
`x-serve-3` when its step-2-to-4 outage ends; same argv each time); B two
(K6: stopped for B's owner in step 5, `b-serve-2` to hear A's receipt);
A three (SIGKILL in step 4; stopped for `bp-obligation status` and the
owner's consumer reads). Removed: every listener turn and every direction
restart (old lines 628-634 and 745-753; `port_far` is now only the second
boundary's row). The step-2 SIGKILL and the step-4 outage are the mission's
crash and outage demonstrations, not turns. The restart of the node whose
receipt is owed is gone: B's receipt reaches Y on b-boundary's listener at
the first offer (step 3), A's reaches X on a-boundary's (step 6). K6 requires
B's step-5 stop and step-6 restart and no other.

## Native gate (hbox, tools/hbox_native.sh e3236a47, images developer and dtn-developer)

- tests.test_bp_node_native 27/27 OK, log 367df9adb8425c11809b16e0d8104d14c4c2c0a37d5b8f4ec094cb0c21dc829f
- tests.test_bp_service_native 17/17 OK, log 04bbdb390ff83f4c287c79219186b55564eda5e2b314e43766f9f1000c966d50
- tests.test_native_bp_node_admission_lock OK, log 85a4b83e971a6cf7dc0097d4202b600c276141ad91875d4e3a9dae77f8840924
- tests.test_bp_contact_relay_native: skipped in the first run (harness: it
  needs FN_NATIVE_CONTACT_SENDER/RECEIVER, which hbox_native.sh does not
  set); rerun with both set to the dtn-developer image: 1/1 OK, log
  47a413f75492d44144884b33407d63976a6774ba84e8dd7c02fcc3d0550e2e3d.

## Not done, and why (PKT-464)

(a) the listener set is read at start, not after a live reconfiguration;
(b) books/bp-node-forward-plan is 10.3 s at 2 jobs (0.3 s over D26);
(c) a next hop fixed before a route change is offered only to that hop
(PKT-148); (d) dtn next hops only (`fn-bpnp-text-eid`); (e) a pass runs only
at start and after an inbound session, one bundle per outbound session per
pass; (f) the K6 equating keystone (PKT-202, narrowed). `make check-lane`:
every check but proof_cost passes; proof_cost fails on this lane's
bp-node-forward-plan (10.3 s, (b)) and on three books this lane did not
touch (native-admin 15.9 s, native-operator 11.8 s, peer-pull-session
11.7 s, all persvati certify-20260926T112155Z-967430 on dev).
