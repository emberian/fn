# BP routing decision owned by ACL2 (lane bp-routing, 2026-09-25)

M4 native request §2 finding 2 found that the machine had no ACL2 decision
for the next hop. The contact on the command line chose it, and an outbound
`bp-node serve` session accepted whatever node ID the contact announced. This
lane moves that decision into ACL2 and connects it to the host. The design is
in specs/bp-node-machine.md §4.7. The requirement is REP-007 and the proof row
is PRF-079.

## What landed

- **Rows.** `operator CONFIG bp-route add PATTERN BOUNDARY [PRIORITY]` and
  `bp-route remove PATTERN BOUNDARY` go through `fn-native-admin-plan` as kind
  `:set-bp-route`, a single `:set-peer` delta. `bp-boundary add ... contact
  PORT` writes the boundary's contact row.
- **Decision.** In books/bp-route.lisp: `fn-bprt-next-hop` (line 156),
  `fn-bprt-outbound-choice` (179), `fn-bprt-offer-decision` (202) and
  `fn-bprt-table` (430).
- **Call site.** books/bp-node-progress.lisp `fn-bpnp-routed-start` (1381),
  called from the `:session` arm (1444) when the event carries
  `(:via HOP ANNOUNCED TABLE)`.
- **Host.** host/native/bp-node.lisp `fnn-bpnode-forward-contact` (280) asks
  `fn-bprt-outbound-choice` over `fn-owner-bp-route-table`
  (host/bp-native-app-host.lisp). With no route it opens no session and
  prints `BP forwarding no-route destination=… decision=…`. Otherwise
  `fnn-bpnode-forward-session` (297):
  1. connects to `127.0.0.1:PORT`;
  2. passes the boundary's EID as the expected TCPCL peer;
  3. sends the routed `:session` event at line 343.

  host/native/bp-service.lisp reports `:forward-no-route`. CONTACT-HOST:PORT
  no longer chooses the hop for held transit.

## Theorems (keystones)

| Name | Statement (short) | Subject / host line |
| --- | --- | --- |
| `fn-bpnp-step-offers-only-the-routed-hop` | On a routed :session, a `:persist-attempt` is for the scan's row. The table routes that row's destination to HOP through a matching route that names HOP. ANNOUNCED is HOP's enrolled EID. | `fn-bpnp-step`; bp-node.lisp:343 |
| `fn-bpnp-step-unrouted-bundle-stays-held-and-is-reported` | With no matching route, the only effect is `(:forward-no-route ARRIVAL HOP :no-route)` and the held list is unchanged. | `fn-bpnp-step`; bp-node.lisp:343 |
| `fn-bprt-next-hop-deterministic-in-the-table` | Tables whose matching routes are the same set give the same answer. | `fn-bprt-next-hop` |
| `fn-bprt-next-hop-names-a-live-matching-route` | A boundary answer is a live matching route of the table. | `fn-bprt-next-hop` |

The teeth are in tests/acl2/bp-route-tests.lisp. There are 33 assertions and
7 `must-fail` forms. The witness is the held transit bundle to
dtn://bp-dest/, which is routed to "relay" and proposes the attempt. The
must-fail cases cover:
- an unlisted hop, which is refused even when it announces the listed EID;
- a wrong announced EID (`:announced-mismatch`);
- a prefix route to another boundary;
- the route present, where no report appears;
- tables whose matching sets differ, which give different answers;
- no live route (`:no-live-hop`).

## Certification (hbox farm, w28 acl2-literal-4g, 2 jobs, timeout 300)

| Run | Manifest (sha256/16) | Result |
| --- | --- | --- |
| dede @ d3e96a5d | certify-20260925T043045Z-2491547 (c8add6e09f57f2c4) | passed. 5 books: bp-route 3.0 s, bp-route-step 7.5 s, bp-route-tests 6.0 s, bp-node-progress 5.7 s, bp-node-forward-retry 7.8 s. |
| af19 @ 4ccecd3c | certify-20260925T043302Z-2495464 (9d646c2e367d3964) | failed. bp-node-progress-premises had no keep lemma for the routed arm, and three books behind it failed. native-admin took 17.7 s. |
| d00b @ 7eb2e670 | certify-20260925T043708Z-2506982 (bfc9232a9d068fa7) | 22 passed, including premises, guards and the forwarding teeth. 8 failed (below). |

Run d00b failures and their fixes:
- **books/native-admin, the `plan-of-set-bp-boundary` lemma.** The kind
  accessor opened to `caddr`, so the new rewrite rule did not fire. The fix
  is `fn-bprt-admin-plan-caddr-is-no-other-kind` in bp-route.lisp.
- **books/bp-node-progress-bridge, `bpnpb-routed-start`.** Enabling
  `fn-bpnpb-effects-confinedp` hid start-one's rule. The fix is a separate
  `bpnpb-no-route-report-confined`.
- **Six books failed only because of those two:** native-operator,
  native-operator-host, and the native-admin, native-operator,
  native-operator-host and bp-node-counterexamples tests.

Both fixes are in the final commit. In a proof REPL on hbox, the bridge
loaded all 52 forms and native-admin's remainder loaded with 0 failures; its
slowest event took 0.24 s, down from 12.9 s in run af19. **They have no
farm manifest.** The brief's three-run limit was reached. One more affected
run owes these books a manifest: `--affected-by books/bp-route.lisp`,
`books/native-admin.lisp` and `books/bp-node-progress-bridge.lisp`.

Over 10 s at 2 jobs:
- bp-node-progress-guards: 11.0 s, against 10.8 to 11.2 s before this lane.
- native-admin-peer: 12.7 s in run af19, against 8.2 s before. The
  `contact` peel adds a case to its plan theorems.

## Native

**Not run.** The DTN developer image needs the whole dtn-profile closure
certified, and native-admin plus native-operator have no certificate at the
final bytes (above). Staged but not run:
- tests/test_bp_node_native.py. Every node now enrols `contact <relay port>`
  and `bp-route add <peer>* <boundary>`. The new
  `test_removed_route_keeps_transit_held_and_reports_no_route` removes the
  route and expects `BP forwarding no-route destination=dtn://sender/
  decision=no-route` with no kind 8 and the kind 5 held. It then adds the
  route back and expects the forward to settle as `status=sent`.
- tests/bp-dtn7/run_fn_dtn7_app_receipt.py adds the topology as route rows.

The lab log SHAs are owed with the run.

## Findings

1. **FNBS base jobs are not routed.** These are `bp-obligation request`,
   receipts and reports sent by `bp-contact tick`, and `bp-service`. Each
   still carries the CONTACT-HOST:PORT it was queued with. In the dtn7 labs
   the fn endpoints send only through base jobs, so a removed route there
   does not stop A's request. To route them, the base job's route would have
   to be chosen by `fn-bprt-outbound-choice` at queue time.
2. **The 6-field `:session` form and `:resume` are not gated.** The host
   sends neither open. Removing the ungated open form would change
   `fn-bpnp-step-session-offer-is-the-scan-choice` and its teeth.
3. **An unrouted older row blocks younger rows under the same key.** The
   dispatch key is still the single-peer route, and the gate reads the scan's
   chosen row. That row can be an older unrouted row with the same key, which
   then blocks younger ones on that session. With single-peer routes, every
   row under a key has that key as its destination.
4. **Priority orders boundaries, not sessions.** LIVE is (HOP): the host holds
   one outbound session at a time. Priority orders the boundaries that have a
   contact.
