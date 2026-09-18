# Actual fn → BP → fn → receipt → BP → fn exchange

On 2026-09-18 the complete trusted-loopback exchange passed against pinned
dtn7-rs `4daf02d7ea927e9293753b2a5c4497457f6e5a40` (0.21.0). Both ends use
actual ACL2 decisions, recovered article storage and durable workflow journals.
The [machine record](2026-09-18-bp-exchange.json) contains source hashes, tool
versions, invocations, certificate manifests, failures and corrected runs.

## Exercised behavior

1. A commits an article/archive pin, durable work and submission intent, then
   submits while B is absent. A's application session and BPA restart.
2. A still has the article, pin and outstanding work. It durably records an
   explicit retry and sends the identical application request in a fresh bundle.
3. B stages the complete ADU non-destructively, accepts through ACL2/Store, and
   durably records its context and receipt decision before deleting that bundle.
4. The first receipt is deliberately omitted. B's application session and BPA
   restart. Another explicit sender retry uses a different bundle ID.
5. B recognizes the exact application request and regenerates the identical
   receipt. Its article, pin and receipt journal records do not multiply.
6. The receipt traverses real BP back to A. A durably commits the matching
   application decision and reopens successfully. Both nodes retain exactly
   one article and one independent archive pin with the original article bytes.

The final run is `build/bp-fn-exchange/exchange-ou541xe9/evidence.json`; its
runtime sources were unchanged. All listeners were IPv6 loopback. Run it with:

```sh
python3 tests/bp-dtn7/run_fn_exchange_lab.py --dtn7-repo build/bp-spike-work/dtn7-rs
```

## Verification

- **132 Python tests passed**, 129.875 seconds, Python 3.14.7. This includes seven
  new receiver exception/reopen cuts over the actual FNBI, Store, FNRJ and ACL2
  bridges, plus the existing sender journal/process-death and storage suites.
- **Nine scoped ACL2 roots passed** across the recorded outbound, corrected
  receiver/journal and sender invariant batches, using ACL2 8.7 / SBCL 2.6.8.
  This is not a new full all-roots run.
- General finite sender traces preserve recognizable state and the exact node.
  Transport-only traces preserve receipt decisions. Stale-event, unchecked
  receipt, fencing and retry results are certified. Outbound projection checks
  actual node/article binding and local-policy-authorized receipt preparation.

The seven new receiver cases cover staged inbox, article-before-context,
context-before-intent, intent-before-decision with explicit recovery, durable
decision before failed BPA deletion, wrong policy/destination, and capacity
refusal preserving prior acceptance. These inject exceptions and reopen files;
they are not seven OS process-kill or physical power-loss experiments.

## Findings retained with the successful result

Recovered Store acceptance initially depended on transient success history.
The corrected predicate requires a ready, valid Store, exact authoritative
record membership and the matching node article/subject/archive binding.

An earlier full exchange reached the returning receipt but sender replay failed:
restart had made an attempt retryable only in live state. Explicit retry records
now preserve that decision. Pure ACL2 whole-history preflight also rejects any
candidate journal record that would fail replay, before publishing or calling BP.

A subsequent transport run retained the first bundle after BPA restart but did
not forward it. Logs place termination between initial persistence and the
dispatch update. Pinned source (`core/processing.rs` send/transmit and
`core/mod.rs` process_bundles) separates those operations and retries only
forward-pending bundles. The final harness therefore recovers through fn's
durable retry policy rather than treating inventory presence as forwarding
readiness. The original bundle may remain inert or arrive as another duplicate.
The successful run does not establish BPA recovery for every internal cut.

## Remaining boundaries

Local A-POLICY is explicitly trusted; receipts are unsigned. Native signatures,
authenticated peers, general receiver trace/journal refinement and the joint
durable/pending-work binding invariant remain open. Outbound retains its explicit
binding check. No complete cooperative-peer handoff theorem is claimed.

LTP, non-overlapping multi-relay contact plans, carried-media composition,
clock-error/liveness/fairness cases, production scheduling, and mission profiles
remain work. Process termination/restart and POSIX operations do not qualify
hardware power-loss behavior. BPA stop artifacts record SIGTERM and any SIGKILL
fallback. The pinned decoder, host I/O and filesystem assumptions remain trusted.
