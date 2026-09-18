# Real BPv7 to fn acceptance — 2026-09-18

The integrated [fn ingress harness](../bp-dtn7/run_fn_ingress_lab.sh) passed
with pinned dtn7-rs `4daf02d7ea927e9293753b2a5c4497457f6e5a40`. Two actual
loopback BPAs carried an exact legacy article to **one fn receiver**. The
[record](2026-09-18-bp-ingress.json) retains versions, commands, bundle identities,
source digests and exact article/state observations.

1. A queued the article while B was absent, then forwarded it on renewed contact.
2. B restarted before fn received it. Inventory rediscovered its stored bundle.
3. Non-destructive download and durable inbox publication preceded actual ACL2
   parsing, configured routing, Store acceptance and explicit BPA deletion.
4. A second real send used a distinct bundle ID with identical article bytes.
   fn returned `duplicate`; reopening still found one transaction, one article,
   one archive pin and the identical payload digest.

Four actual ingress host tests also passed: two distinct articles, same-ID
conflicting bytes, exact duplicate with a new BID, delete failure and restart,
malformed/unknown-group rejection, and refusal to open an unvalidated workflow
journal. Fifteen journal I/O tests passed, including publication faults and real
process exits. These latter tests use replay callback fixtures; they are not
evidence of integrated ACL2 workflow semantics.

The complete current Python suite then passed all 86 tests in 101.527 seconds;
the recorded implementation source snapshot still matched afterward.

The actual Store and parser are used; there is no Python article parser or
acceptance implementation. Metadata uses the existing per-article derivation
after ACL2 extracts Message-ID. A source EID is observed transport provenance,
not authenticated authorship.

The sender in this test is a BPA plus a fixture file. Durable fn outbox jobs,
portable request context and application receipts remain active work. The
inbox-only ingress rejects nonempty workflow record histories until their actual
ACL2 replay bridge is integrated. It emits no receipt. The known-fixture CLI
harness does not establish hostile-input resource bounds, power-loss durability,
authenticated transport, a complete RFC injection profile or mission readiness.

Run with a pinned build and available loopback ports 32301/32302/32311/32312:

```sh
DTN7_REPO=/absolute/path/to/pinned/dtn7-rs tests/bp-dtn7/run_fn_ingress_lab.sh
```
