# Realignment wave: cluster ownership

One deputy per row. A deputy edits only books in its row (and their test,
teeth and guards books under `tests/acl2/`), keeps the row's include-closure
certifying, and proposes interface changes to neighbours rather than making
them. The core deputy goes first and writes `docs/proof-style.md`; the others
launch against that document.

| Deputy | Books | Model |
| --- | --- | --- |
| core | acceptance, acceptance-invariants, retention, retention-invariants, node, node-invariants, node-traces, replay, replay-invariants, exchange, exchange-invariants | Fable |
| store | store-files, store-files-invariants, store-files-traces, store-node, store-node-invariants, store-node-resolution, store-node-traces, store-node-resolution-traces, store-observed, store-observed-traces, checkpoint, index, journal | Fable |
| codecs | cbor, cbor-invariants, records, records-invariants, records-canonicality, frame, frame-invariants, identity, identity-invariants, store-config, bp-adu, bp-primary-cbor | Opus |
| nntp | wire, wire-invariants, article, article-invariants, article-properties, article-work-*, article-public-*, article-fields, wildmat, wildmat-*-invariants, wildmat-work, nntp, nntp-invariants, nntp-effects, nntp-index, transfer, transfer-* | Opus |
| bp | bp-workflow, bp-workflow-*, bp-workflow-records, bp-workflow-records-invariants, bp-outbound, bp-ingress, bp-receipt, bp-receipt-records, bp-receiver-*, bp-release, bp-release-invariants, relay, relay-invariants, relay-crash-invariants, bp-primary, bp-primary-invariants, bp-fragment, bp-fragment-invariants, clock, clock-invariants | Fable |
| substrate | crypto-seam, principal, principal-invariants, statement, statement-invariants, lace, lace-invariants, policy, policy-invariants, membership-epochs, membership-epochs-invariants, assumptions | Opus |
| tooling | tools/, tests/test_*.py for tools, ledger lints, Makefile, docs/proofs.md | Opus (done: `dep/tooling`) |

Shared-interface rule: accessor and keystone NAMES stay stable across the
wave so includers do not change; a deputy that must break a name records the
one-line change each includer needs in its proposal. The convergence merge
applies those changes and runs one farm gate.

Pending feature lanes (rebased after the wave, each by its own small deputy):
mutable-owner, bundle-identity, identity-v1, reader-profile, scheduler,
media-lab, time-anchor, checkpoint, fragment-container, native-host.
