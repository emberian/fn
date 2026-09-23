# A mixed-certificate Store include failure, 2026-09-23

Qualified persvati ACL2 8.7 runs `certify-20260923T172706Z-2191257`
and `certify-20260923T172907Z-2212193` attempted the focused Store
composite test under toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`.
Both failed before a Store theorem was attempted. Their original manifests
are archived byte for byte (SHA-256 `c8f61a84d93f582beba6f6d4be36b2cedf0d44808ca5126ce6c3dd2fa5557441`
and `13e9d2820dc39f4107297e1ad0ccf863cab6d092700fec95facd33346b3ec7a4`).
The first `books/store-node-traces` log is
[`first-store-node-traces.log.gz`](cert-cache-composition-counterexample-2026-09-23/first-store-node-traces.log.gz)
(decompressed SHA-256 `b763de2fd0deb36366480573b0f022074e4be92ea65705908646f903da7fc096`);
the second is
[`second-store-node-traces.log.gz`](cert-cache-composition-counterexample-2026-09-23/second-store-node-traces.log.gz)
(decompressed SHA-256 `db7bbc3867d67cc0870b7b19d889b7591aaf63a896d9d71cba7719ec1fb60f90`).

In the first run, cache preflight kept a set from six origins. At the first
error, `(include-book "stx-accept-records")` rejected that cached book's
certificate: it required `records-seam` as certified from
`/home/ember/fn-gates/takeover-acceptance-stamp`, while ACL2 had included
the familiar book from `/Users/ember/dev/fn/build/lanes/authorship-integration`.
The log lists other required/included origin differences in the same error.
The second run reduced the mix but still drew from four origins and failed
on that include. The manifest's source digests for `stx-accept-records`,
`records-seam`, and `store-node` match before and after certification.
The source closure key and toolchain identity therefore did not predict this
certificate composition's acceptance.

The message enumerates different full-book-names; it does not identify which
required `(familiar-name, certificate annotations, book-hash)` entry failed
ACL2's subset check. Absolute path difference alone is not established as the
cause. The successful small chain and diamond experiments in
[`certificate-cache-2026-09-23.md`](certificate-cache-2026-09-23.md) and the
separate successful combined mixed-origin run remain valid in their measured
scope. This failure bounds their generalization: composition must be treated
as an ACL2-checked attempt, and a failed cached include is a cache-compatibility
event, not evidence that the Store theorem failed. The immediate bounded
repair is to certify the affected include frontier under one coherent run
origin or avoid that cached frontier in a focused test, then verify the new
run. No existing cache entry or failed-run evidence was rewritten here.
