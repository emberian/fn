# BP forwarding checkpoint, 2026-09-24

The host-called `fn-bpnp-step` now selects a held transit carrier under a
negotiated TCPCL session, proposes immutable FNBS kind 8 before giving TCPCL
the exact ACL2-authored forwarding image, and records a definite result as
kind 9. Both kinds replay through the same row-update functions used by the
live callback. The outer state carries received-final count and cleanup debt;
successful cold replay rebuilds them from the ordered rows, while a fault
preserves the prior state. The host does not infer application receipt or
release from the TCPCL outcome.

The selected ACL2 runs on persvati used ACL2 8.7, toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`,
one job and a 120-second per-book cap. The source-matched manifests are
`certify-20260924T064105Z-1331425.json` (forward attempt and outer live
teeth), `certify-20260924T064239Z-1346105.json` (publication and mixed
replay), `certify-20260924T064028Z-1324662.json` (debt prerequisites), and
`certify-20260924T064322Z-1352087.json` (reached two-kind-5, two-kind-6,
MRU/attempt/result and cache teeth). Earlier failed selected attempts exposed
fixture include/token errors and are superseded by these passing manifests.

The native N04 interrupted-contact/restart test is source-only pending a
saved image at this revision. The existing source-matched image still predates
this packet and exposed an independent A3 character/octet boundary error;
it cannot establish native forwarding success. The actual outer cold-recovery
cache theorem is not admitted; five local projection lemmas and byte-replay
teeth are certified. `books/bp-node-progress-guards` does not certify at this
source: `verify-guards fn-bpnp-credit-blockedp` lacks the rational `free`
premise, and later new helper guards have not been checked. No guarded native
execution claim follows from this checkpoint. Post-kind-8 ambiguous TCPCL
outcome keeps the attempt active and fences the host; a defined recovery
settlement policy for that active attempt remains open. The full N03 class
fairness and general carried-debt invariant also remain open.
