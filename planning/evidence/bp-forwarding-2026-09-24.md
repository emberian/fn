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
saved image at this revision. The prior image predates this packet and exposed
an A3 character/octet boundary error that has since received a source fix;
it cannot establish native forwarding success. The actual outer cold-recovery
cache theorem is not admitted; five local projection lemmas and byte-replay
teeth are certified.

The forwarding frame codec passed the selected persvati run
`run-20260924T070020Z-c470` (manifest
`certify-20260924T070026Z-1507216.json`). The lower dispatch, forward-image,
and attempt/result guard book passed `run-20260924T070624Z-556c` (manifest
`certify-20260924T070630Z-1564034.json`). The composed host-called progress
guard root **did not certify** in `run-20260924T070716Z-108a` (manifest
`certify-20260924T070729Z-1573594.json`): ten parents passed, then
`verify-guards fn-bpnp-issued-debt-delta` timed out at 120 seconds. Its first
remaining guard goal requires `fn-bpn-machine-statep` of the retained base for
the `:family` arm because `fn-bpnf-family-apply-at` has that guard. The
delegate's input carries this invariant, but the helper is called on an inner
`fn-bpn-report-author-step` result; the next proof must establish preservation
for that actual result without scanning the whole base on every served step.
No guarded native execution claim follows from this packet.

After durable kind 8, process death before the host sends or publishes kind 9
replays a `:forwarding` row while recovery clears the session and pending
image. The current session selector does not re-offer that row, leaving its
reserved debt stranded. Automatic retry after a possible send would raise a
duplicate-control policy question, so this remains an explicit crash-recovery
liveness obligation. The full N03 class fairness and general carried-debt
invariant also remain open.
