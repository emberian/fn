# Fragment carrier admission and expiry-safe family replacement

The earlier constructed-state counterexample and wire-path refusal are kept in
`bp-fragment-expiry-gate-2026-09-23.md`. This packet changes both gates
together. The native `fnn-bps-receive` calls
`fn-bpnf-receive-wire-event`, whose shared ACL2 carrier decision admits a
validated fragment for durable kind-5 custody. `fn-bpn-receive` still refuses
partial application ADUs, and `fn-bpah-pending-view` excludes held fragments.

At family proposal, `fn-bpnf-family-plan-at` checks **every** selected row at
one host-supplied ACL2 clock observation. It does not time-filter the
principal/coherence active set. `fn-bpnf-family-next` skips a blocked family
and scans for another eligible one. The host-called
`fn-bpnf-fragment-step` can emit `:persist-family` only after the selected
rows are live under the event observation; the certified keystone is
`fn-bpnf-fragment-step-family-publication-has-live-sources`. The observation
is encoded in the version-1 kind-18 protected frame. Both live durable
callback and ordered byte replay invoke `fn-bpnf-family-apply-at` with that
recorded observation, recomputing exact family membership and whole wire.
Historical unversioned kind-18 bytes are still parsed, then fault recovery
with `:legacy-family-expiry` instead of receiving an invented clock value.
Refused publication leaves source rows retained; uncertainty fences further
ordinary transitions until recovery.

The test books include the original expired-nonzero/fresh-zero family,
unknown-age refusal, a later eligible family behind a blocked one, canonical
version-1 codec and historical-frame fault, refusal/uncertain publication,
and an exact equality witness between the actual live durable callback's
installed held row/frontier and ordered kind-5/18 byte replay. Hbox ACL2
toolchain identity `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`
certified the affected 16 roots plus one missing dependency in
`run-20260924T010953Z-2a0f`, manifest
`planning/evidence/manifests/certify-20260924T011004Z-671572.json`;
the stronger exact replay test certified in `run-20260924T011157Z-2fcb`,
manifest `planning/evidence/manifests/certify-20260924T011207Z-675227.json`.

These are ACL2 results over the reported source snapshot and reported clock
observations. The source-matched saved image and interrupted-contact native
fixture remain open. The inherited ordered recovery decoder's guard is not
verified by the fragment live-wrapper guard book. Clock observations assume
the separately persisted boot-domain authority and do not prove peer clock
honesty, full RFC lifetime semantics under unknown upstream age, kind-10
conflict deletion, or proactive forwarding fragmentation.

The activation was transplanted onto current `dev` base `8c61c098`, reusing
its already-integrated arrival-frontier repair and pure expiry selector. The
changed BP book/test roots certified on persvati jobs 2 in
`run-20260924T033253Z-6f04`, manifest
`planning/evidence/manifests/certify-20260924T033307Z-3777649.json`:
142 matching dependencies installed and 40 current-source certificates
completed. This result covers the edited roots, not yet their downstream BP
dependents or a native saved image. The subsequent affected run is recorded
separately when it finishes.

The first current-source dependent sweep `run-20260924T033925Z-d9be`, manifest
`planning/evidence/manifests/certify-20260924T033936Z-3836310.json`,
certified 53 of 56 scheduled books. Its real BP test failure exposed a fixture
coupling: the previously nil-anchor row became `(:wall)` in the new live
fragment fixture, so the independent legacy-unknown tooth no longer had a
legacy row. Commit `5cb84637` constructs an explicit nil-anchor legacy pair;
that test root then passed on persvati jobs 2 in
`run-20260924T034643Z-df49`, manifest
`planning/evidence/manifests/certify-20260924T034655Z-3902697.json`.
`green_check --changed-since 8c61c098` reports one remaining unqualified
affected root: `tests/acl2/bp-transit-join-tests`.
`books/owner-invariants` timed at
120 seconds at the current Store-v6 base, and
`tests/acl2/bp-transit-join-tests` failed only because its owner certificate
was unavailable. The owner proof cost also appeared in the frozen 8c61 hbox
run; it is not a BP transition counterexample. Neither of those two roots is
claimed qualified by the passing BP books.
