# E2 byte-store reopen bridge (2026-09-23)

`fn-bs-crash-image-consumer-replay-ok` composes the existing byte scan/image
theorem K2 with `fn-csi-recovery-crash-image-strict-replay`. The latter is a
maintained-state result: `fn-csi-full-relationp` holds initially and is
preserved by `fn-snrt-step`; its proof covers the optional removal of the
last unfenced record in the three recovery phases by strict replay of a
successful prefix. The bridge concludes that the **scanned bytes' decoded
record list** passes the same ACL2 consumer projection interpreter used by
`fn-sn-open-observed`. No consumer validity of the observed list is assumed.

`fn-bs-crash-image-reopens`, acknowledged-record K4, and the recovery sweep
reopen theorem now require this maintained full relation. They retain the
separate observed identity-replay premise: that older kernel condition has
not been discharged by the E2 consumer proof. K4's acknowledged-pair arm is
substantive in the publish window; the recovery window has no successes of
its own, while the general reopen theorem covers both windows. General K0
proof that every physical P-RECORD call trace establishes and preserves the
byte/kernel relation remains open, as does the full byte-to-native device
failure correspondence.

Certification on hbox used ACL2 toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
`python3 tools/farm.py submit hbox --jobs 2` with only
`books/byte-store-keystones` and `tests/acl2/byte-store-scan-tests` requested.
The book passed in
[`certify-20260923T215107Z-249478.json`](manifests/certify-20260923T215107Z-249478.json);
the final test bytes passed in
[`certify-20260923T215342Z-257308.json`](manifests/certify-20260923T215342Z-257308.json).
The test's initial attempt failed because the old sample store contains
placeholder config/frontier octets, not the concrete framed metadata. The
test now constructs the real initializer image and checks its related state,
modeled crash, consumer replay and host reopen. Three earlier failed test
attempts are retained in the manifests. `make check` passed after ledger
regeneration.

The consumer lemma's test book supplies a structurally valid
registration-before-bootstrap negative record history and current/rollback
positive histories. The byte test added here has an initial concrete image;
it does not yet give a nonempty E2 consumer-event byte image or an independent
byte-level tooth isolating `fn-csi-full-relationp`. That is test evidence
still owed for the expanded K4 hypothesis. The ACL2 theorem is certified at
the stated hypothesis, not a claim that all served physical traces satisfy
it.
