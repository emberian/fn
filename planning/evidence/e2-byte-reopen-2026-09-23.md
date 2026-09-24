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
the final expanded test bytes passed in
[`certify-20260923T220256Z-276657.json`](manifests/certify-20260923T220256Z-276657.json).
The test's initial attempt failed because the old sample store contains
placeholder config/frontier octets, not the concrete framed metadata. The
test now constructs the real initializer image and checks its related state,
modeled crash, consumer replay and host reopen. Earlier failed test attempts
are retained in the manifests. `make check` passed after ledger
regeneration.

The follow-up byte test runs the actual frontier, P-RECORD and finish
programs with the same bootstrap event as the actual `fn-snrt-run` trace.
The nonempty physical crash scan reads the exact bootstrap event and reopens
with a consumer projection. It also frames and publishes a structurally
valid registration before bootstrap through the file program: the byte
relation and modeled crash premise still hold, while `fn-csi-full-relationp`
and consumer replay fail. Pairing that physical image with a valid bootstrap
node separates the byte/kernel-relation premise; presenting it as an image
of the good byte state separates the modeled-crash premise. The three
`must-fail` assertions are in `byte-store-scan-tests.lisp` and passed in
[`certify-20260923T220256Z-276657.json`](manifests/certify-20260923T220256Z-276657.json).
The invalid registration is deliberately unreachable through the checked
Store-node prepare transition; it is a counterexample to dropping the
maintained relation, not a claimed served trace. General K0 still has to
establish the byte/kernel relation for all served physical traces.
