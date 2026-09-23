# BP application handoff service composition, 2026-09-23

The full BP service now replays one ordered kind-5/kind-7 FNBS stream through
`fn-bpah-recover-auto-event`. A definitive application result emits a kind-7
publication effect from `fn-bpnf-step`; the host asks
`fn-bpah-publication-authorize` for the exact name, frame, and immutable
publisher operation, then returns the actual durable/refused/uncertain result
to the same machine. The application caller owns `:deliver` effects and is
separate from this service change. This packet does not establish receipt
outbox completion or application release.

The frozen source is `e459f963` on top of A2 `2811a555`, with the A3 logical
chain `3b2a07fb`, `1d00ce84`, `2a1f37f6`. Hbox ACL2 8.7 / SBCL 2.6.8,
toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
certified 32 affected book/test roots with jobs 2, no closure, in
`run-20260923T200503Z-6cfd`; the exact
[manifest](manifests/certify-20260923T200515Z-16894.json) reports `passed`
and no book failures. The incremental run installed 124 compatible dependencies
from four cache origins and certified 32 roots in 67.424 seconds. The strict
changed-root gate found zero ungreen roots. `make check` passed after
regenerating the ledger. SBCL source-loaded `host/native/bp-service.lisp` with
only the expected image environment stubs; no A3 image or process test is
claimed here.

The native caller joined at `5930f4f2`. Its five dependency-shifted roots
passed hbox `run-20260923T202049Z-8165` with
[manifest](manifests/certify-20260923T202059Z-31204.json); the strict
changed-root gate then had zero ungreen roots and `make check` exited zero.
The explicit full-image default profile listed 80 roots; hbox
`run-20260923T202252Z-a0cc` installed 79 and certified its one missing root
([manifest](manifests/certify-20260923T202257Z-33256.json)).
`proof_artifacts.py acquire` loaded 196 books under composed artifact set
`f82a74c143d98e3c32e323287c04851c80fb32ca2b5fac180d6c18c520b8e617`,
source identity `8ad89085a2503ea09e94cec214c308d9d08ecd91592131a20500e986666a7a14`.
The resulting full developer `fn-host-developer.core` SHA-256 is
`a4139a01bef7a22d251adf0038f98bc91ef81a6a3d69676bfc87024faac6daa8`.

With the bundled OpenSSL 3.5.8 library on `LD_LIBRARY_PATH`, a fresh
`bp-node dispatch` opened one shared BP/Store owner and exited zero after
recovering zero held records and zero outbound jobs. On this image, all 22
receive/contact/recovery native tests passed (the first run's four legacy
`bp-app` tests failed during setup because `FN_ACL2` was omitted); rerunning
only those four with the exact ACL2 launcher passed. The two exact
[logs](native-bp-a3-2026-09-23/regression.log) and
[app log](native-bp-a3-2026-09-23/bp-app-regression.log) preserve that
distinction. A two-node `bp-node` application witness, process-death cuts,
and the authoritative `:handed-off` projection remain open at this image cut.
