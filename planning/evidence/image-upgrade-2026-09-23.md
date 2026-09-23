# Relocatable image and isolated upgrade evidence — 2026-09-23

The packaging lane began at `df5097b6`. It changed shell packaging and runbooks,
not ACL2 books or the native semantic core. The real image used below was built
from `2e53fae2` and recorded under the `da5fd8cb` node evidence; these checks
exercise relocation of that existing image, not a newly certified image.

On hbox, `packaging/freeze-native-image.sh` copied the three saved cores from
`/tank/fn/gates/freeze-dev-2e53fae2/build` into
`/tank/fn/gates/takeover-image-upgrade/da5fd8cb-relocatable-v2`. The script
preserved each generated SBCL invocation's runtime options and restart form,
replacing only runtime, core and support paths. `sha256sum -c image.sha256`
passed. Production core SHA-256 was
`a6e5437e23fc74a743f07c21e46e7876b42f132de2a558f9db4142a781ab5cca`,
matching both the original build and the earlier frozen copy. Developer and DTN
core hashes were `c53ca0cc7cea8ddbbe0796aebaec3762acb88d8b25f4882b583f8318bb498fca`
and `e6d236a561933f214742ee804553d4d2e3b11b19f514ec36154a394249b6fb4d`.
The copied SBCL binary hash was
`b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`;
libcrypto.so.3 `14d40ec690d4d2e4d49f95d9509ec8b3112c39089f9ad11fa8bde42796b99190`,
libssl.so.3 `bb2d12bec3c53f997b5edf5e4ac3ed24584412008070eb731830f29896004ed4`,
and libsodium.so.23 `7de3e60f9f7df83a7299aa1b8b7a88013ace3233f70c9f63698dd331781d557e`.
The OpenSSL pair came from `/tank/fn/toolchains/openssl-3.5.8`.

With `FN_OPENSSL_PREFIX` unset, the relocated `fn-host --fn reader invalid-port
1 -` returned exit 5 and `reader is available only in the developer image`.
`strace -f -e openat` recorded the opened core as
`/tank/fn/gates/takeover-image-upgrade/da5fd8cb-relocatable-v2/fn-host.core`.
A production install under
`/tank/fn/gates/takeover-image-upgrade/fixture/releases/test` also returned
exit 5; its trace opened its own
`.../fixture/releases/test/libexec/fn/fn-host.core`, with the same core hash.
No path under `/tank/fn/node` was modified.

Locally on Darwin, `sh tests/test_frozen_image_upgrade.sh` passed. The fixture
moves away the original build and runtime before launching all three frozen
variants; stages an installation; checks a successful switch; checks that a
failed health check rolls back to the old executable; verifies unchanged
config, TLS key/cert, credentials and article fixture bytes; and rejects a
modified core before service stop. `sh tests/test_native_distribution.sh` and
`make check` passed. The fixture runtime models the launch and profile result,
not native article service behavior. A live service upgrade, crash during the
symlink switch, power loss, or compatibility of a future Store schema was not
tested. The upgrade tool now requires an operator compatibility assertion
because a new image may commit Store bytes before a failed health check;
rollback of the executable cannot undo those writes. The fixture confirms
staged service templates name their final release path. The actual hbox node continues running its earlier versioned unit.
