# Relocated native image and protected two-host gate

The qualified ACL2 book source was `329a51a23f08e42904d4e0894c94ef5dc243d17e`.
Root's 466-book certification is
`certify-20260923T175847Z-4039310.json` (SHA-256
`15e5615d9c2b0d6c0751d65f268ef7e6c25231c73e135caeebddd156ba9812ce`),
under `/tank/fn/toolchains/w28/acl2-literal-4g` on hbox. No ACL2 book was
changed for this image. The **core-build source** was scratch commit
`1836ed01cba287bea1633c6cd0c231443302de3f`: that qualified source plus
the canonical receipt fault cut `b12aa84f`, saved-image library fix
`17a79482`, and relocation test `516b0f8f`. The hbox scratch tree was
`/tank/fn/gates/relocated-native-1836ed01`; it carried the qualified 466
certificates from the base tree. These host/test changes did not earn a new
ACL2 certification claim.

Production and developer cores were built there with `swarm-build sh
tools/build_native_host.sh`, `FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g`,
`FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, and respectively
`FN_NATIVE_PROFILE=production` and `developer`. Both builds passed. The
build logs remain in the hbox scratch tree as `build/relocation-production.log`
(SHA-256 `0817be7f00f3ea3965a9cd2a31ffec1b72bd9a0df94d17668af2b2e5d0e393db`)
and `build/relocation-developer.log` (SHA-256
`34d03f6d7125691250bac874f649e7c4b843f497eaddc99251c6191df054163f`).
An initial production attempt without `FN_OPENSSL_PREFIX` failed its build-time
OpenSSL 3.5/ML-DSA check; it produced no accepted image and the prescribed
prefix was supplied for both successful builds.

The separate **freeze-tool source** was `5426057a7e1308f61ddf2f88b320ec5fca47192e`
(`packaging/freeze-native-image.sh` SHA-256
`7a76d24e82de1478f55a9071004288b0fa7ff1cec6a40398b091f29b3a415b81`).
Its explicit `FN_FREEZE_VARIANTS='fn-host fn-host-developer'` selection froze
only the two built images; its default still freezes the full variant set.
The frozen directory is
`/tank/fn/gates/relocated-native-1836ed01/build/images/1836ed01-production-pair`.
The whole 693,001,277-byte directory was copied by `rsync -a` through local
scratch to `/home/ember/fn-gates/relocated-native-1836ed01/image` on persvati.
All 54 `image.sha256` entries passed on hbox, local scratch and persvati.
The hbox build-time OpenSSL path was absent on persvati. The measured hashes
matched on both hosts:

| File | SHA-256 |
| --- | --- |
| `fn-host` | `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505` |
| `fn-host.core` | `d754a540c3a143caed67ffa1af6525565cf05b25f492d0aaeef60c547aa43281` |
| `fn-host-developer` | `e4eeefd290450e7497dade96e2c4089e0caacfa88f72c737f51a92b2f3b2ba18` |
| `fn-host-developer.core` | `501f11d68ecb1b1cff63a85e9049877c38aaa977ef0756d0f726a46cdfdab19b` |
| `runtime/sbcl` | `b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` |
| `build-source.sha256` | `2024599ca9c32ce3aec40fea27cdcc44d4a57e3b288467dce5482dd7567d579a` |
| `image.sha256` | `1c616f445932064958802e07beec10b4a04b5465e81df8caab792148570ed3b0` |

On persvati, `FN_RUN_RELOCATION_E2E=1` with the copied production launcher,
`FN_BUILD_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, and
`FN_TEST_OPENSSL=/usr/bin/openssl` ran
`python3 -m unittest tests.test_native_frozen_relocation -v`. Both cases
passed: actual store startup, ML-DSA-65 hybrid signing, a loopback STARTTLS
handshake, and refusal to initialize when the bundled OpenSSL pair is absent.
The [test log](relocated-native-1836ed01/relocation-test.log) has SHA-256
`ffd828243b1756777d526e8bb62a51435eb3912782d416383aacc780310d3423`.

The two-host gate used driver source `1bf073776feb2f1752aca20d833560ff9deb32e7`
(`tools/native_two_host_protected_gate.py` SHA-256
`44197b70404ac8fc915c78c2caeb1cc25c5fea59c3b70f61557a73e4f0dbac0f`),
full core-build source `1836ed01cba287bea1633c6cd0c231443302de3f`,
the absolute hbox/persvati launcher paths above, and the four measured
launcher/core/runtime/source-manifest hashes for each host. It passed:

```
PASS declared-source=1836ed01cba287bea1633c6cd0c231443302de3f hosts=hbox,persvati
```

The [gate log](relocated-native-1836ed01/two-host-gate.log) has SHA-256
`75907e704fb1ac942174a41a2010a6a989d9fbfa61a1aae3644c7427cc79e8ac`.
The [observations](relocated-native-1836ed01/two-host-observations.json)
(SHA-256 `3fe2adadb9ea7ccf35fefbbb450557b29ceec40bf85a52d882eee568eca3d0a3`)
record both owners' actual `/proc` runtime and core paths and hashes,
source and target article equality in both directions, a wrong outbound
password and unrelated CA refusing delivery while retaining journal evidence,
and delivery after the same queued obligation's credential or CA is restored.
An earlier gate comparison against the pre-injection POST input failed because
the source host adds `Path`, `Injection-Date`, and `Injection-Info`; the final
driver compares the exact served article on source and target while separately
checking the submitted body survives source injection. That changes the
observer, not the native images or acceptance decisions.

The unchanged `tests.test_bp_app_native` ran under `swarm-build` on hbox
against the targeted developer image with the same ACL2 and OpenSSL paths.
All four cases passed, including the canonical receipt decision namespace
fault. Its [log](relocated-native-1836ed01/bp-app-native.log) has SHA-256
`d533f71094b6c75166dfbc5765c8e30e617e071ed9a7ba8c49f6fa362036f6ad`.
All gate-created `/tmp/fn-protected-1836ed01cba2-*` roots were removed on
both hosts. No live `/tank/fn/node` path was used. This evidence covers the
named hosts, image bytes, TLS/ML-DSA operations and protected NNTP scenario;
it does not establish arbitrary-platform relocation, a live deployment or
full DTN/flight readiness.
