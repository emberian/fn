The source-matched `bc9be7ec` developer image at
`/tank/fn/gates/reader-clone-poll-native-bc9-20260923/build/fn-host-developer`
(SHA-256 `0261d56337f1c8278f29e1190ef34c011f5920b6a0df104c87fad69e8537fe5f`)
failed the signed composite poll test before submission. The frozen driver
`tests/test_native_consumer_e2.py` had SHA-256
`3ae5005836eebecbe586e12ccc8dfdaff9d05c20615618dcb068d4297afbe92f`.
The invocation used the `FN_RUN_CONSUMER_E2E=1` and
`FN_RUN_CONSUMER_POLL_E2E=1` gates, pinned w28 ACL2 and OpenSSL 3.5.8, and the
public `tests/fixtures/dregg-e1/source.eml` fixture. It exited 1 after the
CLI returned fault exit 4, `ACL2 refused local consumer request`; the exact
captured output is `native-e2-poll-bc9-original.log` (SHA-256
`51eaa17c3428ddad9b60342230d69440ac4066ade58fddd4ec1f7bf386e64d65`).
This is negative runtime evidence, not a certification failure. The CLI passed
its poll cursor output filename as the second request argument although
`fn-ncl-request-encode` requires nil there.
