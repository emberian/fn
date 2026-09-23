# Parsed-EID BP native retest at c1bb050b (2026-09-23)

The repaired image source is `c1bb050b` in the isolated hbox gate
`/tank/fn/gates/bp-admission-native-c1bb-20260923`. It includes the
`b450b36e` host caller repair: `fnn-bps-tcpcl-ingress` passes the parsed BP
peer EID into ACL2 session admission. The earlier `4f66e6b0` image and its
[nine-failure record](native-e2-bp-4f66-2026-09-23.md) remain unchanged.
Local and remote `git archive` file aggregates matched
`a28dba9fdacfadeed67c740a4199af25db33a95a1d4a5ef230e2579cb5ac0120`
over 2,641 source files before build. `0af5a6cf` later regenerated only the
ledger; no runtime or ACL2 source differs from this image.

The full incremental ACL2 run on `c1bb050b` passed with 531 cached and 9
new certificates; the archived manifest is
`planning/evidence/manifests/certify-20260923T223055Z-353949.json`.
Using `/tank/fn/certcache` and pinned w28 ACL2
(`/tank/fn/toolchains/w28/acl2-literal-4g`, SHA-256
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`),
[default acquisition](native-bp-admission-c1bb-logs/acquire-default.log)
composed 215 books and
[validation](native-bp-admission-c1bb-logs/validate-default.log) loaded 86
roots. `swarm-build` built the developer profile with matched OpenSSL 3.5.8;
its [build log](native-bp-admission-c1bb-logs/build-developer-run.log) is
preserved. The saved developer core SHA-256 is
`54ea34a870398e97d860e5d1e2149f02d61abd94a2fbabe90cab712f06a36f1a`.
No production image was rebuilt for this focused retest.

The exact source driver `tests/test_bp_node_native.py` (SHA-256
`3b6dcc2dd2b2f1f259fbf1785a5293ca9d5e9c7b5806cb2548795e23bbf7a1ea`)
ran on hbox under `swarm-build` with
`LD_LIBRARY_PATH=/tank/fn/toolchains/openssl-3.5.8/lib`,
`FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g`,
`FN_NATIVE_SOURCE_ROOT=$PWD`,
`FN_NATIVE_DEVELOPER_HOST=$PWD/build/fn-host-developer`, and `PYTHONPATH=$PWD`:

`python3 -m unittest tests.test_bp_node_native -v`

The [complete log](native-bp-admission-c1bb-logs/test-bp-node-native.log)
records **11/11 passed in 159.310 s**. This includes admitted request and
receipt paths, absent-trust refusals, wrong-peer refusal, and FNRJ/kind-5,
kind-7, outbox, and process-death/uncertainty scenarios. The result closes
the specific native regression seen on `4f66e6b0`: a parsed admission EID
now yields the configured principal, allowing the outer trust decision and
the serialized current-config recheck to reach application commitment.
It is saved-image behavioral evidence for these synthetic fixtures, not
an assertion about default authenticated transport peers or live service.
No live node, service or Store path was touched. E2 and topic suites were
already exercised on the earlier source and were not rerun on this repair
image.
