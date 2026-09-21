# Native owner integrated gate, 2026-09-21

This evidence fixes the tested source at
`03eb3ba34cc150d8cde63de656558f7cb3bd18b8` and the persvati source origin at
`/home/ember/fn-lanes/w13-owner-integrated-gate`.  The remote farm copy has no
usable Git metadata, so the certification manifest's per-book source digests
and the copied key-source digests are the origin check.  The latter match the
same files in the named local revision byte for byte.

## Certification

Farm run `run-20260921T095031Z-5cf4` certified the 42-root default profile,
34-root DTN profile, and eight focused test roots as one closure.  The exact
command was:

```text
python3 tools/farm.py submit persvati $(cat build/owner-integrated-gate/certify-roots.txt) --closure --jobs 4 --timeout-seconds 3600 --remote-root /home/ember/fn-lanes/w13-owner-integrated-gate
```

The terminal manifest is
`planning/evidence/manifests/certify-20260921T095039Z-2322081.json` (SHA-256
`37845b69e98cc15dc4a75117402f678007a447fd25dac01c6127da0732e1c150`).
It reports `passed`, 139 books from 50 requested roots, no book failures,
990.819 seconds wall time, four effective jobs, ACL2 8.7 on SBCL 2.6.8,
Python 3.13.7, and saved ACL2 executable SHA-256
`c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163`.
It contains 139 source digests and 139 certificate digests.

The first local publication attempt after the remote exit-0 result lost a
race renaming one shared certificate-cache temporary file.  Waiting on the
same completed farm handle again installed the already-produced 138 missing
cache entries and archived the manifest.  No certification job was rerun and
the manifest records the remote terminal result.

On the unchanged source origin, both artifact profiles accepted the installed
certificates:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 python3 tools/proof_artifacts.py validate --profile default --acl2 $HOME/fn-tools/acl2-8.7/saved_acl2
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 python3 tools/proof_artifacts.py validate --profile dtn --acl2 $HOME/fn-tools/acl2-8.7/saved_acl2
```

The results were `profile=default image=build/fn-host roots=42 result=loaded`
and `profile=dtn image=build/fn-host-dtn roots=34 result=loaded`.

## Native images and runtime tests

The same persvati origin built both images without an uncertified, missing, or
stale-certificate diagnostic:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 FN_NATIVE_LOG=build/owner-integrated-gate/native-build-default.log sh tools/build_native_host.sh
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 FN_NATIVE_BUILD=host/native/build-dtn.lisp FN_NATIVE_IMAGE=build/fn-host-dtn FN_NATIVE_LOG=build/owner-integrated-gate/native-build-dtn.log sh tools/build_native_host.sh
```

The default image core is 293,439,064 bytes with SHA-256
`9a904101f03d56bb9eeb1a747ee9dc20b054998e5923d8e70cb030171850e7a3`.
The DTN image core is 277,476,696 bytes with SHA-256
`31d02f5260cae6010f5d7ad0825c9ba1c3713db6fd183a1f2e937fccf2bc71a7`.
Launcher and core digests are all recorded in `artifact-digests.log`.

The default image passed 20 tests in 34.910 seconds:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 FN_NATIVE_HOST=$PWD/build/fn-host python3 -m unittest -v tests.test_native_owner tests.test_native_operator_cli tests.test_native_recovery tests.test_native_checkpoint
```

The exercised paths include ordinary disconnect isolation, the two-client
uncertain-publication fence, durable feed-intent reconciliation after restart,
the 9 KiB CRLF article through native POST and readback, bounded native
operator input classification, bounded recovery, and all native checkpoint
crash cuts represented by that test module.

The DTN image passed 11 tests in 4.021 seconds:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 python3 -m unittest -v tests.test_bp_receive_integrity_native tests.test_native_app_journal
```

These tests retain distinct core-fault and uncertain-publication outcomes,
preserve two exact BP wire values when transfer numbers repeat across
sessions, block later mutation after uncertainty, reopen durable application
journal work, and reject publication through read-only or fenced Stores.

A separate public-entry loopback witness initialized a native Store, ran
`build/fn-host --fn operator CONFIG run --once`, connected to its ACL2-selected
IPv4 loopback endpoint, observed NNTP `200`, sent `QUIT`, observed `205`, and
then observed native exit 0 with `accepted operator run`.  Python was only the
external test driver; the running service and Store were the saved Lisp+ACL2
image.

## Scope

This checkpoint supports the tested default and DTN native image composition;
it is not a complete-v0 or deployment claim.  The frozen source precedes the
native auth, local-control, outbound-feed worker, and ACL2 listener-address
successors.  Its operator supports the recorded run/status/recover surface;
native shared submission remains unavailable there.  Configured TLS/auth and
full timer/feed service parity are outside this checkpoint.

The frozen owner globally fences serious conditions.  The future
HST-005/PRF-040 split between attributable unexpected connection-local faults
and shared semantic/core/persistence faults remains open.  Its SIGTERM path is
also the pre-U12 abortive path; orderly active-client signal shutdown and
immediate reopen belong to the separate lifecycle successor.  The posting
permission and agent/path-identity configuration convergence is not claimed by
this evidence.

Raw logs and source/tool digests are under
`planning/evidence/native-owner-integrated-2026-09-21/`.
