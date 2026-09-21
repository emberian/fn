# First wide native-service qualification batch

Frozen input: `f7190d6914f140dedff1417831529cf748837930`, retained locally in
`build/lanes/w25-native-freeze-f7190d69`. Farm handle:
`run-20260921T161741Z-6d04`, persvati origin
`/home/ember/fn-gates/freeze-f7190d69`.

The selected roots were the union of `proof_artifacts.profile_roots` for default
and DTN images, plus the native administration/configuration observation,
STARTTLS prefix, owner feed port, BP fast application/authored-wire/lifecycle
and native byte-correspondence test roots. The exact selection, source digests,
ACL2/SBCL versions, invocation and per-root results are in the archived manifest
`planning/evidence/manifests/certify-20260921T161747Z-1591345.json`.

The task-local literal launcher fixed the SBCL runtime/core paths and proof
startup, bounded each Lisp heap to 8192 MiB, and ran four workers with a
900-second per-root timeout. Its qualified core SHA-256 is
`1bc67f611886a0898641bbb0a67a38baddc6b800c1c31a1d757d26e10eda3ffd`;
its runtime SHA-256 is
`b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`.
The installed toolchain was not modified. Launcher hashes and proof environment
are separately recorded in the manifest.

The batch failed: `books/native-admin` used `fn-cfg-peer-make` without including
`peer-config`, producing a translation error. Configuration-observation and
operator roots depending on it consequently failed to load. Successful
independent certificates were retained; no image/runtime success is claimed.

The repair snapshot `55e6d00a` adds that dependency and totalizes arithmetic in
configuration observation. It is running under handle
`run-20260921T163612Z-b31e`, reusing the same qualified toolchain and certificate
origin after the original manifest/logs were harvested. The origin directory's
name remains the earlier revision; the new manifest's source digests identify
its actual input. Its result and subsequent image/runtime results remain to be
recorded separately.
