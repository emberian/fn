# W15 native existing-store recovery evidence

## Subject and source boundary

This packet is the existing-store recovery surface at source revision
`f2e6545` (`proof: admit staging observation bound`), following
`300b984` (`native: recover staging through ACL2 policy`).  It does not extend
fresh initialization or make an `EEXIST`/retry claim.

The native host calls `fnn-acquire` in
`host/native/io.lisp`, which checks `root/`, `transactions/`, and `staging/`
before locking.  `fnn-recover` invokes `fnn-sweep-staging` only after its
existing replay and five success barriers.  The bridge sends the bounded
observation to the executable ACL2 subject `fn-sn-sweep-staging`, via
`fn-store-sn-sweep-staging-list`; it does not reproduce the stage-name decision
in raw Lisp.  The ACL2 limit is `fn-sn-staging-observation-limit`, presently
64, and the raw directory helper faults when the next entry would exceed it.

The earlier differential report that native recovery accepted a missing
`staging/` directory was stale-image evidence: current `fnn-acquire` already
calls `fnn-safe-directory` for that directory.  The source-pinned run below
reproduces the case with exit 4 for both Python and native.

## ACL2 result

On hbox, the owned closure was submitted with:

```
python3 tools/farm.py --jobs 2 --closure --timeout-seconds 1200 \
  --root "$PWD" --remote-root /tank/fn/lanes/w15-native-recovery-fidelity \
  submit hbox books/store-sweep tests/acl2/store-sweep-tests
```

Run `run-20260921T085524Z-890a` completed successfully.  Its final manifest is
[certify-20260921T085527Z-1892190.json](manifests/certify-20260921T085527Z-1892190.json)
(SHA-256 `421182d34995aebc441ad31a4a44814c5238041dc6e51d6f1f5e6757a30cd326`).
All 32 closure roots, including `books/store-sweep` and
`tests/acl2/store-sweep-tests`, passed under ACL2 8.7 at
`/tank/fn/acl2-8.7/saved_acl2` (executable SHA-256
`64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`).

This is a source-identified result rather than a remote Git assertion: the
farm worktree is synchronized by rsync and retains a `.git` pointer unsuitable
for an independent remote revision query.  The manifest records the certified
source closure.  The changed subject digests were `books/store-sweep.lisp`
`2edb3ca43805fccba029d7ac8dd2bd2848ba19f234c890ba80a8345e5fd58a35`,
`host/store-node-host.lisp`
`d76be8905b1c04659c1ff5568c5f74519f039c9898ce06324ad444fc2796b973`,
and `host/native/io.lisp`
`4fd0d18782f4ccdfa0df13f3c7b9fbff477392369584ccf70fde8609b665fda3`.

## Native runtime result

The same hbox source was built explicitly with:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_BUILD=host/native/build.lisp \
FN_NATIVE_IMAGE=build/fn-host \
FN_NATIVE_LOG=build/native-host-build-w15-recovery.log \
sh tools/build_native_host.sh
```

The resulting launcher SHA-256 was
`8969c11b08d46c133bec7a406ae214760831ab7b7d0cc10178fbb35cdf5a9743` and
core SHA-256 was
`c3bbb7b3cf83e573f4eb56ba8b632659abd5d2e3f20e9bbdc3773097140180f3`.
The full build output is
[native-recovery-w15-2026-09-21-build.log](native-recovery-w15-2026-09-21-build.log)
(SHA-256 `d43cb8a9a3303eb0da8809a68e157e1cd9e26e3a1f315195eebd08be7347955f`).

With that image:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 FN_NATIVE_HOST="$PWD/build/fn-host" \
python3 -m unittest tests.test_native_recovery \
  tests.test_native_storage_codec tests.test_native_initializer_fidelity -v
```

passed 20 tests in 35.548 seconds.  The log is
[native-recovery-w15-2026-09-21-tests.log](native-recovery-w15-2026-09-21-tests.log)
(SHA-256 `3d6eccd4de1475bf5940474f2c07d48bcda9c0c3219d5de9878dc26da75b532d`).
The recovery-specific cases show: missing staging faults; only ACL2-selected
`.stage-` names are removed while an unknown name remains; the 65th entry faults
before cleanup; an injected error *after* a successful unlink yields uncertain
exit 3; and `SIGKILL` after one unlink is process death, after which a new
process observes and completes cleanup.  The injected error is a developer seam
for the post-success cut, not evidence that a platform `EIO` occurs after an
unlink.

`python3 tests/native_differential.py` against the same image checked 40
scenarios.  The missing-staging case now agrees at exit 4.  Its only finding is
recovery stdout: Python contains `checkpoint=none`, while this frozen native
image lacks the checkpoint module.  The exact output is
[native-recovery-w15-2026-09-21-differential.log](native-recovery-w15-2026-09-21-differential.log)
(SHA-256 `1f29fd16ff642c4499dbf45487d667014286ef2739cc5f7c71ee549867b95f73`).
That is a live integration gap owned by the checkpoint packet; it is neither
suppressed nor treated as recovery equivalence.

## Limits

The policy proves and executes only the bounded staging-name decision.  It does
not prove a physical filesystem correspondence, reconcile arbitrary external
namespace races, establish power-loss behavior, or cover all existing/retry
open paths.  Checkpoint reporting must be integrated and the differential rerun
against that integrated image.
