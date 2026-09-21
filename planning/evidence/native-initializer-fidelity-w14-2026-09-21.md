# Native fresh-initializer fidelity runtime evidence — W14

This is runtime evidence for the native host subject
`fnn-command-init` -> `fnn-initialize` -> `fnn-acquire`; it does not prove a
whole-host correspondence theorem, K0, or any existing/EEXIST retry branch.

The source packet is local `w14/native-initializer` `0510fad`.  Its raw-I/O
commits were replayed without logical changes onto the native-codec frozen
source `452828c4` in the hbox evaluation worktree, producing evaluation HEAD
`fd4b06641a448afb046ee1c3aadae60e49198427`.  Before the replay,
`proof_artifacts.py acquire` selected the manifest-backed certificate artifact
set `881adbd15a1aaeac0e791f568be3504617e4a35f40c15eae11bd47a05dbc6a17`,
origin `/tank/fn/lanes/w13-native-storage-codec`, 102 books, source identity
`7884e3d276854f880c6a0d61f0418ec5f7bf4ac2d8c88fed0341ec64a6c4e65d`,
and ACL2 toolchain identity
`1fcb6ffbe061048b5212b58e6870c112e0ed261452ab5b1e39aa31d766b3a7bd`.
The producer relabelled its manifest-verified pairs as `origin-kind run`; no
certificate file was copied by hand.  The manifest is preserved as
`planning/evidence/manifests/certify-20260921T074821Z-1788915.json` (SHA-256
`a1cb268b77ff0804063f9dfc2ed345cb06d2e611aa503d538d55b55683fb2ecd`).

On hbox, after replaying the raw-I/O packet, the following passed:

```sh
python3 tools/proof_artifacts.py validate --profile default --root "$PWD" \
  --acl2 /tank/fn/acl2-8.7/saved_acl2 --timeout 1800
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 FN_NATIVE_BUILD=host/native/build.lisp \
  FN_NATIVE_IMAGE=build/fn-host \
  FN_NATIVE_LOG=build/native-host-build-w14-initializer.log \
  swarm-build sh tools/build_native_host.sh
swarm-build python3 -m unittest tests.test_native_initializer_fidelity -v
```

`validate` reported `roots=26 result=loaded`; the default image built with a
100M core.  The test run passed all seven cases: complete fresh init followed
by recovery in another process; post-history-fence EIO and restart faulting
before frontier publication; second configuration enumeration faulting instead
of becoming empty history; SIGKILL before metadata and at history both followed
by faulted restart; SIGKILL after frontier publication followed by successful
new-process recovery; and the complete source-map label check.  The SIGKILL
tests observe return code `-9`, so they are process death, not unwind cleanup
after a raised exception.

The built launcher SHA-256 is
`0455b75e5531a7f06ce8330dbe73ed30b055e91cd421f2fa8029b358eee2301f`; its
core is `9c35471d14511bf9580f2901ea06e3d95c83cc36ff43e2eea9a5e34f5726ee8e`.
The exact build log is
`planning/evidence/native-host-build-w14-initializer.log` (SHA-256
`93f9cd9267e40dc4bf73f053162fc3ede1ede925de1eb0636a0e74d805d05170`) and
the test log is `planning/evidence/native-initializer-fidelity-w14.log`
(SHA-256 `6fff0812300b79de2c81afc7b02ce98d7a738b4119f5e7cf719df2dd7dd090f6`).

Limits remain: the byte-program theorem is conditional and models the fresh
path only; this runtime evidence does not establish physical crash-image
qualification after SIGKILL, a full K0 preservation theorem, or behavior of
existing directories/locks, EEXIST publication, and load branches.
