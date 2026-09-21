# W12 native BP sequence lock classification transcript

Source revision: `3a6b80ee2d3cf5cac1a99505774cd95cacf929bc` in the isolated
`/Users/ember/dev/fn/build/lanes/w12-bp-sequence` worktree.  Nothing was
deployed.

ACL2 was Version 8.7 from `/opt/homebrew/bin/acl2`, SBCL was 2.6.8, and Python
was 3.14.7.  The certified DTN artifact-set identifier supplied to the native
test was `b0f61318acac7c2f`; it covers the ACL2 runtime set, while this run
also compiles the current W12 host adapter source.

The native build command was:

```sh
FN_ACL2=/opt/homebrew/bin/acl2 \
FN_NATIVE_BUILD=host/native/build-dtn.lisp \
FN_NATIVE_IMAGE=build/fn-host-dtn \
FN_NATIVE_LOG=build/native-host-build-w12-lock.log \
sh tools/build_native_host.sh
```

It produced a 280M core.  The executable SHA-256 was
`cf17df95770fcc465e7438f349d7aca9b4712857761e477cbb602baed0814509`; the core
SHA-256 was
`5510e126dd6adf15192dff184188963ea03eb0ab5aa227b27823c46da4d89721`.

The exact regression command was:

```sh
python3 tests/bp-dtn7/run_fn_bp_sequence_durability.py \
  --image build/fn-host-dtn --work build/evidence-bp-sequence-lock \
  --source-revision 3a6b80ee2d3cf5cac1a99505774cd95cacf929bc \
  --artifact-set b0f61318acac7c2f
```

It passed.  The injected journal-root parent barrier exited uncertain (3) and
authored nothing.  The first failed-connect send authored `(100, 0)` and
exited fault (4).  The test then held an external `LOCK_EX|LOCK_NB` on
`sequence/frontier.lock`: the second process exited refused (1), reported
`bp: sequence frontier is already locked`, and authored nothing.  Releasing
the lock allowed the next failed-connect process to author `(100, 1)` and exit
fault (4).  A malformed frontier finally exited uncertain (3) without
authoring.

This validates the adapter's EAGAIN contention classification and the stated
host cut ordering.  Other `flock` errno paths are classified as native faults
by source inspection; this process test does not synthesize each such kernel
errno.  It remains conditional on the stated filesystem barrier semantics and
does not extend the sequence-only ACL2 theorem to W13 lifecycle persistence.
