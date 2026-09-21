# W12 native BP sequence durability transcript

Source revision: `d2daed19244772d8194080c4aa71d61b3cb464ac` in
`/home/ember/fn-lanes/w12-bp-sequence` on persvati.  The source and image were
not deployed.

The DTN artifact acquisition first selected the one current set
`b0f61318acac7c2f8b770597231ceac9b545f0331a086445901f9c875699f726`, origin
`/home/ember/fn-lanes/w12-bp-sequence`, after ACL2 loaded its 103 declared
books without an uncertified warning.  It was populated by farm run
`run-20260921T065324Z-17f8` (`--jobs 4`, declared DTN runtime-root union,
exit 0); the relevant archived manifest is
`certify-20260921T065328Z-633554.json`.

Tooling was ACL2 Version 8.7 at
`/home/ember/fn-tools/acl2-8.7/saved_acl2`, SBCL 2.6.8, and Python 3.13.7.
The native build command was:

```sh
FN_ACL2=/home/ember/fn-tools/acl2-8.7/saved_acl2 \
FN_NATIVE_BUILD=host/native/build-dtn.lisp \
FN_NATIVE_IMAGE=build/fn-host-dtn \
FN_NATIVE_LOG=build/native-host-build-w12-barrier.log \
sh tools/build_native_host.sh
```

It built a 263M DTN-only core.  The executable SHA-256 was
`18087f1a421fde9e72c18c73a254391b69802ac5d58465dc52fcfa5db634e2e7`; the core
SHA-256 was
`547640fc31ea3da190d93f52b4b7f3dbe0cb5132d3af4f95e3dffb9d8f0a6fcb`.

The native fault regression command was:

```sh
python3 tests/bp-dtn7/run_fn_bp_sequence_durability.py \
  --image build/fn-host-dtn --work build/evidence-bp-sequence-barrier \
  --source-revision d2daed19244772d8194080c4aa71d61b3cb464ac \
  --artifact-set b0f61318acac7c2f
```

It first injected `FN_BP_TEST_FAIL_ROOT_PARENT_BARRIER=1` against an existing
journal.  That process exited uncertain (3) with `bp: injected journal root
parent barrier failure` and authored no bundle.  Two following independent
failed-connect sends with the same source and wall creation time 100 exited
with connection-refused fault code 4 only after respectively authoring
`(100, 0)` and `(100, 1)`.  Replacing `sequence/frontier.fnb` by a malformed
octet made the final process exit uncertain (3), report `bp: sequence frontier
cannot be recovered`, and author no bundle.

This is evidence for the native ordering and its injected parent-publication
cut.  It relies on filesystem staged-write and fsync semantics; it is neither
a hardware power-loss proof nor a proof of nonreuse over all crash traces.
