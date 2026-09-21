# Native owner connection-fault isolation — 2026-09-21

This packet implements the HST-005 boundary in the native owner.  Failures
inside the named receive/send/graceful-close envelope, before or after no
shared semantic mutation, become connection-local faults.  The worker then
applies the existing ACL2 `fn-owner-fault` transition for that connection and
keeps the service available.  Store indeterminacy, store/core faults, and any
unexpected condition escaping `fnn-owner-serialized` fence the service while
the owner mutex is still held.

## Source

- Final owned source: `652199d07ddf5f85211967443f29c4a4a5ed114b`, based directly on
  integrated main `117f4bbea2c6b598a4f47d141f7c3d6f31a1724d`.
- Owned commits: `2240264b` (runtime witnesses), `9484e1eb` (fault boundary),
  and `652199d0` (the witness respects a reader's pinned archive snapshot).
- Exact image source: `974bd287`, the same HST implementation over the frozen
  control/lifecycle source used for the image build.  The later final-source
  changes to this packet are test-only.
- Image SHA-256:
  `4ac990d34ba83e01c2cc0649aa671e74eae01bf89b80fe507514ef8424bc12f5`.
- Exact image-source SHA-256 values: `host/native/owner.lisp`
  `49b9c89c73989c22826c1208027abf08935c4fd0276cc3696a05dd162186b0d7`,
  `host/native/io.lisp`
  `f29a65eaba092ac31e7298fa13d0484f5850cd8140d5f031dd418ee6b3eea5f6`,
  and `host/native/control.lisp`
  `be157d902bb1d7d6de93ffccef7ca3723beeaccd75e329c363ec7ba7cb699857`.

## Certificate and image build

The absolute source origin was
`persvati:/home/ember/fn-lanes/w22-owner-fault-runtime`.  ACL2 was 8.7 over
SBCL 2.6.8.  The exact default profile validation command was:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
python3 tools/proof_artifacts.py validate --profile default \
  --acl2 $HOME/fn-tools/acl2-8.7/saved_acl2
```

It reported `profile=default image=build/fn-host roots=46 result=loaded`.
The source-pinned manifests are:

- `certify-20260921T104908Z-2887063.json`: 24-book control closure, exit 0,
  136.614 seconds, four jobs.
- `certify-20260921T105238Z-2922509.json`: 102-book exact-origin dependency
  repair, exit 0, 1019.522 seconds, four jobs.
- `certify-20260921T111025Z-3104899.json`: final host-only source sync root,
  exit 0, 1.258 seconds, one job.

The build command was:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
FN_NATIVE_LOG=build/owner-fault-isolation/native-build.log \
sh tools/build_native_host.sh
```

It exited 0, produced a 286 MiB `build/fn-host`, and neither the build log nor
stdout contains `Uncertified`, `ACL2 Error`, or `HARD ACL2 ERROR`.  Archived
SHA-256 values are `eefb07c5...619d` for `native-build.log` and
`d82448ef...e46f` for `native-build.stdout`.

These certificates cover the logical dependencies loaded by the image.  The
HST change itself is a native host composition boundary and is established by
the runtime witnesses below, not by claiming an ACL2 theorem about raw socket
exceptions.

## Runtime result

The terminal focused command was:

```text
FN_NATIVE_HOST=/home/ember/fn-lanes/w22-owner-fault-runtime/build/fn-host \
python3 -m unittest -v \
  tests.test_native_owner.NativeOwnerTests.test_reset_peer_does_not_stop_concurrent_writer_or_reader \
  tests.test_native_owner.NativeOwnerTests.test_local_handler_fault_uses_core_fault_and_preserves_other_clients \
  tests.test_native_owner.NativeOwnerTests.test_two_client_uncertainty_fences_before_later_mutation
```

Result: **3/3 passed in 0.592 seconds**.  The reset witness uses a real TCP RST.
The handler witness injects a plain error at the production receive call, so
the actual envelope must classify it; it does not signal the new condition
directly.  In both cases a client opened before the fault remains responsive,
a healthy writer commits, and a reader opened after the commit retrieves the
exact article.  The third witness reaches an ambiguous Store publication,
returns exit 3, fences all clients before mutex release, and proves a queued
later mutation is absent.  The archived focused log SHA-256 is
`c486f544...f0e0a`.

An earlier combined owner/control run is retained as negative integration
evidence: **5/13 passed, 8 failed in 903.228 seconds**.  Its control source
predated the final resource-lifecycle packet, one feed-restart case lacked an
`FN_ACL2` test-driver setting, and the two first-form HST witnesses incorrectly
asked a pre-commit pinned reader snapshot to expose a later article.  The last
error was corrected in `652199d0`; the three focused cases above then passed.
The full negative log SHA-256 is `7c8b75dd...dac1`.  It is not represented as
a passing combined gate.  The final control/lifecycle packet has separate
source-pinned 7/7 evidence from its owner.

## Limits

This packet does not activate outbound feed service, native peer ingress, TLS,
or a production raw fault-injection verb.  It does not claim a final-main
combined image gate.  The production local-fault classifier is deliberately
limited to bounded connection I/O outside `fnn-owner-serialized`; arbitrary
exceptions after shared mutation still fence globally.
