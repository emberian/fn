# W15 native BP receive integrity evidence

The tested source is commit
`3241cdd3698af790ea43d1b0a62c640b15e6af75` on
`w15/bp-receive-integrity`.  The native image was built on `persvati` from
the same source snapshot before the final test-only commit; the five build
input hashes below equal the final local files, and the final test file was
then copied byte-for-byte to that snapshot before the recorded run.  Nothing
was deployed.

The shared immutable publisher consumed by this packet is the API frozen at
`219205f`; its files were imported in the separate prerequisite commit
`2ea2f15`.  The W15 receive behavior is in `a100fc1`, its proof repair is in
`61e6a7d`, and its restart witness is in `3241cdd`.

## ACL2 certification

The two new roots were certified as separate dependency-ordered jobs on
`persvati`, ACL2 8.7 / SBCL 2.6.8:

| Farm run | Root | Result | Wall time | Archived manifest |
|---|---|---:|---:|---|
| `run-20260921T090337Z-cc96` | `books/bp-receive-evidence` | passed | 3.633 s | `planning/evidence/manifests/certify-20260921T090340Z-1883423.json` |
| `run-20260921T090355Z-739d` | `tests/acl2/bp-receive-evidence-tests` | passed | 1.590 s | `planning/evidence/manifests/certify-20260921T090359Z-1885985.json` |

The manifests have SHA-256 digests
`2176ed75182d44ee91100c185b745059053d3c6e61e88e078ce73df81c35d978`
and
`c49095f9e8ee999694fdb5e14740d1b7119d20a09a33aa5a7a8b0cb427a6bcb0`,
respectively.  The preexisting decimal name codec and the shared application
journal prerequisite were also completed as bounded one-root farm jobs
`run-20260921T090213Z-729f` and `run-20260921T090428Z-ca85`; they are not
claimed as new W15 proof results.

## Native image and runtime tests

The saved DTN image was built on `persvati` with:

```sh
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
FN_NATIVE_BUILD=host/native/build-dtn.lisp \
FN_NATIVE_IMAGE=build/fn-host-dtn \
sh tools/build_native_host.sh
```

It exited zero and produced a 269 MiB core.  The launcher SHA-256 is
`0b676efe0da19d5c8789438e931683d3fdeb4861db0a1d7ca856c0301cf1464f`;
the 281,508,232-byte core is
`c8712cc46818d53b00c397f9bb70a9658ece0793057e33c5bbb55c83d4920432`.
The archived build transcript
`planning/evidence/bp-receive-integrity-w15-2026-09-21/native-host-build.log`
has SHA-256
`0c069a7c2ae67f86db844601a9d66f38f9a76b9d33b3c32a0ce75cf822300212`.

The focused command was:

```sh
python3 -m unittest \
  tests.test_bp_receive_integrity_native \
  tests.test_bp_service_native -v
```

All eight tests passed in 11.341 seconds.  The archived transcript
`planning/evidence/bp-receive-integrity-w15-2026-09-21/native-tests.log`
has SHA-256
`846f376350bd8ceea5ce95507f1e5e1cda6673c95d4ade7847a2bccd790d2d08`.
The receive-specific cases exercised the production native paths and showed:

* two separate TCPCL sessions each delivered transfer ID 0 with different
  bytes; both exact byte strings remained under identities 0 and 1;
* an injected real `fnn-os-error` EIO at the immutable publisher's final
  directory barrier left the linked wire visible, returned exit 3, closed the
  listener, and permitted no second mutation in that process;
* restart repeated the evidence-directory recovery barriers, treated that
  wire-only identity as consumed, and published the next transfer as identity
  1 without replacing identity 0; and
* injected receive and lifecycle-send core faults remained exit 4 rather than
  being collapsed to article refusal or transport uncertainty.

The source hashes used by the image and tests are:

```text
490e4af7287adaf670967355b5d4964629cc0ef5da54f81fbd05b6ae38718606  books/bp-receive-evidence.lisp
cdd2427eb20e5db8b0059d9f340209e2caab5c8bbf30974d1ca7910ddb638540  host/bp-receive-evidence-host.lisp
f26c2de34c4d581201defbbf02f87d0da054fdafc778cc5220b99eea35fce424  host/native/bp.lisp
eab9ed97b99c9c1b168dbbe44cc8ca666b0ba4b289091dded27ab065fda59f9a  host/native/immutable-publish.lisp
af97f8ae4a33d88a3552aea926f9ebe4be335e85ceb9a3f4e129790397a225af  tests/test_bp_receive_integrity_native.py
```

The SHA-256 over the ordered `sha256  path\n` artifact list comprising the
launcher, core, build log, the five source files above, and native test log is
`4466ad0d6578f59cddd0dc431ba55cadfbc41612b414f5339308fda9f477ae9f`.

## Scope

The model makes an immutable `.wire` publication the durable allocation of a
receive-evidence identity.  Recovery accepts only a complete, bounded,
contiguous ACL2-rendered namespace after successful parent and evidence
directory barriers.  A retained wire consumes its identity even when its
verdict sidecar is absent.  Legacy root-level `passive-*` evidence is retained
unchanged and is not authoritative for new allocation.

This evidence does not prove filesystem or hardware power-loss behavior, and
the exclusive spool lock constrains cooperating fn processes rather than an
external process that ignores the lock.  The packet does not close the
separate BP machine invariant/per-event cost obligations or the sequence
allocator's actual host-cut correspondence work.
