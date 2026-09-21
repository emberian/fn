# W18 native initializer composition evidence

## Subject and scope

The host subject is `fnn-command-init` -> `fnn-initialize` -> `fnn-acquire`
in `host/native/io.lisp`, at packet head `e62abd6`.  The preceding executable
model commits are `c1663c0` and `a993623`; the final negative witness is
`8f161db`.  This packet covers current native initialization over a fresh
store, an existing immutable root namespace, and one interrupted-history
retry.  It does not establish an all-opening-path, physical power-loss, K0, or
recovery-sweep correspondence claim.

`fnn-publish-initial-file` now returns `:published` only after a new immutable
link and `:existing` only after the actual `link(2)` returned `EEXIST`.
A different link error is `fnn-indeterminate` (CLI exit 3), since that error
may follow an issued namespace operation.  A configuration-history entry that
appears after the empty enumeration is likewise uncertain; it is preserved
rather than silently adopted or deleted.

The executable byte-store extension is `:link-eexist`.  It invokes
`fn-bs-link` and continues only if that call returns `:eexist`; an unexpected
successful link and an issued `EIO` both stop the model trace.  The model has
separate programs for an existing valid store and for a retry after the
configuration-history barrier but before frontier publication.  Their input is
the observed pre-existing image after directory/lock validation, not the
fresh-input predicate or a desired postcondition.

## ACL2 evidence

On hbox, the full default-native-image closure was certified because this
packet changes `books/byte-store-programs.lisp`; reusing the old frozen
artifact would have mismatched book sources.  The invocation was:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_ACL2_TIMEOUT_SECONDS=1800 \
FN_CERT_CACHE=/home/hbox/.cache/fn-certs FN_CERT_ORIGIN_KIND=run \
swarm-build python3 tools/certify_books.py --jobs 4 --closure \
  $(python3 tools/proof_artifacts.py --profile default --root "$PWD" roots)
```

The resulting 118-book manifest is
[certify-20260921T093534Z-1966193.json](manifests/certify-20260921T093534Z-1966193.json)
(SHA-256 `8bfc4fe4abf5f6c0a10db20df89eb7fd890ae7dd052df9ccf767bc015fc368d5`),
with status `passed` under ACL2 8.7 at
`/tank/fn/acl2-8.7/saved_acl2` (SHA-256
`64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`).
`proof_artifacts.py acquire` then selected complete artifact set
`1a04057ebf95a5b05a5a73748b810c7e1bf2d991634704d85754d956604dccdf`,
source identity
`fcc8911fb04af8779d39f4d164d0ae828c3c420c0f171ef205e97a3e322ea0bc`, and
loaded all 118 books before native construction.

The final test-only witness certified as
[certify-20260921T095918Z-2002274.json](manifests/certify-20260921T095918Z-2002274.json)
(SHA-256 `16699a07f0f2b98fa6ac9e76d896bc05ba19a7eb5a90b06297206a43ffff75a6`) after the image run.  It checks that `(:eio . :issued)`
at `:link-eexist` stops rather than becoming the accepted `EEXIST` branch.

## Native runtime evidence

After acquisition, hbox built the host with:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_BUILD=host/native/build.lisp FN_NATIVE_IMAGE=build/fn-host \
FN_NATIVE_LOG=build/native-host-build-w18-initializer-composition.log \
sh tools/build_native_host.sh
```

The image SHA-256 is
`e1fbf8cb27d893ab93af45b17e4314f8ebe239b264b6b77a325367f25da9b749`.
The build output is
[native-initializer-composition-w18-2026-09-21-build.log](native-initializer-composition-w18-2026-09-21-build.log)
(SHA-256 `ed58288a0028648f9dcfa981be385a059c3b8e91f97c3742779dfc65fab20a68`).

The exact image ran:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 FN_NATIVE_HOST="$PWD/build/fn-host" \
python3 -m unittest tests.test_native_initializer_fidelity \
  tests.test_native_storage_codec -v
```

All 18 tests passed in 15.150 seconds.  The full output is
[native-initializer-composition-w18-2026-09-21-tests.log](native-initializer-composition-w18-2026-09-21-tests.log)
(SHA-256 `8f83d705dfe5f1d3d0d2f77372db886c78b1a8e6efb178f983d0b46da5eebb5d`).
The added runtime cases repeat a valid init through real root-metadata
`EEXIST` links, retry a new process killed after the history fence, kill a new
process after an actual config `EEXIST` return, and hold `writer.lock` while a
second initializer is refused.  The SIGKILL cases observe `-9`, so they are
process death rather than exception cleanup.

## Limits

The `EEXIST` runtime cases show the named host/model branch and selected
process restarts.  They do not qualify platform `EIO` behavior, arbitrary
external writers, lock fairness, filesystem crash images, or every preexisting
layout.  The link-error classification is conservative because the host cannot
observe whether the kernel issued the link.  The separate recovery staging
executor remains a plan/execution boundary and is not promoted here to an
every-cut physical-state theorem.
