# Evidence: closure-consistent deployment artifacts (w12)

Date: 2026-09-21.  Lane revision at the remote sync:
`625159f175bc99fe5cf848094d2a469622abd45b`; the git archive-free remote
snapshot was `/tank/fn/lanes/w12-artifact-set` on hbox.  The source identity
computed over the selected image and deployed owner entry-point union was
`4bd9e029975a49b1d869813d97df0b7b831f8d95123593324914d7751514df6f`.

## The reproduced defect

The concrete production failure is recorded in
`planning/evidence/owner-survival-2026-09-21.md` section 7: a `served`
certificate required `nntp-auth` under the owner-survival origin while the
per-book cache installer had installed the same familiar book from the
auth-live origin, and ACL2 refused the include.  That worktree contained
certificates naming eight origins.

`tests/test_certs.py::ArtifactSetTests` reduces it to two current entries:
origin A holds `base`, origin B holds `mid`, and `mid` includes `base`.
`install_artifact_set` refuses to combine them and installs neither.  A
complete origin installs both.  `tests/test_proof_artifacts.py` then makes
the first complete set produce an ACL2 absolute-origin error, requires the
whole set to be rejected, and accepts the second only after its actual load
prints the ready marker.  An `Uncertified` warning is a separate rejecting
case.

## Box acquisition and bounded certification

Before the heavy run, hbox reported load averages `1.69 2.00 1.60`, 15 GiB
memory available, and 318 GiB free on `/tank/fn`; no fn certification or
native image build was found.  Another lane began a four-process narrow run
after this observation.  This lane stayed at the assigned maximum of four
jobs under `swarm-build`.

The first cache acquisition was intentionally allowed to fail:

```
python3 tools/proof_artifacts.py acquire --profile default \
  --root /tank/fn/lanes/w12-artifact-set --cache /tank/fn/certcache \
  --acl2 /tank/fn/acl2-8.7/saved_acl2
```

It reported `no current artifact set matches this ACL2 toolchain` and
installed nothing.  It did not reconstruct a set from individually current
cache entries.

`--profile default` names `host/native/build.lisp` and `build/fn-host`
explicitly.  Its session script and loaded host files declare 22 certificate
roots; their local include union is 89 books.  Only that image closure was
certified first:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_CERT_CACHE=/tank/fn/certcache FN_CERT_ORIGIN_KIND=run \
swarm-build python3 tools/certify_books.py --jobs 4 \
  --timeout-seconds 1800 --closure \
  $(python3 tools/proof_artifacts.py roots --profile default)
```

Result: 89 of 89 passed in 250.038 seconds, with sources unchanged.  ACL2 was
8.7; executable SHA-256
`64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`.
The complete manifest is
`planning/evidence/manifests/certify-20260921T062525Z-1649086.json`.

The deployment also starts `tools/run_owner.py`.  Its ACL2 bridge loads
`host/owner-host.lisp`, so the profile parser follows that shipped host entry
point too.  On this revision it adds `books/owner-fault`; its 78-book closure
was certified on the same origin and executable with the same four-job cap:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_CERT_CACHE=/tank/fn/certcache FN_CERT_ORIGIN_KIND=run \
swarm-build python3 tools/certify_books.py --jobs 4 \
  --timeout-seconds 1800 --closure books/owner-fault
```

Result: 78 of 78 passed in 209.594 seconds, with sources unchanged.  Its
manifest is
`planning/evidence/manifests/certify-20260921T063623Z-1662559.json`.  The
two closures overlap; their deployment union is 96 books and 23 declared
roots.  Parsing the shipped owner host, instead of hardcoding only
`owner-fault`, means a later owner entry-point include such as `feed-journal`
also becomes part of the selected set.

## Actual coherent load and native build

Repeating the acquisition selected exactly one origin for the full 96-book
deployment union and loaded all 23 roots through ACL2:

```
attempt ab5fa9f8ae817b7d /tank/fn/lanes/w12-artifact-set: loaded
profile=default image=build/fn-host
artifact-set=ab5fa9f8ae817b7d82a7cb01c2da4bc7c8ba6b5fe73220871aa228d90a882290
origin=/tank/fn/lanes/w12-artifact-set books=96
source=4bd9e029975a49b1d869813d97df0b7b831f8d95123593324914d7751514df6f
toolchain=1fcb6ffbe061048b5212b58e6870c112e0ed261452ab5b1e39aa31d766b3a7bd
rejected=0
```

The native build named both sides of the selection rather than relying on
the script's defaults:

```
FN_NATIVE_BUILD=host/native/build.lisp \
FN_NATIVE_IMAGE=build/fn-host \
FN_NATIVE_LOG=build/native-host-build-w12-artifact-set.log \
swarm-build sh tools/build_native_host.sh
```

It produced `build/fn-host` and a 272,002,984-byte core.  The build log held
one `FN_NATIVE_BUILD_LOADED` marker and zero matches for `ACL2 Error`, `HARD
ACL2 ERROR`, `ABORTING from raw Lisp`, or `Uncertified`.  Image SHA-256 was
`b999b3d27f877b18293f5aa64fb60d56cd8e2e2213ef148f34a84eb39d5d2cd0`;
core SHA-256 was
`ffbdbaf9a56cc3b904f6ad3e93f37ddb76613ef2689fa51840a0c6edaaea6019`.

This is the default deployment image only.  The DTN-only declaration
(`host/native/build-dtn.lisp`, `build/fn-host-dtn`) is a separate explicit
profile and was neither acquired nor built in this run.

## Local validation

```
python3 -m unittest tests.test_certs tests.test_proof_artifacts \
  tests.test_deploy_gate tests.test_twonode_gate tests.test_inn_lab
```

All 97 tests passed in 75.044 seconds.  `make check` also exited zero.  Its
structural checks passed with the repository's recorded lint backlog; its
`host_check` explicitly skipped because `FN_ACL2` was unset locally.  The
hbox certification and load above are the ACL2 evidence for this batch.
