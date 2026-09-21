# Native AUTHINFO runtime evidence — 2026-09-21

This is a path-preserving continuation of frozen owner source
`03eb3ba34cc150d8cde63de656558f7cb3bd18b8` at
`persvati:/home/ember/fn-lanes/w13-owner-integrated-gate`.  The frozen base is
recorded separately by `run-20260921T095031Z-5cf4` and
`certify-20260921T095039Z-2322081.json`.  After that gate finished, the native
auth changes through local commit `7e6737d` were applied at the same full book
name.  The owner preflight additions already present in
`tests/acl2/native-operator-host-tests.lisp` were retained.

Because the farm continuation is an rsynced tree whose `.git` file names the
macOS repository, its source identity is the manifest's per-file SHA-256 map,
not a remote Git claim.  In particular:

* `books/native-auth-profile.lisp`:
  `01655a8d189416e5fca4af3ec4c9e4ebab7f6ba9282ec030a451aa5ada809543`
* `books/native-config.lisp`:
  `8a9909247789c2311c81ffa8f1d2001c89454b57e6517446076c77e4aae79d54`
* `books/native-operator.lisp`:
  `2d9f7319eeea90bde752a8131534b603c71ad62db2e860f0bd51e1195407f57d`
* `tests/acl2/native-auth-profile-tests.lisp`:
  `898a6b5354527dcb6bce22edbc634abb130f3ab67cdc827061a9930287d97f79`
* `tests/acl2/native-operator-host-tests.lisp`:
  `da657444adba3318211c15002690b0dafd2be84b950dd34b91144b6cf710ad95`
* raw `host/native/auth.lisp`:
  `233b2db522acc0dcd1f813cafff87fdd73a904c397c712592c69140c1045bcd3`
* runtime test `tests/test_native_auth.py`:
  `b99ff5be00e34182a7f3223039d9c454166eff3671ffc14e0b34bce3e23ffba0`

The complete certified-source map is in `certify-manifest.json`.

## Certification and build

The exact certification command was:

```sh
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
FN_ACL2_TIMEOUT_SECONDS=1800 FN_CERT_CACHE=$HOME/fn-certcache \
FN_CERT_ORIGIN_KIND=run python3 tools/certify_books.py --jobs 4 --closure \
  books/native-auth-profile books/native-config books/native-operator \
  tests/acl2/native-auth-profile-tests tests/acl2/native-auth-host-tests \
  tests/acl2/native-config-tests tests/acl2/native-operator-host-tests
```

It passed as `certify-20260921T101518Z-2561161`, from
2026-09-21T10:15:18Z through 10:18:46Z (207.291 seconds).  The toolchain was
ACL2 8.7 on SBCL 2.6.8 with Python 3.13.7; saved ACL2 SHA-256 was
`c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163`.

The exact artifact-set check was:

```sh
python3 tools/proof_artifacts.py validate --profile default \
  --acl2 $HOME/fn-tools/acl2-8.7/saved_acl2
```

It returned `profile=default image=build/fn-host roots=43 result=loaded`.
The image was then built with:

```sh
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
FN_NATIVE_LOG=build/native-auth-continuation/native-build-core-fix.log \
  sh tools/build_native_host.sh
```

The builder exited 0 and reported a 281M core.  `native-build.log` contains no
ACL2 error, uncertified-book, or failure marker.  The resulting artifacts are:

* `build/fn-host`: `acc73b70c0112b7cceaba8d280f81e369db5ea931babb303a038fdf13f1daf6d`
* `build/fn-host.core`: `2abea9e40160956bc8656cdedee64a138959afc3d398fffe4d0c72c00404a89c`

## Runtime results

With both executable paths pinned:

```sh
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
FN_NATIVE_HOST=$PWD/build/fn-host \
  python3 -m unittest -v tests.test_native_auth
```

all 3 tests passed in 2.336 seconds.  The generated canonical credential gated
the reader before login, rejected a wrong password, accepted the generated
password, and allowed `GROUP`; `IHAVE` remained `502` on the reader path.
Legacy cleartext credentials refused before listen with the refused exit, and
protected-only refused before listen as an unsupported profile because no TLS
facility was installed.

The regression command was:

```sh
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
FN_NATIVE_HOST=$PWD/build/fn-host \
  python3 -m unittest -v tests.test_native_operator_cli tests.test_native_owner
```

all 9 tests passed in 24.678 seconds.

The first runtime invocation lacked `FN_ACL2`, so operator-side test enrollment
failed before service start; `preflight-no-acl2.log` records it.  The next run
found that raw auth used `fnn-core-state` for a state-free wrapper; the exact
failure is retained in `preflight-core-state-failure.log`.  Commit `7e6737d`
changed that call to `fnn-core`; the image and passing logs above are after the
fix.

## Scope

These results cover the loopback native operator/owner image and its startup
credential snapshot.  They do not establish TLS, public listening, live
credential reload or generation switching, native configured-peer admission,
orderly SIGTERM parity, a D09 cryptosuite choice, or properties of storage and
network hardware.
