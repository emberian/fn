# U09 native image entry profiles

## Contract

The default `tools/build_native_host.sh` build is the production image
`build/fn-host`. Its news service has one start entry:

```text
packaging/fn-native operator CONFIG run [--once]
```

That entry retains the existing ACL2 native-operator/configuration plan and
calls `fnn-owner-run-normalized`; the packaging shell does not parse or
recompute owner arguments. The production image does not register the raw
`owner` verb, and its raw `reader` branch refuses before parsing diagnostic
arguments. Public operator and existing BP/TCPCL/application registrations
remain loaded.

Tests that need raw owner fault injection or the socket/model differential
build a distinct developer image:

```text
FN_NATIVE_PROFILE=developer tools/build_native_host.sh
# build/fn-host-developer
```

`host/native/build.lisp` selects the profile immediately after loading the
common native I/O layer and before loading owner/operator modules. The value is
serialized in the saved core. A restart-time `FN_NATIVE_PROFILE` therefore
cannot enable diagnostics in a production image or hide them in a developer
image. An unknown profile stops the build before ACL2 runs.

`FN_NATIVE_DEVELOPER_HOST` selects a nondefault developer image for the owner
and served differential tests. `FN_NATIVE_HOST` continues to select the
production image used by the packaged operator and public native tests.

## Source and executable witnesses

`tests/test_native_image_profiles.py` always checks:

- production is the default and developer has a distinct default image path;
- image profile selection precedes owner and operator loading;
- raw owner uses developer-only registration and raw reader checks the same
  serialized profile before calling its diagnostic handler;
- the production build still loads operator, BP and BP-service modules;
- `packaging/fn-native` still defaults to `build/fn-host`.

When both saved images exist, the same test runs the boundary. Production
accepts configuration-free operator help, dispatches the BP verb, reports raw
owner as unknown, and reports raw reader as developer-only. The developer
image reaches both diagnostic dispatchers. This lane did not build the exact
images because the integrated native artifact gate is owned by the root batch;
the executable cases skip loudly until both images are supplied.

Targeted source checks on this lane passed. `tools/host_check.py` loaded the
changed `host/native/io.lisp` successfully. Its standalone check of
`host/native/owner.lisp` still stops earlier because the fresh ACL2 process has
not loaded the pre-existing `SB-BSD-SOCKETS` dependency; it did not reach this
packet's final registration form and is not reported as a pass.

On 2026-09-21, from base `910096914fe5f024bc1600f1ff09e63732fc906b`:

- `python3 -m unittest tests.test_native_image_profiles tests.test_native_owner tests.test_native_served_differential` ran six tests successfully and skipped four saved-image-dependent cases because neither exact profile image was present;
- `python3 -m py_compile` on the changed Python tests and benchmark passed;
- `sh -n tools/build_native_host.sh packaging/fn-native` and `git diff --check` passed;
- `python3 tools/check_scaffold.py` stopped only on the expected generated-ledger staleness after the host-source change (`planning/ledger.json: stale`); the root integration batch owns ledger regeneration.
