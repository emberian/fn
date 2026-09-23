# Two-host protected NNTP scratch gate: image relocation failure

The attempted subject was the native protected NNTP gate in
`tools/native_two_host_protected_gate.py` at gate revision `4ae16d8a`, using
root's qualified source `329a51a23f08e42904d4e0894c94ef5dc243d17e`.
Root reported the 466-book certification manifest ending `175847` and four
successful native image builds. This record covers the subsequent hbox to
persvati scratch copy and gate attempt; it is **not** a two-host pass.

The hbox frozen directory was
`/tank/fn/gates/takeover-v0-image-329a51a2/build/images/329a51a23f08e42904d4e0894c94ef5dc243d17e`.
The entire directory (60 regular files, 1,280,145,797 logical bytes) was
copied with `rsync -a` through local `build/two-host-protected-stage-329a51a2/image/`
to persvati
`/home/ember/fn-gates/two-host-protected-329a51a2/image/`. The 58 entries
in `image.sha256` passed `sha256sum -c` on hbox and persvati and the
equivalent `shasum -a 256 -c` on the local copy. The manifest itself was
`e125bf0a6ca14c3799394ce896a371a087d162a43385ff45ba1a72417b823868`.
The four measured SHA-256 values were identical on both hosts:

| Artifact | SHA-256 |
| --- | --- |
| `fn-host` launcher | `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505` |
| `fn-host.core` | `7b00b3bf568f88e7f87b2d1ef2d801d45c248758424685f14ea804d3da9d6320` |
| `runtime/sbcl` | `b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5` |
| `build-source.sha256` | `2d6caf8f56b4195f2293ccbc26477d535a218a97f3d1a246ff861646f0df1c7c` |

The gate used `--host-a hbox`, `--host-b persvati`, each absolute scratch
`fn-host` path, `--source` set to the full revision above, all eight measured
artifact SHA-256 arguments, and `--timeout 300`. Its output is
[two-host-protected-329a51a2-failure.log](two-host-protected-329a51a2-failure.log)
(SHA-256 `c9b9f7b1231d653fcb316fe1ad97fe862314ce9cf2635150c62f70b83764524a`).
Hbox store initialization succeeded. Persvati store initialization exited 1
before either owner started:

> Error opening shared object
> `/tank/fn/toolchains/openssl-3.5.8/lib/libcrypto.so.3`: No such file or directory.

The frozen launcher points `FN_OPENSSL_PREFIX` to its bundled `openssl/`
directory, and those files passed the image hash check. However,
`host/native/build.lisp` calls `fnn-hsig-initialize` before saving the core;
`host/native/tls.lisp` records the selected absolute OpenSSL pair in
`*fnn-tls-pinned-libraries*` and deliberately preserves it across restart.
The saved image therefore attempts the hbox build path on persvati before the
scratch gate can exercise NNTP. This is a native image relocation limitation,
not evidence about two-host authentication, delivery, or rejection behavior.

The gate's cleanup removed its `/tmp/fn-protected-329a51a23f08-*` roots on
both hosts; a `find` on both returned none. No live `/tank/fn/node` store was
used. A new image qualification or a process-local mapping of the recorded
build path would need separate evidence before rerunning this gate.
