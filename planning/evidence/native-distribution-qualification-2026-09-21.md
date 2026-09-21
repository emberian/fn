# Native distribution qualification — 2026-09-21

This is installation and lifecycle evidence for the selected frozen production
image. It is not a parity, peering, certification, or deployment claim.

## Inputs

- host: `persvati`, Linux 6.17.0-40-generic x86-64
- frozen source revision label supplied with the image: `8c231978`
- launcher: `/home/ember/fn-gates/freeze-f7190d69/build/fn-host`
- launcher SHA-256: `6855eba7d15424b1db8f039d1dff777f3bb675eb014662f7394f04ddb2818dd0`
- core SHA-256: `3364a22c75699e7d55161ab06608120e1831a5d0ccc8d4ef4222baa495e7e5ad`
- installer source: `bbcc1084` plus the crypto dependency check in the
  immediately following distribution commit
- task prefix: `/tmp/fn-native-dist-qual-20260921/install`

The installer executed the disabled reader entrypoint and observed exit 5 with
the production-profile refusal before installing. It copied the generated
launcher's `/home/ember/fn-tools/sbcl/bin/sbcl` and `SBCL_HOME` tree into the
task prefix. The source and copied SBCL executables both hashed to
`b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`.
The manifest recorded x86-64 `libsodium.so.23`, `libcrypto.so.3`, and
`libssl.so.3` paths from the system `ldconfig` inventory; it did not hash those
Linux libraries or observe loader events. The production-profile probe started
the image successfully, which exercised its startup-time crypto loading. The
SBCL `ldd` output itself listed only libc and libm.

## Invocation and result

The installer was run with explicit `FN_NATIVE_HOST`, `FN_NATIVE_CORE`,
`FN_NATIVE_SOURCE_REVISION=8c231978`, and the task-local absolute `PREFIX`.
Using only the installed `bin/fn`, the smoke then ran:

```
fn operator MISSING help run
fn store STORE init fn.test
fn operator CONFIG status
fn operator CONFIG run
kill -TERM OWNER_PID
```

Help, initialization, and status exited 0. Status reported zero transactions,
zero articles, and zero staging orphans. The owner announced its control socket
and `LISTENING 39127`, then exited 0 after SIGTERM.

While the owner was live, `/proc/OWNER_PID/exe` resolved to the installed
`libexec/fn/runtime/sbcl`. Its command line named the installed core and the
positional `--fn operator CONFIG run` entry. `pgrep -P OWNER_PID` found no child
processes, and the observed owner process contained no Python executable or
argument. No service manager command or pre-existing service was used.

The selected image predates the live peer-admin callback and returns usage 5
for public `peer add`; this qualification therefore makes no native peering
claim. The short source revision is the identity delivered with this frozen
image, rather than a reconstructed full commit identity.
