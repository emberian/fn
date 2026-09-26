# release-openbsd (2026-09-26): no Python on the runpath; fn on OpenBSD 7.9

Lane release-openbsd, D35. Branch `lane/release-openbsd` from dev 265d3242d,
with `lane/crypto-deps` (11e31599f) merged. Requirement HST-015 (new).
Evidence files live on hbox under `/tank/fn/scratch/release-openbsd/evidence/`
(first probe run) and `.../evidence/merged/` (the candidate); SHA-256s below.

## 1. No Python on the runpath (HST-015)

What a deployed node executes, enumerated from the tree:

| Step | What | Interpreter / format |
| --- | --- | --- |
| service | systemd `fn.service`, launchd plist, OpenBSD `rc.d/fn` | start `PREFIX/bin/fn operator CONFIG run` |
| `bin/fn` | packaging/fn | `/bin/sh`; runs `readlink`, `dirname`, then `exec` the image |
| `libexec/fn/fn-host` | frozen launcher (packaging/freeze-native-image.sh) | `/bin/sh`; runs `dirname`, then `exec runtime/sbcl` |
| `runtime/sbcl` | SBCL runtime | ELF; Linux: libc etc.; OpenBSD 7.9: libzstd (bundled), libutil, libpthread, libm, libc |
| the core | dlopen | libsodium, libcrypto+libssl (system), `lib/libfn-mldsa65.so` |
| process starts | `host/**/*.lisp` | exactly one: `fnn-workflow-ion-run-helper` (host/native/workflow.lisp), `sb-ext:run-program` of the absolute, operator-named pinned ION helper, `:search nil`, reachable only through `fn --fn app-journal workflow-ion-submit` |
| contrib fasls | `runtime/sbcl-home/contrib/*.fasl` | SBCL fasls with a `#!.../sbcl --script` header line; data the runtime loads |

Findings:

- The runpath has no Python. The one program start is operator-supplied;
  the check cannot tell what that helper is (docs/operator.md calls it a
  "trusted pinned ION binary").
- The `app-journal` verb that reaches the helper is registered in the
  production image too (host/native/workflow.lisp `fnn-register-verb`), while
  docs/operator.md "Experimental offline ION/LTP submission" says the
  developer image. A doc/profile mismatch, not a Python finding; left as is
  (a packet for the deputy).

`tools/runpath_check.py`: static mode (in `make check`) and `--tree`/`--tarball`
(run by `packaging/release-tarball.sh` before it packs). Fails on an unlisted
process site in `host/` (comments and strings are blanked first), a stale
listed site, a dlopen candidate naming Python, a shipped script whose
interpreter is not `/bin/sh`/`/bin/ksh` (SBCL fasl headers excepted), a
command word that is Python or resolves on the checking machine to a Python
script, a `.py`/`.pyc`, an ELF object whose DT_NEEDED names libpython, an
executable that is neither sh nor ELF, a service file that does not start
`PREFIX/bin/fn`. It cannot see what a shell variable holds at run time or
what the target's loader resolves. `tests/test_runpath_check.py` (10 cases:
clean tree, clean release, and one failing case per rule). On the candidate
tarball: `runpath-tarball.txt` (df078bb4...), "no Python on the deployed path".

## 2. OpenBSD 7.9 amd64 in a VM on hbox

Provenance. hbox's user is not in group `kvm`, so qemu runs in a container
(`fn-openbsd-qemu:local`, image sha256:f589094d..., ubuntu:24.04 +
qemu-system-x86 8.2.2, Dockerfile 19f2dc84...) with `--device /dev/kvm`; no
host package or group was changed. Disk: 20 GB qcow2,
`/tank/fn/scratch/release-openbsd/vm/`. Unattended install: PXE
(`auto_install` = pxeboot a07e21c3..., `bsd.rd` 6f0974bf..., checked against
cdn.openbsd.org 7.9 `SHA256` 50bec66f...), response file
`vm/http/install.conf`, disklabel template 4ca103e0... (`/usr/local` 11.6 GB,
mounted `wxallowed` by default); the installer verified every set against
`SHA256.sig` ("Signature Verified"); `syspatch` applied 002-021. Build runs:
8 vCPU / 7 GiB. Run and measurement: **1 vCPU / 2 GiB** (`hw.physmem`
2130563072), matching the friend's machine (sal.lo2.org: 7.9, 1 CPU, 2 GB,
clang 19.1.7, no Lisp).

Toolchain in the build VM: `pkg_add sbcl` (2.6.3; hbox's is 2.6.8),
`libsodium` (1.0.22, `libsodium.so.11.1`), `python` (3.13, build tools only),
`bash` and `gmake` (ACL2's build); base clang 19.1.7 and LibreSSL 4.3.0.

| Step | Result |
| --- | --- |
| LibreSSL and ML-DSA-65 | `openssl genpkey -algorithm ML-DSA-65`: "Algorithm ML-DSA-65 not found" (confirmed; then moot: crypto-deps' PQClean) |
| ACL2 8.7 (acl2.tar.gz d6013c22..., the hbox recipe) | `gmake LISP=sbcl` builds `saved_acl2`; `update_books_build_info` needs `bash` (Error 127 without it); system books certified (`build-sysbooks.log` 0ce3e13d...) |
| Heap on OpenBSD | root's login class `daemon` caps datasize at 4 GiB, which a 4096 MB dynamic space plus the rest exceeds ("mmap: Cannot allocate memory"); the build used 3072 MB |
| fn books | `certify_books.py --closure --no-publish` over the default profile's 185 roots: pass, 4.5 min on 8 vCPU (`certify-openbsd-manifest.json` 6e16df8e..., log d6fe7829...) |
| First image build | refused: "native TLS: no complete OpenSSL libcrypto/libssl pair exists" (the blocker crypto-deps removed) |
| Candidate images (a04213276 tree) | developer and production build (`native-host-build-*.log` d2c0a85a.../611c3fb9...); `libfn-mldsa65.so` built by base clang; identities in `build-identity.txt` (58666798...) |

Native modules on OpenBSD (candidate images, `SBCL_USER_ARGS=--dynamic-space-size 1024`, pool-less, 8 vCPU VM):

| Module | Result | Log SHA-256 |
| --- | --- | --- |
| tests.test_native_operator_verbs | OK (22) | 4ea0346a... |
| tests.test_native_implicit_tls | OK (3) | 3f5ef4fb... |
| tests.test_native_hybrid_author (FN_TEST_OPENSSL = pkg eopenssl35, test tool only) | OK (11) | e4abeed9... |
| tests.test_native_starttls | FAILED (1 of 2): harness | 57e86dd6... |
| tests.test_native_tls_transport | FAILED (1 of 2): harness | 54718bd0... |

The two failures are harness expectations written for OpenSSL, classified
harness, not changed here:

- starttls `test_pipelined_clienthello_protection_and_failure_isolation`
  expects EOF with no bytes after a malformed ClientHello; LibreSSL sends one
  fatal alert record (`15 03 01 00 02 02 46`, protocol_version) and then
  closes. With a VM-only copy of the test that reads past exactly that alert
  (`tls-test-probe.diff` 5a20784e...), the module passes (2 of 2, 47dbfa86...),
  so the listener survives the malformed handshake.
- tls_transport's Lisp driver asserts the version string contains "OpenSSL 3";
  it is "LibreSSL 4.3.0". Accepting "LibreSSL " as well (VM-only copy), the
  module passes (2 of 2, 325e4e06...).

The TLS client path (the peer feed's): `tls_client_probe.lisp` (f67566e6...)
drives `fnn-tls-open-client-context` and `fnn-tls-connect` against LibreSSL
`openssl s_server`: the TLS 1.2 floor ctrl, `SSL_set1_host` and the SNI ctrl
(55) are accepted, the server logs the server_name
`fnbsd.friends.fn.invalid`, TLS 1.3 completes, and a wrong name is refused
"certificate verify failed" (`tls-client-probe.log` 805f1b20...). This is the
confirmation crypto-deps asked for.

## 3. The OpenBSD tarball, installed fresh

`fn-a04213276edf-openbsd-amd64.tar.gz` (86 MB, sha256 18a2d2b6a5d0318e...),
built in the VM by `packaging/release-tarball.sh openbsd-amd64` from
`freeze-native-image.sh` with `FN_FREEZE_SODIUM=/usr/local/lib/libsodium.so.11.1
FN_FREEZE_DYNAMIC_SPACE_MB=1024`. It carries the SBCL runtime, sbcl-home,
`lib/{libsodium.so.11.1,libzstd.so.7.0,libfn-mldsa65.so}`, the rc.d script,
the docs and a BSD-format SHA256SUMS; TLS is the base LibreSSL.

Then every package was removed (`pkg_info`: firmware, quirks, updatedb only;
no sbcl, libsodium, zstd, python) and the VM restarted at 1 vCPU / 2 GiB.
From the tarball alone, as docs/operator.md "On OpenBSD" says
(`fresh-install.log` 9ad81ead...): sums OK, `_fn` user, `mission
small-community`, LibreSSL `openssl req` EC pair, `init`, `policy set
path-identity`, `principal set-password`, rc.d install, `rcctl enable/start`,
`rcctl check` ok, listening; `fn --version` prints a04213276edf...

| Observation (2 GiB, 1 vCPU) | Result | Evidence |
| --- | --- | --- |
| STARTTLS, 483 before it, login, post, fresh-connection reread, from hbox (Linux) | all held, TLSv1.3 TLS_AES_256_GCM_SHA384 | probe-1.log a3c8933e... |
| `peer keygen` (Ed25519 from libsodium, ML-DSA-65 from PQClean) | principal 5bb9e50c... | keygen.log c4dba953... |
| 99 more probes (100 posts, 200 TLS sessions) | 99 of 99, 49 s | posts-100.txt 599ab1fb... |
| Resident size of the node | 37.2 MB at start, 43.4 MB after 1 post, 90.4 MB after 100 (VSZ 1.49 GB: the 1024 MB reservation) | rss-*.txt, posts-100.txt |
| Smallest heap, development profile, fresh node, one post + read | 288 MB served; 280 MB listened then died in the first session (probe exit 3, ldb backtrace); 256 MB refused at start "dynamic space too small for core: 272320KiB required" | heap-sweep-a/b/c.txt 95c24f19.../f9c9581d.../3c9ca3f0... |
| First Linux-to-OpenBSD peering | Linux node (crypto-deps' tarball fn-cde3986a5c78, hbox system OpenSSL 3.3.1, on 172.17.0.1:11990) `peer invite`; OpenBSD `peer accept` (verifies the Linux-signed invitation); Linux `peer confirm` (verifies the OpenBSD-signed acceptance); both `peer list` show the other | peering-*-2.log 2ab7fe5e.../0e14808c... |

The first peering attempt passed the OpenBSD name as the invitation's PATH
(the inviter's own path identity); the records were removed and the second
exchange is the evidence (both logs kept).

Not done: section 3 of peering-with-a-friend.md (the protected feed both
ways, articles flowing between the nodes) was not run; the peer records are
the clear, inbound-only ones `accept`/`confirm` write.

## Findings for OpenBSD (each with its disposition)

1. W^X: SBCL is `OPENBSD_WXNEEDED`; the release must live on a `wxallowed`
   mount. Prefix `/usr/local/fn-REV12` (default install mounts it so).
2. The runtime links `libzstd.so.7.0` from packages; the freeze now bundles
   every non-base DT_NEEDED of the runtime.
3. The 32000 MB heap the image inherits fails at start on OpenBSD
   (datasize: 1536 MB `default`, 4096 MB `daemon`).
   `FN_FREEZE_DYNAMIC_SPACE_MB` writes the size into the frozen launcher;
   `SBCL_USER_ARGS` still overrides. Lane heap-from-profile owns deriving it.
4. The image halts at start when its working directory is unreadable
   (`getcwd: Permission denied`, ACL2's `our-pwd`); the rc.d script sets
   `daemon_execdir=/var/fn`, the docs say `cd /var/fn`.
5. A link to `bin/fn` resolved the image beside the link; `packaging/fn`
   now follows the link (`readlink -f`).
6. `store clone` publication needs Linux `renameat2(RENAME_NOREPLACE)`
   (host/native/checkpoint.lisp refuses elsewhere); unexercised capability on
   OpenBSD. The DTN image's BP clock needs Linux `CLOCK_BOOTTIME` and boot ID
   (host/native/bp.lisp); DTN is not in the OpenBSD tarball.
7. Host ports made here: getpeereid for the control socket
   (host/native/control.lisp) and the statvfs offsets (checkpoint.lisp; the
   OpenBSD amd64 struct matches Linux x86-64 at f_frsize 8 / f_bavail 32).
   Exercised by operator_verbs; the free-space observation is not separately
   asserted on OpenBSD.
8. The two TLS test harnesses above assume OpenSSL.

## Assurance chain

Packaging and host I/O only; no book changed. Native entry `bin/fn` →
frozen launcher → `fn-native-entry` (host/native/build.lisp) → the same
ACL2 subjects as on Linux (the certified closure, re-certified on OpenBSD
with SBCL 2.6.3: manifest above) → the observed results in the tables. The
runpath check is a static and file-level inspection, not a theorem.

## Commits

7a65596fd (runpath check, platform plumbing), 62ecdd3da (fasl headers),
e241585b3 (link-following launcher, rc.d /var/fn), 963657361 (merge
crypto-deps), a04213276 (docs; the tarball's revision), then the record and
HST-015.
