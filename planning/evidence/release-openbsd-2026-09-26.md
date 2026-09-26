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

## Continuation: openbsd-feed (2026-09-26, ~19:05-19:40Z)

Evidence on hbox under `/tank/fn/scratch/release-openbsd/feed/` (with a
`SHA256SUMS` of every log and article file) and
`.../evidence/feed-tests/`.

### SCN-136: articles over the protected feed, Linux <-> OpenBSD

The two nodes of §3 (Linux fn-cde3986a5c78 on hbox, OpenSSL 3.3.1; OpenBSD
fn-a04213276edf in the guest under rc.d, LibreSSL 4.3.0, 1 vCPU / 2 GiB),
already peered by invite/accept/confirm, were given docs/peering-with-a-friend.md
§3 each way: a login bound to the other node's principal (`bsd-node` on
Linux for 5bb9e50c..., `linux-node` on OpenBSD for 590dad59...), an FNAUTH1
profile, and `peer add` of the same name with `starttls NAME ANCHOR`,
`local.*` both halves (`setup-linux.log` e1287fa8..., `setup-openbsd.log`
377069009f...), then both restarted (the new logins are read at start).
The guest's container cannot reach the host's docker bridge address
(172.17.0.1), so OpenBSD reaches the Linux node through an ssh reverse
tunnel (`systemd-run --user` unit fn-rob-tunnel, guest 127.0.0.1:11990 ->
172.17.0.1:11990; `setup-openbsd-2.log` 30c4b9b8...); the name check is on
the certificate's CN either way.

| Direction | Origin log | Receiver log | Read back over STARTTLS (TLSv1.3) |
| --- | --- | --- | --- |
| Linux -> OpenBSD, `<node-probe.20260926T191651Z.c8998084@probe.invalid>` | `accepted feed peer=fnbsd ... code=239` | `accepted transit ... code=239 decision=want ... verdict=unsigned` | Linux ae748d2d... (477 B), OpenBSD f6676afe... (503 B) |
| OpenBSD -> Linux, `<node-probe.20260926T191652Z.f2e05471@probe.invalid>` | `accepted feed peer=hbox-linux.friends.fn.invalid ... code=239` | `accepted transit ... code=239 decision=want ... verdict=unsigned` | OpenBSD 2d63ff89... (467 B), Linux 21c12f3d... (498 B) |
| OpenBSD -> Linux, hybrid-signed `<openbsd-signed-1@fnbsd.friends.fn.invalid>` | `accepted post path=control`, `accepted feed ... code=239` | `accepted transit ... code=239 decision=want ... verdict=verified` | OpenBSD 1ea7889b... (7846 B), Linux 5ff2f176... (7877 B) |

In each pair the bytes differ only in the Path line: the receiver prepends
its own path identity with the `!!` diagnostic (RFC 5537 §3.2.1, RFC 5536
§3.1.5). Everything after the Path line is byte-identical: SHA-256
ce3b9ad1..., 96ec6ba3..., 980251e2... on both nodes respectively. `peer
pull` each way: `pull peer=... round=done cursor=advanced transport=tls`
on both (`pull-openbsd-3.log`, `pull-linux-3.log`; the logs:
`linux-fn-log-excerpt.log` 8c6ae471..., `openbsd-fn-log-excerpt.log`
bfa24660...).

The signed carrier: `hybrid-author` with keyring generation 1 was refused
`SIGNED-EVENT-NOT-FORMED` (generation 1 on the OpenBSD node is the Linux
principal `accept` enrolled; the article was signed with the OpenBSD keys),
2 and 3 `AUTHOR-NOT-ENROLLED`; after `hybrid-enroll` of the OpenBSD node's
own keys at generation 2 it was accepted (`signed-openbsd-generations.log`
0355918a...). `peer keygen` does not enrol a node's own keys at its own
node; the peering doc does not say to. Linux verified it under the
OpenBSD principal `peer confirm` had enrolled.

**A stop, not reproduced.** At 19:18:39Z, during the first pulls after the
tunnel, the OpenBSD node stopped: `owner core/store fault; process stopped:
ACL2 refused FNFD peer filename` (syslog, `openbsd-fault-daemon.log`
af0daa13...), and the Linux node's inbound TLS read ended in EOF the same
second (`linux-journal.log` c877c6a4...). Both peer names are legacy-safe
and both FNFD files existed under them, so the refused string was some
other value. After `rcctl start fn`, the same pulls in each direction were
`round=done` and nothing stopped. Classification: implementation, cause
unknown; PKT-591 (a).

### The two LibreSSL test expectations (repaired)

- tests/test_native_starttls.py `assertClosedAfterFailedHandshake`: after a
  malformed ClientHello the server closes with no bytes (OpenSSL 3) or with
  exactly one fatal alert record and then closes (LibreSSL:
  `15 03 01 00 02 02 46`). Still refuted: any plaintext NNTP reply, a
  handshake or other non-alert record, a warning-level alert, a second
  record, a connection left open.
- tests/native_tls_transport.lisp: the loaded library's text names
  `OpenSSL N` or `LibreSSL N` with N >= 3, checked from the text rather than
  through `fnn-tls-supported-version-p` (the function under test). Still
  refuted: no library loaded, OpenSSL 1.x, LibreSSL 2.x, any other name.

### Protocol floor and SNI on LibreSSL (two native cases)

Both in tests/test_native_starttls.py:
`test_protocol_floor_refuses_tls_1_1` sends a hand-built TLS 1.1-only
ClientHello after 382 (so the refusal is the server's, not the client
library's) and requires no handshake record back, at most one fatal
`protocol_version` alert, and close; then a TLS 1.2 client is served
(`DATE` 111). Teeth: the same hello against `openssl s_server -tls1_2`
draws `15030200020246`, against `-tls1_1` a ServerHello `160302...`
(`evidence/feed-tests/teeth.log` c0a42dbd...).
`test_sni_answered_with_the_configured_certificate`: a client sending
`server_name` completes, gets the configured certificate (the DER equal to
the one a client without SNI gets) and NNTP after it.

| Where | Module | Result | Log SHA-256 |
| --- | --- | --- | --- |
| OpenBSD guest, LibreSSL 4.3.0, the release image (`FN_NATIVE_HOST=/usr/local/fn-a04213276edf/libexec/fn/fn-host`) | tests.test_native_starttls | OK (4) | 3137f489... |
| OpenBSD guest | tests.test_native_tls_transport | OK (2) | a2802ef9... |
| OpenBSD guest, the build tree's image, no libsodium package | tests.test_native_starttls | environment: `libsodium cannot be loaded` (4 of 4); rerun above | 23c63a5a... |
| hbox, OpenSSL 3.3.1, `tools/hbox_native.sh --images developer,production .` (native-wt-20260926T192502Z) | tests.test_native_starttls | OK (4 ran, 0 skipped) | d5403e4d... |
| hbox | tests.test_native_tls_transport | OK (2 ran, 0 skipped) | 92deb8fd... (run.log b8e29f8b...) |

The client path's SNI and floor on LibreSSL were observed in §2
(`tls-client-probe.log` 805f1b20...).

### Filed

PKT-589 (`store clone` needs Linux renameat2), PKT-590 (app-journal in the
production image, docs say developer), PKT-591 (the unreproduced stop, the
tunnel, SCN-136 not a module). docs/operator.md "On OpenBSD": the rc.d
script starts the node in `/var/fn` itself.
