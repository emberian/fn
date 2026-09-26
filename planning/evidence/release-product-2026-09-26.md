# release-product (2026-09-26): the release is the product (D35)

Lane release-product, wave 5 lane 7, Opus. Ids: HST-017 (the release
layout), HST-018 (no Python in the runpath), SCN-134, PKT-588. Branch
`lane/release-product`; base dev 91c59dabb with lane/launcher-env,
lane/crypto-deps and lane/release-openbsd (62ecdd3d) merged in (the two named
prerequisites had not landed at launch: migration-removal had no commit,
release-openbsd was still working). D35 as ember confirmed it applies, not
the brief's wording: the release bundles NO OpenSSL; the node uses the
system libssl (HST-016, crypto-deps) and the release carries libsodium and
libfn-mldsa65.

## The release, as built

| | |
| --- | --- |
| tarball | `fn-c755569badf5-linux-x86_64.tar.gz`, 87,249,497 octets |
| SHA-256 | `26d56fba0b3b0017ded52e5f846ee6ff336c711b40efc1a41de78a4b55f66c75` |
| where | hbox:/tank/fn/scratch/release-product/out/ (with `SHA256SUMS`) |
| source | c755569badf5839f85750619d6b7fa1a370e7e94, `git archive` (296,427,520 octets), never a worktree |
| image | production only (`fn-host`, 142M core); `fn --version` prints `fn c755569badf5839f85750619d6b7fa1a370e7e94` |
| build | `packaging/release-tarball.sh linux-x86_64 REV OUT ARCHIVE` on hbox, FN_CERT_CACHE=/tank/fn/certcache, FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g, the image under swarm-build; log `release-product-2026-09-26/build-c755569badf5.log` (sha256 400214b3...) |

**This is the file lane public-node deploys**: the path and SHA-256 above
(its `SHA256SUMS` beside it lists exactly that line). It is built from a
LANE revision; the batch rebuilds it from the merged revision with the same
command (READY FOR BATCH in the lane's LANEDUMP), and public-node deploys
the batch's tarball, not this one, if the batch's revision differs.

The release gate, as the tarball carries it (`share/fn/release-gate.txt`):

```
source=c755569badf5839f85750619d6b7fa1a370e7e94 (git archive, 296427520 octets)
green-check profile=default: 403 books in the closure of 185 roots, 403 green at their current digest; not green: none
acquire: profile=default image=build/fn-host artifact-set=768967bc... origin=composed books=403 source=69b87de4... toolchain=d5f2b9f0... rejected=0
validate: profile=default image=build/fn-host roots=185 result=loaded
acl2: /tank/fn/toolchains/w28/acl2-literal-4g
```

`green_check --profile default --strict` is new here: the closure of the
image profile's roots (tools/proof_artifacts.py's `profile_roots`, the set
`acquire` loads), each book's verdict at its current digest from the
committed manifests; exit 1 unless all are green. The build refuses before
acquiring anything otherwise.

## The layout (HST-017)

One top directory `fn/` (no revision in the directory: D34, one
installation directory):

```
fn/SHA256SUMS                  every file below
fn/install.sh                  packaging/install.sh
fn/bin/fn                      packaging/fn (launcher-env's installed form)
fn/libexec/fn/fn-host          frozen launcher v2
fn/libexec/fn/fn-host.core     production core
fn/libexec/fn/source-revision
fn/libexec/fn/runtime/         sbcl, sbcl-home/
fn/libexec/fn/lib/             libsodium.so.23, libfn-mldsa65.so
fn/share/fn/                   systemd/fn.service.in, fn.toml.example, docs/install.md,
                               native-artifacts.txt, release-gate.txt, runpath-check.txt
```

On OpenBSD the service template is `share/fn/rc.d/fn.rc.in` and `lib/` adds
the runtime's libzstd (release-openbsd's freeze). `install-native.sh` stages
one directory and refuses a non-empty prefix; `install.sh` (the stranger's)
checks SHA256SUMS, asks the release's own `status` about an existing node
(a `store-format` answer stops it before anything is copied), refuses an
existing prefix, and installs the account, node directory and unit.

## No Python in the runpath (HST-018)

`tools/runpath_check.py` (release-openbsd's; static mode in `make check`)
gained in `--tree`/`--tarball` mode: symbolic links must stay inside the
release; a shipped script may run an absolute path only if it is the shell
or rc.subr; each ELF object's interpreter must be the C library loader, no
RPATH/RUNPATH outside, each DT_NEEDED carried by the release or the C
library; every `lib*.so` name the saved core carries (latin-1 and UTF-32
strings) must be carried, the C library, or the system TLS library D35
chose. The build runs it before packing; its output over the tarball
(`release-product-2026-09-26/runpath-tarball.log`, sha256 1de33e96...):

```
runpath: bin/fn: /bin/sh; commands: dirname $image
runpath: libexec/fn/fn-host: /bin/sh; commands: dirname $here/runtime/sbcl
runpath: libexec/fn/fn-host.core: dlopen names libcrypto.so libcrypto.so.3 libfn-mldsa65.so libsodium.so libsodium.so.23 libssl.so libssl.so.3; the system's: libcrypto.so libcrypto.so.3 libssl.so libssl.so.3
runpath: libexec/fn/lib/libfn-mldsa65.so: ELF; needs libc.so.6 ld-linux-x86-64.so.2
runpath: libexec/fn/lib/libsodium.so.23: ELF; needs libc.so.6 ld-linux-x86-64.so.2
runpath: libexec/fn/runtime/sbcl: ELF; needs libm.so.6 libc.so.6; interpreter /lib64/ld-linux-x86-64.so.2
runpath: 23 SBCL contrib fasls (#!.../sbcl --script headers, loaded by the runtime)
runpath: share/fn/systemd/fn.service.in: starts @PREFIX@/bin/fn
runpath_check .../fn-c755569badf5-linux-x86_64.tar.gz: no Python on the deployed path
```

(The tarball's own `share/fn/runpath-check.txt` was written by the check as
of c755569b, before the UTF-32 scan; the line above is the final tool over
the same bytes.) Witnesses: tests/test_runpath_check.py (laptop, 15 OK): a
planted `bin/python3 -> /usr/bin/python3`, a link leaving the tree, an
uncarried DT_NEEDED, a `libpython3.12.so.1.0` string in the core, an
absolute command outside the release; and on the real tarball,
tests.test_release_tarball's planted symlink in a scratch copy (fails with
`bin/python3: links to /usr/bin/python3`) beside the pass on the real one.

## tests.test_release_tarball on hbox

`FN_RELEASE_TARBALL=.../fn-c755569badf5-linux-x86_64.tar.gz python3 -m
unittest -v tests.test_release_tarball`: 8 ran, 7 OK, 1 skipped
(`test_install_refuses_a_format_7_store`: FN_FORMAT7_FIXTURE unset; the
one-format open is lane migration-removal's, not in this revision). Log
`release-product-2026-09-26/test_release_tarball.log`, sha256 4c69f3fe...

## The rehearsal (Linux, hbox, isolated copies; never /tank/fn/node)

`release-product-2026-09-26/rehearsal.sh` (node side, on hbox under
/tank/fn/scratch/release-product/rehearsal), the client on persvati
(`tools/fn_client.py`, STARTTLS with the node's certificate as the only
anchor, AUTHINFO):

| step | log | sha256 |
| --- | --- | --- |
| sum, unpack, `install.sh --no-service`, `mission small-community --host 192.168.50.39 --port 11995`, self-signed P-256 pair, `init`, `policy set path-identity`, `principal set-password rehearsal --posting`, `status` | hbox/install.log | fcd52b34... |
| `systemd-run --user --unit fn-release-rehearsal ... bin/fn operator fn.toml run`; listening; `--version` | hbox/start.log (the second start's) | caa6a2dd... |
| persvati: `groups`; `post local.general` accepted `240` | persvati/post.log | 7b397e45... |
| persvati: `show <fn-client.20260926T185412Z.c67ac60f@rehearsal.invalid>` | persvati/read-before.log | 861b204c... |
| stop; remove the prefix; install over a non-empty prefix REFUSED (`an installation is one directory`); install again; `status` (install.sh asked the new release about the node first) | hbox/stop.log, hbox/remove-reinstall.log | 0c2a2a9b..., 0b411fa2... |
| start; persvati: `show` the same Message-ID | persvati/read-after.log | 861b204c... (byte-identical to read-before) |

What the rehearsal does NOT show: `store export`/`store import` (the verbs
do not exist at c755569b; migration-removal owns them), so the reinstall
kept the node directory, which is the same-format case. The export/import
leg and the format-7 refusal run in the batch once migration-removal is
merged (READY FOR BATCH). A system unit under root was not exercised (hbox
gives no root); the user-manager path was.

## OpenBSD: not shipped

The OpenBSD tarball is not built. First blocker: an image build in the
OpenBSD VM needs the default closure's certificates for the VM's own ACL2
toolchain (certificates are bound to a toolchain identity; there is no such
cache), and lane release-openbsd, which owns the VM and its recipe, had not
reported when this record was written (its LANEDUMP names the VM, nothing
past it). The recipe exists: `release-tarball.sh openbsd-amd64 REV OUT
ARCHIVE` inside the VM with FN_CERT_CACHE/FN_ACL2 of that toolchain; the
freeze, install and rc.d template carry release-openbsd's OpenBSD plumbing
(W^X, libzstd, BSD sha256 lines). PKT-588 carries it.

## Deletion map (design 4.7, D35 row)

- The developer checkout as a deployment: `tools/runbooks/hbox-node-deploy.sh`
  now installs only from a release tarball (sum, the tarball's
  `install.sh`, mission) and refuses /tank/fn/node without an explicit
  variable; its checkout steps (`cd TREE`, `install-native.sh` from the
  worktree, `fn-host --fn store init`, the hand-written fn.toml) are gone;
  runbooks/README's versioned-releases paragraph is gone.
- `packaging/upgrade-native.sh`: removed by migration-removal (not touched
  here, so the two lanes do not conflict); the release does not ship it.
- Docs telling the operator to run Python on the node: operator.md's
  `~/fn-live` section (tools/live_service.py) replaced by the release's
  user-service form; its head now says a release runs no Python and points
  to docs/install.md; the old tarball prose (OpenSSL 3.5 bundled) replaced.
  Kept, because they run on another machine: fn_client.py, node_probe.py,
  fn_web.py. The Python development service sections ("Install",
  "Initialize") remain, marked as the checkout's, not a release's.

## Not done, and why

- store export/import in the rehearsal (above); install.md's two lines are
  marked `docs-check: skip` until the verbs exist.
- The OpenBSD tarball (above).
- A self-signed certificate tool in the tarball: the brief allows "a
  self-signed one the tarball's tool makes, or the operator's"; install.md
  uses the platform's `openssl req` (LibreSSL's on OpenBSD) or the
  operator's pair (Let's Encrypt for the public node). A verb would be new
  host X.509 code plus grammar; PKT-588 (b).
- `packaging/fn`'s header still names upgrade-native.sh and the upgrade
  verbs; heap-from-profile rewrites that file in the same batch, so the
  comment is left to the merge.
- The mission's fn.toml still writes `[ops] keep_releases = 3`
  (migration-removal's D34 removal).

## Assurance chain

No ACL2 theorem is claimed. Native entry `bin/fn` (packaging/fn) -> the
frozen launcher -> the production core, whose every decision is the
certified closure the gate names (green_check at the digests, acquire and
validate at build) -> observed: the rehearsal's post and reads, the
tarball test, the runpath check. The one book changed is the generated test
book tests/acl2/docs-operator-grammar-tests.lisp (install.md's rows),
admitted whole in the persvati REPL (13 forms, `last loaded: assert-event`).
