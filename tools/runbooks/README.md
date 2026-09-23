# Runbooks

Hand-driven sequences with box-specific paths, kept here so they survive a
session. None of them is a gate or a claim; each says what it does at the top.

- `hbox-image-build.sh <frozen-tree> <40-char-rev>`: after a farm closure
  certifies, acquire and validate the artifact set, build the production,
  developer, DTN production and DTN developer images under `swarm-build`, freeze them under
  `build/images/<rev>/` with a source manifest and hashes.
- `persvati-acl2p.sh build | measure <book> <mode> [cpus]`: build ACL2(p)
  8.7 into `/home/ember/fn-gates/toolchains/w25p` from the tarball w25 used,
  certify its system books, and time one book's certification in the
  `/home/ember/fn-gates/acl2p` gate under plain ACL2 or an ACL2(p) waterfall
  mode. A measurement, not a toolchain: see `planning/evidence/acl2p-2026-09-23.md`.
- `hbox-matrix-provision.sh <image>`: two clean loopback stores for
  `tools/v0_matrix.py --backend native-operator` (ports 11190/11191).
- `hbox-node-deploy.sh <frozen-tree> <shortrev> <listen-ipv4>`: install the
  production image under `/tank/fn/node`, a self-signed STARTTLS pair,
  `[auth] required` + `protected_only`, path identity `hbox.ember.software`,
  groups, principals `ember`/`yue`/`tulip` with generated passwords kept only
  in `/tank/fn/node/credentials.txt` (mode 0600), and a user systemd unit
  `fn-node.service`. Refuses to touch an existing `/tank/fn/node/store`.

After `hbox-node-deploy.sh`, the check from the laptop is `tools/node_probe.py`
(see docs/operator.md, "Reaching it from a laptop"): STARTTLS, the 483 before
it, login, a post and a fresh-connection reread, with the password taken from
the environment and the certificate copied from `/tank/fn/node/tls/cert.pem`.

Not a runbook, but what to run before `hbox-image-build.sh`:
`python3 tools/triage.py <box> <roots...> --remote-root <path> --acl2 <path>
--cache <path> --budget-seconds 900`. An ordinary closure run stops at the
first failing book and hides every book above it, so a red closure costs one
run per layer. A triage runs the closure through ACL2's provisional
certification instead — one parallel wave does every book's proofs — so one
run names every independent red, each with its first ACL2 error and its key
checkpoint, and says of the books above them that their proofs passed and
they are waiting on a certificate. Measured on a 63-book closure: 337 s and
four reds, against 691 s and one for an ordinary round. Its certificates are
published nowhere and its output is evidence of nothing but the list of reds
(docs/proofs.md, planning/evidence/triage-2026-09-22.md).

## Frozen image and isolated upgrade

`hbox-image-build.sh` now freezes each core beside its launcher, copied SBCL
runtime/home, and the OpenSSL 3.5 pair plus libsodium used at runtime. The
launchers resolve these from their own directory. Verify `image.sha256` with
`(cd IMAGE && sha256sum -c image.sha256)` and exercise `IMAGE/fn-host --fn
reader invalid-port 1 -` (production refusal 5) before installation. The
source tree and original `build/*.core` are not runtime inputs. The initial
`hbox-node-deploy.sh` takes the full frozen image directory as fourth argument.
It still refuses an existing store.

For a managed *isolated fixture* node, put the persistent `store/`, `fn.toml`,
`tls/` and `credentials.txt` directly under NODE. Keep immutable installs in
`NODE/releases/REV` and point `NODE/current` at the active release. Make the
service's executable `NODE/current/bin/fn operator NODE/fn.toml run` before
using `packaging/upgrade-native.sh`; its control hook receives `stop`, `start`
and `check` with NODE as its second argument. The check must verify the actual
service and a fresh read of a known article. Invoke:

```sh
FN_UPGRADE_STORE_COMPATIBLE=yes FN_UPGRADE_CONTROL=/path/to/fixture-control \
  sh packaging/upgrade-native.sh NODE FROZEN_IMAGE_DIR REV
```

Before setting `FN_UPGRADE_STORE_COMPATIBLE=yes`, establish that the prior
binary can read every Store change the candidate may commit before a health
failure. A failed switch restores the executable and service, not prior Store
bytes. The tool cannot infer schema compatibility. Staged service templates
name the final release path, never the temporary stage path.

The tool verifies and stages the candidate before stopping, switches the
`current` symlink atomically, then starts/checks. A failed start/check restores
the prior symlink and restarts/checks it. The persistent paths are never copied
into a release; the tool checks their hashes and the store directory identity.
The old release remains available. This is tested only on isolated fixture
nodes. It has not been run on `/tank/fn/node`; that existing unit names a
versioned executable and must first be migrated to `current` during a planned
operator maintenance window. No automatic migration or live-node action is
part of this runbook.
