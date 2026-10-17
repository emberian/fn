# Runbooks

Hand-driven sequences with box-specific paths, kept here so they survive a
session. None of them is a gate or a claim; each says what it does at the top.

- `hbox-image-build.sh <frozen-tree> <40-char-rev>`: after a farm closure
  certifies, acquire and validate the artifact set, build the production,
  developer, DTN production and DTN developer images under `swarm-build`, freeze them under
  `build/images/<rev>/` with a source manifest and hashes.
- ONE ACL2 TOOLCHAIN on hbox and persvati (lane toolchain-unify, 2026-09-28):
  both run w28 from the SAME absolute paths, `/tank/fn/sbcl`,
  `/tank/fn/acl2-8.7` (core + certified system books) and the launchers in
  `/tank/fn/toolchains/w28/` (`acl2-literal-4g`, `-tls64k`).  The identity
  `tools/acl2_toolchain.py` computes hashes the launcher's bytes (which name
  those paths), the core and the runtime, so a byte-identical copy at the
  same paths has the same identity (d5f2b9f0; tls64k fcedce7e) and the two
  caches exchange certificates (`tools/cert_cache_sync.py`, run by farm's
  fetch).  To put it on another Linux box (as done for persvati; its
  `/tank/fn` is a plain directory, and it has no `/tank/fn/scratch`, which
  `tools/boxes.sh` reads as hbox's): `sudo mkdir -p /tank/fn && sudo chown
  $USER /tank/fn`, then from the laptop `ssh hbox 'cd /tank/fn && tar cf -
  sbcl acl2-8.7 toolchains/w28' | ssh BOX 'cd /tank/fn && tar xpf -'`, and
  check `ssh BOX python3 - identity /tank/fn/toolchains/w28/acl2-literal-4g
  < tools/acl2_toolchain.py` prints hbox's identity.  persvati's old w25
  (`~/fn-tools`, `~/fn-gates/toolchains/w25`, identity 1b4169e9) is retired.
- `persvati-acl2p.sh build | measure <book> <mode> [cpus]`: build ACL2(p)
  8.7 into `/home/ember/fn-gates/toolchains/w25p` from the tarball w25 used,
  certify its system books, and time one book's certification in the
  `/home/ember/fn-gates/acl2p` gate under plain ACL2 or an ACL2(p) waterfall
  mode. A measurement, not a toolchain: see `planning/evidence/acl2p-2026-09-23.md`.
- `hbox-node-deploy.sh TARBALL SHA256 NODE PREFIX LISTEN_IPV4 PORT PATH_IDENTITY`:
  a node from a RELEASE TARBALL (packaging/release-tarball.sh; D35), never
  from a checkout: the sum checked, the tarball's own `install.sh
  --no-service` into PREFIX (one directory), `mission small-community`, a
  self-signed pair, `init`, the path identity, principals `ember`/`yue`/`tulip`
  with generated passwords kept only in `NODE/credentials.txt` (mode 0600),
  and `systemd-run --user --unit fn-node`. Refuses an existing `NODE/store`,
  and `/tank/fn/node` unless `FN_DEPLOY_LIVE=yes`.
- `two-host-protected-gate.md`: stage one source-pinned frozen image in
  separate hbox and persvati scratch paths and run the protected NNTP gate
  after its image hashes are supplied. It never uses the live node store.
- `two_store_join.py run --image-dir DIR --mini-bin BIN --scratch
  /tank/fn/scratch/... --local-out DIR [--cut FAMILY]`: from the Mini host,
  the one-exchange two-Store join (R at A, protected A→B peering, B's
  receiver verdict, Mini's poll/transaction/ACK at B, Mini's signed reply at
  B, B→A, restart both, Mini reads at A), with per-step logs and
  ACCEPTED/REFUSED/UNCERTAIN verdicts. `--mini-a-FIELD` / `--mini-b-FIELD`
  (FIELD one of pinned-config, genesis, birth-intent, custody-key, policy)
  give each side its own Mini deployment, so A and B are independent Mini
  identities; an absent one is the common input. See
  `planning/evidence/two-store-join-harness-2026-09-24.md`.

After `hbox-node-deploy.sh`, the check from the laptop is `tools/node_probe.py`
(see docs/operator-internals.md, "Reaching it from a laptop"): STARTTLS, the 483 before
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
`hbox-node-deploy.sh` deploys only a release tarball (above).
It still refuses an existing store.

A deploy is a reinstall (D34): stop the node, `fn operator NODE/fn.toml store
export DIR` if its data must survive, remove the installation, install the new
release (its `install.sh`, which replaces one `libexec/fn/` whole), then `init`
or `fn operator NODE/fn.toml store import DIR`, and start (docs/install.md
section 4). There is no release switching, no versioned release directory, no
`current` symlink and no rollback of a store: a store of another format is
refused at open by name (`open refused reason=store-format: reinstall from the
release and import`).


## Measurement kits and the source-world emitter

Not gates and not claims; a number from one of these is quoted only with the
image and revision it ran on.

- `tools/native_source_world.py`: emit the current native logical world as
  ordinary, resumable ACL2 source (the composition gate: `--world-book
  books/image-world-dtn --cache-root CERTS --output build/... --source-revision
  REV`, no `--defer-defthm`; the result must `ld` in one `proof_repl` session
  to `FN_SOURCE_LOGICAL_WORLD_READY`). `native_source_runner.py` and
  `native_source_cache.py` drive and cache it (CONTRIBUTING.md).
- `tools/image_anatomy/` (`anatomy.sh IMAGE OUT SNAPSHOT...`, `derive.sh`,
  `ia_node.py`, `ia_report.py`): every object of an image's core given an
  owner and joined with a node's residency snapshots, and the probes behind
  three ways to make the image smaller (lane image-anatomy, 2026-09-26).
- `tools/runtime_floor/` (lane runtime-floor, 2026-09-27, `8ac70017a`; merged
  by python-diet-4): `extract.lisp`, loaded into a DEVELOPER image's core
  started without ACL2's loop (`rf-start.sh IMAGE FILE`), exports the
  world's executable definitions (ACL2's own CLTL-COMMAND raw forms, macros
  expanded) as a plain Common Lisp system; `build-sbcl.lisp` /
  `save-plain-sbcl.lisp` save it with host/native unchanged in a bare SBCL
  core, `build-ecl*.lisp` the same on ECL; `trace.lisp` + `replay*.lisp`
  record the host-to-ACL2 calls of a run and replay them on each target;
  `mapbreak.py` splits a node's RSS by mapping (runs on hbox beside
  `tools/runtime_image/node_measure.py`). At `bc7958f87` it measured: the
  production image 90 MiB RSS at start (70.5 clean core pages, 17 anon of
  which 9.1 the 65,536-word TLS); the export 10,173 definitions, 0 undefined;
  a bare-SBCL node 30 MiB at start with the identical served transcript and
  store digests; 191,423 recorded calls identical on bare SBCL and ECL 26.5.5
  (ECL 16-45x slower). Those numbers are that revision's; no current-image
  run exists. It is the prototype for the D35 question (an extracted build
  on plain SBCL), wave 3/4 tcb-shrink.
