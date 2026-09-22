# Runbooks

Hand-driven sequences with box-specific paths, kept here so they survive a
session. None of them is a gate or a claim; each says what it does at the top.

- `hbox-image-build.sh <frozen-tree> <40-char-rev>`: after a farm closure
  certifies, acquire and validate the artifact set, build the production,
  developer and DTN images under `swarm-build`, freeze them under
  `build/images/<rev>/` with a source manifest and hashes.
- `hbox-matrix-provision.sh <image>`: two clean loopback stores for
  `tools/v0_matrix.py --backend native-operator` (ports 11190/11191).
- `hbox-node-deploy.sh <frozen-tree> <shortrev> <listen-ipv4>`: install the
  production image under `/tank/fn/node`, a self-signed STARTTLS pair,
  `[auth] required` + `protected_only`, path identity `hbox.ember.software`,
  groups, principals `ember`/`yue`/`tulip` with generated passwords kept only
  in `/tank/fn/node/credentials.txt` (mode 0600), and a user systemd unit
  `fn-node.service`. Refuses to touch an existing `/tank/fn/node/store`.
