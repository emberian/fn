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

After `hbox-node-deploy.sh`, the check from the laptop is `tools/node_probe.py`
(see docs/operator.md, "Reaching it from a laptop"): STARTTLS, the 483 before
it, login, a post and a fresh-connection reread, with the password taken from
the environment and the certificate copied from `/tank/fn/node/tls/cert.pem`.

Not a runbook, but what to run before `hbox-image-build.sh`:
`python3 tools/triage.py <box> <roots...> --remote-root <path> --acl2 <path>
--cache <path> --budget-seconds 900 --rounds 3`. A closure run stops at the
first failing book and hides every book above it, so a red closure costs one
run per layer; a triage reports every independent red in the closure at once,
each with its first ACL2 error, its key checkpoint and the assumption it rests
on. Its certificates are published nowhere and its output is evidence of
nothing but the list of reds (docs/proofs.md).
