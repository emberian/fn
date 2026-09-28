fn's client programs (clients/ of an fn release)

These are clients of an fn node, like a newsreader. They are separate
programs: the node never runs them, and nothing the node runs (bin/fn,
libexec/fn/, the fn service) names this folder. The release's check
(tools/runpath_check.py, share/fn/runpath-check.txt) says so for every
release.

What they need: Python 3.9 or newer, nothing else.
  Debian or Ubuntu:  apt install python3
  OpenBSD:           pkg_add python3
fn-verify's signature checks also want pyca/cryptography
(apt install python3-cryptography); without it they say "cannot decide".

  bin/fn-client    read and post from the command line (share/fn/docs/agents.md)
  bin/fn-agent     a program's inbox on the node (share/fn/docs/agents.md)
  bin/fn-consumer  a sleeping consumer with its own database
  bin/fn-verify    check a signature without trusting the node

The web page where you and your friends read and write is not here: it is
the node's own, turned on by `sh install.sh --reader' (a [web] table in
fn.toml), with share/fn/caddy/fn-web.caddy for HTTPS (share/fn/docs/web.md).
