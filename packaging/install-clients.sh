#!/bin/sh
# Stage the clients subtree of a release (clients/: fn's command-line client
# programs, Python 3, separate from the node).  The web page friends use is
# not here: it is the node's own face ([web] in fn.toml, install.sh --reader,
# share/fn/caddy/fn-web.caddy).  fn_client and nntp_session are also the
# test instruments the native modules drive a node with:
#
#   sh packaging/install-clients.sh TOP
#
# TOP is the staged release directory (PREFIX under DESTDIR, the fn/ of the
# tarball); run from the source tree.  packaging/release-tarball.sh calls it
# after packaging/install-native.sh.  It writes
#   TOP/clients/bin/        the launchers (packaging/fn-client-launcher)
#   TOP/clients/lib/        the programs, from tools/
#   TOP/clients/README.txt  what they are and what they need
# and share/fn/docs/web.md, agents.md and share/fn/caddy/fn-web.caddy.  tools/runpath_check.py --tree
# checks clients/ under its own rule: Python is allowed there and nowhere
# else, and nothing outside it may run it.
set -eu
[ "$#" -eq 1 ] || { echo 'usage: install-clients.sh TOP' >&2; exit 2; }
top=$1
case $top in /*) ;; *) echo 'install-clients: TOP must be absolute' >&2; exit 2 ;; esac
[ -x "$top/bin/fn" ] || { echo "install-clients: $top is not a staged release (no bin/fn)" >&2; exit 4; }
[ ! -e "$top/clients" ] || { echo "install-clients: exists: $top/clients" >&2; exit 4; }
programs='fn_client fn_agent fn_consumer fn_verify'
for one in $programs nntp_session; do
  [ -r "tools/$one.py" ] || { echo "install-clients: missing tools/$one.py" >&2; exit 4; }
done
c=$top/clients
mkdir -p "$c/bin" "$c/lib" "$top/share/fn/docs" "$top/share/fn/caddy"
for one in $programs nntp_session; do
  install -m 0644 "tools/$one.py" "$c/lib/$one.py"
done
for one in $programs; do
  install -m 0755 packaging/fn-client-launcher "$c/bin/$(printf '%s' "$one" | tr '_' '-')"
done
install -m 0644 packaging/fn-web.caddy "$top/share/fn/caddy/fn-web.caddy"
install -m 0644 packaging/clients-README.txt "$c/README.txt"
install -m 0644 docs/web.md "$top/share/fn/docs/web.md"
install -m 0644 docs/agents.md "$top/share/fn/docs/agents.md"
echo "staged the clients under $c"
