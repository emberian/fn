#!/bin/sh
# Stage the clients subtree of a release (clients/: fn's client programs,
# Python 3, separate from the node):
#
#   sh packaging/install-clients.sh TOP
#
# TOP is the staged release directory (PREFIX under DESTDIR, the fn/ of the
# tarball); run from the source tree.  packaging/release-tarball.sh calls it
# after packaging/install-native.sh.  It writes
#   TOP/clients/bin/        the launchers (packaging/fn-client-launcher)
#   TOP/clients/lib/        the programs, from tools/
#   TOP/clients/share/      the reader's service template (this system's),
#                           its settings example, the Caddy snippet
#   TOP/clients/README.txt  what they are and what they need
# and share/fn/docs/web.md and agents.md.  tools/runpath_check.py --tree
# checks clients/ under its own rule: Python is allowed there and nowhere
# else, and nothing outside it may run it.
set -eu
[ "$#" -eq 1 ] || { echo 'usage: install-clients.sh TOP' >&2; exit 2; }
top=$1
case $top in /*) ;; *) echo 'install-clients: TOP must be absolute' >&2; exit 2 ;; esac
[ -x "$top/bin/fn" ] || { echo "install-clients: $top is not a staged release (no bin/fn)" >&2; exit 4; }
[ ! -e "$top/clients" ] || { echo "install-clients: exists: $top/clients" >&2; exit 4; }
programs='fn_reader fn_web fn_client fn_agent fn_consumer fn_verify'
for one in $programs nntp_session; do
  [ -r "tools/$one.py" ] || { echo "install-clients: missing tools/$one.py" >&2; exit 4; }
done
c=$top/clients
mkdir -p "$c/bin" "$c/lib" "$c/share/caddy" "$top/share/fn/docs"
for one in $programs nntp_session; do
  install -m 0644 "tools/$one.py" "$c/lib/$one.py"
done
for one in $programs; do
  install -m 0755 packaging/fn-client-launcher "$c/bin/$(printf '%s' "$one" | tr '_' '-')"
done
if [ "$(uname -s)" = OpenBSD ]; then
  mkdir -p "$c/share/rc.d"
  install -m 0644 packaging/fn_reader.rc.in "$c/share/rc.d/fn_reader.rc.in"
else
  mkdir -p "$c/share/systemd"
  install -m 0644 packaging/fn-reader.service.in "$c/share/systemd/fn-reader.service.in"
fi
install -m 0644 packaging/fn-reader.conf.example "$c/share/fn-reader.conf.example"
install -m 0644 packaging/fn-reader.caddy "$c/share/caddy/fn-reader.caddy"
install -m 0644 packaging/clients-README.txt "$c/README.txt"
install -m 0644 docs/web.md "$top/share/fn/docs/web.md"
install -m 0644 docs/agents.md "$top/share/fn/docs/agents.md"
echo "staged the clients under $c"
