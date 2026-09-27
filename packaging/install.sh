#!/bin/sh
# Install an unpacked fn release onto this machine.  A release carries this
# file at its top (fn/install.sh); it is /bin/sh and runs nothing else of fn's
# except the release's own bin/fn.
#
#   sh fn/install.sh [--prefix DIR] [--node DIR] [--user NAME] [--no-service]
#
#   --prefix   where the release goes (default /opt/fn; /usr/local/fn on
#              OpenBSD).  It must not exist: an installation is one
#              directory, and a reinstall removes the old one first
#              (stop, export, remove, install, import, start).
#   --node     the node directory: fn.toml, store/, tls/, log/ (default
#              /var/lib/fn; /var/fn on OpenBSD).  Created if absent, owned by
#              the service account; an existing one is kept.
#   --user     the service account (default fn; _fn on OpenBSD), created
#              if absent (root only).
#   --no-service  create no account and install no unit: the rendered
#              service file is written to NODE/ for you to use or not.
#
# It checks every file of the release against SHA256SUMS first.  When the
# node directory already holds a configuration and a store, it asks the
# release's own `fn operator NODE/fn.toml status` before copying anything,
# and refuses a store this release cannot open (another store format): export
# it with the release that wrote it, install, then import.  It starts nothing.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
system=$(uname -s)
case $system in
  Linux) prefix=/opt/fn node=/var/lib/fn user=fn ;;
  OpenBSD) prefix=/usr/local/fn node=/var/fn user=_fn ;;
  *) echo "install: fn releases are for Linux and OpenBSD, not $system" >&2; exit 2 ;;
esac
service=yes
while [ "$#" -gt 0 ]; do
  case $1 in
    --prefix) [ "$#" -ge 2 ] || { echo 'install: --prefix DIR' >&2; exit 2; }; prefix=$2; shift 2 ;;
    --node) [ "$#" -ge 2 ] || { echo 'install: --node DIR' >&2; exit 2; }; node=$2; shift 2 ;;
    --user) [ "$#" -ge 2 ] || { echo 'install: --user NAME' >&2; exit 2; }; user=$2; shift 2 ;;
    --no-service) service=no; shift ;;
    *) echo "install: unknown argument $1 (sh install.sh [--prefix DIR] [--node DIR] [--user NAME] [--no-service])" >&2; exit 2 ;;
  esac
done
for path in "$prefix" "$node"; do
  case $path in /*) ;; *) echo "install: $path must be absolute" >&2; exit 2 ;; esac
  case $path in *[!A-Za-z0-9_./-]*) echo "install: $path contains unsupported characters" >&2; exit 2 ;; esac
done
case $user in ''|*[!A-Za-z0-9_-]*) echo "install: invalid account name $user" >&2; exit 2 ;; esac
[ -x "$here/bin/fn" ] && [ -x "$here/libexec/fn/fn-host" ] && [ -s "$here/SHA256SUMS" ] || {
  echo "install: $here is not an unpacked fn release" >&2; exit 4; }
if [ "$system" = OpenBSD ]; then template=$here/share/fn/rc.d/fn.rc.in
else template=$here/share/fn/systemd/fn.service.in; fi
[ -s "$template" ] || { echo "install: this release is not built for $system (no $template)" >&2; exit 4; }

echo "== checking the release against SHA256SUMS"
if command -v sha256sum >/dev/null 2>&1; then
  (cd "$here" && sha256sum -c --quiet SHA256SUMS) || { echo 'install: SHA256SUMS does not match' >&2; exit 4; }
else
  (cd "$here" && sha256 -c -q SHA256SUMS) || { echo 'install: SHA256SUMS does not match' >&2; exit 4; }
fi
"$here/bin/fn" --version

config=$node/fn.toml
if [ -f "$config" ]; then
  echo "== $config exists: asking this release whether it opens that node's store"
  set +e
  answer=$("$here/bin/fn" operator "$config" status 2>&1)
  rc=$?
  set -e
  printf '%s\n' "$answer" | sed 's/^/   /'
  case $answer in
    *store-format*)
      echo "install: this release refuses that store's format: export it with the release that wrote it (fn operator $config store export DIR), move the node directory aside, install, init, then store import DIR" >&2
      exit 4 ;;
  esac
  [ "$rc" -eq 0 ] || echo "install: status answered $rc (see above); the store is not a format refusal, so the install continues"
fi

if [ "$here" != "$prefix" ]; then
  [ ! -e "$prefix" ] || {
    echo "install: $prefix exists: an installation is one directory; stop the node and remove $prefix first (its store lives in $node, not there)" >&2
    exit 4; }
  mkdir -p "$(dirname -- "$prefix")"
  cp -Rp "$here" "$prefix"
  echo "installed $prefix"
fi

render() {
  sed -e "s|@PREFIX@|$prefix|g" -e "s|@NODE@|$node|g" -e "s|@USER@|$user|g" "$template"
}
if [ "$service" = no ]; then
  mkdir -p "$node"
  if [ "$system" = OpenBSD ]; then out=$node/fn.rc; else out=$node/fn.service; fi
  render > "$out"
  echo "rendered $out (not installed; --no-service)"
  exit 0
fi
[ "$(id -u)" -eq 0 ] || { echo 'install: installing the service needs root (or pass --no-service)' >&2; exit 2; }
if ! id "$user" >/dev/null 2>&1; then
  if [ "$system" = OpenBSD ]; then
    useradd -L daemon -d "$node" -s /sbin/nologin -c 'fn news node' "$user"
  else
    useradd --system --home-dir "$node" --no-create-home --shell /usr/sbin/nologin "$user"
  fi
  echo "created account $user"
fi
mkdir -p "$node"
chown "$user" "$node"
chmod 0750 "$node"
if [ "$system" = OpenBSD ]; then
  render > /etc/rc.d/fn
  chmod 0555 /etc/rc.d/fn
  echo "installed /etc/rc.d/fn (start it: rcctl enable fn; rcctl start fn)"
else
  render > /etc/systemd/system/fn.service
  systemctl daemon-reload
  echo "installed /etc/systemd/system/fn.service (start it: systemctl enable --now fn)"
fi
