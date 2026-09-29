#!/bin/sh
# Install an unpacked fn release onto this machine, move a node to the next
# release beside the one it runs, or back.  A release carries this file at
# its top (fn/install.sh); it is /bin/sh and runs nothing else of fn's
# except a release's own bin/fn.
#
#   sh fn/install.sh [--prefix DIR] [--node DIR] [--user NAME] [--no-service] [--reader]
#   sh fn/install.sh --upgrade [--prefix DIR] [--node DIR] [--no-service]
#   sh PREFIX/current/install.sh --rollback [--prefix DIR] [--node DIR] [--no-service]
#
#   --prefix   the installation (default /opt/fn; /usr/local/fn on OpenBSD).
#              PREFIX/releases/VERSION+REV holds each installed release,
#              PREFIX/current links to the one that runs (the service starts
#              PREFIX/current/bin/fn) and PREFIX/previous to the one that
#              ran before it.  A first install makes releases/ and current.
#              A PREFIX that exists without releases/ is an installation
#              from before this layout: refused by name (stop that node,
#              move PREFIX aside, install; the store lives in NODE).
#   --node     the node directory: fn.toml, store/, tls/, log/ (default
#              /var/lib/fn; /var/fn on OpenBSD).  Created if absent, owned by
#              the service account; an existing one is kept.
#   --user     the service account (default fn; _fn on OpenBSD), created
#              if absent (root only).
#   --no-service  create no account and install no unit: the rendered
#              service file is written to NODE/ for you to use or not.  With
#              --upgrade or --rollback the node is neither stopped nor
#              started: stop it first, and start it through
#              PREFIX/current/bin/fn afterwards (what the unit does).
#   --reader   turn on the node's own web face (docs/web.md): add a [web]
#              table to NODE/fn.toml, listening on 127.0.0.1:8920 behind
#              an HTTPS proxy on this machine (proxied = true; the Caddy
#              block is share/fn/caddy/fn-web.caddy).  The face is part of
#              the node: no other account, service or program.  An fn.toml
#              that already has a [web] table is left as it is; with no
#              fn.toml yet (before `mission'), run this again afterwards
#              (sh PREFIX/current/install.sh --reader).  The node reads the
#              table when it starts.
#   --upgrade  run from the unpacked next release: check it, print the gap
#              to expect, install it beside the current release, stop the
#              node, ask the next release whether it opens the store, switch
#              current to it (previous keeps the one before), render the
#              unit from it, start the node and wait for `health'.  A
#              refusal puts nothing in place: the node starts again on the
#              release it ran.
#   --rollback run from PREFIX/current/install.sh: the switch back to
#              previous, with the same stop, ask, switch, start and health.
#              Refused by name when there is no previous release, or when
#              that release refuses the store.
#
# The gap: "the node will be away for about N s", read from the last
# OWNER-OPEN line of NODE/log/fn.log, whose `ms=' is the milliseconds the
# node's last start took from the image's entry to the open (recovery
# included; host/native/owner.lisp).  A measurement, not a promise: the
# stop, the heap probe and the service manager add their own seconds, and
# the upgrade prints the interval it measured when the node answers.
#
# There are no migrations (D34, D38).  A release opens only a store of its
# own format, and the verdict is the release's own: `fn operator
# NODE/fn.toml status' on the stopped node answers `open refused
# reason=store-format: not an fn store of this release: redeploy fresh'.
# This file refuses by that name and decides nothing about the store.  It
# checks every file of a release against SHA256SUMS before using it.  A
# first install starts nothing.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
system=$(uname -s)
case $system in
  Linux) prefix=/opt/fn node=/var/lib/fn user=fn ;;
  OpenBSD) prefix=/usr/local/fn node=/var/fn user=_fn ;;
  *) echo "install: fn releases are for Linux and OpenBSD, not $system" >&2; exit 2 ;;
esac
usage='sh install.sh [--prefix DIR] [--node DIR] [--user NAME] [--no-service] [--reader] | --upgrade | --rollback'
service=yes reader=no mode=install prefix_given=no
while [ "$#" -gt 0 ]; do
  case $1 in
    --prefix) [ "$#" -ge 2 ] || { echo 'install: --prefix DIR' >&2; exit 2; }; prefix=$2; prefix_given=yes; shift 2 ;;
    --node) [ "$#" -ge 2 ] || { echo 'install: --node DIR' >&2; exit 2; }; node=$2; shift 2 ;;
    --user) [ "$#" -ge 2 ] || { echo 'install: --user NAME' >&2; exit 2; }; user=$2; shift 2 ;;
    --no-service) service=no; shift ;;
    --reader) reader=yes; shift ;;
    --upgrade) mode=upgrade; shift ;;
    --rollback) mode=rollback; shift ;;
    *) echo "install: unknown argument $1 ($usage)" >&2; exit 2 ;;
  esac
done
# --rollback from an installed release finds its installation by where it is.
if [ "$mode" = rollback ] && [ "$prefix_given" = no ]; then
  case $here in
    */current) prefix=${here%/current} ;;
    */releases/*) prefix=${here%/releases/*} ;;
  esac
fi
for path in "$prefix" "$node"; do
  case $path in /*) ;; *) echo "install: $path must be absolute" >&2; exit 2 ;; esac
  case $path in *[!A-Za-z0-9_./-]*) echo "install: $path contains unsupported characters" >&2; exit 2 ;; esac
done
case $user in ''|*[!A-Za-z0-9_-]*) echo "install: invalid account name $user" >&2; exit 2 ;; esac
if [ "$reader" = yes ] && [ "$mode" != install ]; then
  echo "install: --reader goes with an install; afterwards: sh $prefix/current/install.sh --reader" >&2; exit 2
fi
if [ "$mode" != install ] && [ "$service" = yes ] && [ "$(id -u)" -ne 0 ]; then
  echo "install: --$mode stops and starts the service and needs root (or pass --no-service and stop and start the node yourself)" >&2; exit 2
fi
config=$node/fn.toml
if [ "$system" = OpenBSD ]; then template_rel=share/fn/rc.d/fn.rc.in
else template_rel=share/fn/systemd/fn.service.in; fi

# --- a release ---------------------------------------------------------------
check_release() {  # $1: an unpacked or installed release; its bytes are its SHA256SUMS'
  [ -x "$1/bin/fn" ] && [ -x "$1/libexec/fn/fn-host" ] && [ -s "$1/SHA256SUMS" ] || {
    echo "install: $1 is not an unpacked fn release" >&2; exit 4; }
  [ -s "$1/$template_rel" ] || { echo "install: this release is not built for $system (no $1/$template_rel)" >&2; exit 4; }
  echo "== checking $1 against SHA256SUMS"
  if command -v sha256sum >/dev/null 2>&1; then
    (cd "$1" && sha256sum -c --quiet SHA256SUMS) || { echo "install: $1: SHA256SUMS does not match" >&2; exit 4; }
  else
    (cd "$1" && sha256 -c -q SHA256SUMS) || { echo "install: $1: SHA256SUMS does not match" >&2; exit 4; }
  fi
}
release_name() {  # $1: a release; sets name=VERSION+REV from `fn VERSION (REV)'
  dir=$1
  printed=$("$dir/bin/fn" --version) || { echo "install: $dir/bin/fn --version failed" >&2; exit 4; }
  echo "$printed"
  set -- $printed
  [ "${1:-}" = fn ] && [ -n "${2:-}" ] && [ -n "${3:-}" ] || {
    echo "install: $dir/bin/fn --version printed '$printed', not 'fn VERSION (REV)'" >&2; exit 4; }
  rev=${3#\(}; rev=${rev%\)}
  case "$2$rev" in ''|*[!A-Za-z0-9.]*) echo "install: unusable release name from '$printed'" >&2; exit 4 ;; esac
  name=$2+$rev
}
ask() {  # $1: a release.  Its own verdict on the node's store (the node stopped).
  echo "== asking $1/bin/fn whether it opens the store of $config"
  set +e
  answer=$("$1/bin/fn" operator "$config" status 2>&1)
  rc=$?
  set -e
  printf '%s\n' "$answer" | sed 's/^/   /'
  case $answer in *reason=store-format*) return 1 ;; esac
  [ "$rc" -eq 0 ] || echo "install: status answered $rc (see above); the store is not a format refusal, so this continues"
  return 0
}
install_beside() {  # $1: the unpacked release, $2: its name -> PREFIX/releases/NAME, staged then renamed
  stage=$prefix/releases/.$2.new
  rm -rf "$stage"
  mkdir -p "$prefix/releases"
  cp -Rp "$1" "$stage"
  mv "$stage" "$prefix/releases/$2"
  echo "installed $prefix/releases/$2"
}
switch_to() {  # $1: the release that runs next (releases/NAME), $2: the one to keep as previous
  ln -sfn "$2" "$prefix/previous"
  ln -sfn "$1" "$prefix/current"
  echo "current -> $1 (previous -> $2)"
}

# --- the node, through the service manager ----------------------------------
gap_line() {  # the gap to expect, from the node's last start
  log=$node/log/fn.log
  last=$(grep 'OWNER-OPEN ' "$log" 2>/dev/null | tail -n 1 || true)
  ms=
  case $last in *" ms="*) ms=${last##* ms=}; ms=${ms%% *} ;; esac
  case $ms in ''|*[!0-9]*) ms= ;; esac
  if [ -n "$ms" ]; then
    gap=$(( (ms + 999) / 1000 ))
    echo "the node will be away for about $gap s: its last start took $ms ms from the image's entry to the open ($log: $last); the stop and the heap probe add their own seconds"
  else
    gap=
    echo "the gap is unmeasured: no OWNER-OPEN line with ms= in $log (the node's log is elsewhere, or it never ran)"
  fi
}
stop_node() {
  if [ "$service" = no ]; then
    echo "== not stopping the node (--no-service): it must be stopped already"
    return 0
  fi
  echo "== stopping the node"
  stopped_at=$(date +%s)
  if [ "$system" = OpenBSD ]; then rcctl stop fn; else systemctl stop fn; fi
}
start_node() {
  [ "$service" = yes ] || return 0
  echo "== starting the node"
  if [ "$system" = OpenBSD ]; then rcctl start fn; else systemctl start fn; fi
}
health_wait() {  # the node on PREFIX/current answers `health'; the interval since the stop
  if [ "$service" = no ]; then
    echo "== start the node through $prefix/current/bin/fn, as the unit does: $prefix/current/bin/fn operator $config run"
    return 0
  fi
  deadline=$(( $(date +%s) + 180 ))
  while :; do
    set +e
    line=$("$prefix/current/bin/fn" operator "$config" health 2>/dev/null | head -n 1)
    set -e
    case $line in
      "health exit="*" state=not-running"*|"health exit="*" state=fenced"*|"health exit=19"*|"") ;;
      "health exit="*)
        away=$(( $(date +%s) - stopped_at ))
        echo "$line"
        echo "the node answered on $(readlink "$prefix/current") after $away s away${gap:+ (expected about $gap s)}"
        return 0 ;;
    esac
    [ "$(date +%s)" -lt "$deadline" ] || {
      echo "install: the node did not answer health within 180 s of its start (last: '${line:-nothing}'); see $prefix/current/bin/fn operator $config health and the service log" >&2
      exit 4; }
    sleep 1
  done
}
render() {  # $1: template
  sed -e "s|@PREFIX@|$prefix|g" -e "s|@NODE@|$node|g" -e "s|@USER@|$user|g" "$1"
}
render_service() {  # the unit of the release on PREFIX/current, installed (root) or left in NODE/
  template=$prefix/current/$template_rel
  if [ "$service" = no ]; then
    mkdir -p "$node"
    if [ "$system" = OpenBSD ]; then out=$node/fn.rc; else out=$node/fn.service; fi
    render "$template" > "$out"
    echo "rendered $out (not installed; --no-service)"
    return 0
  fi
  if [ "$system" = OpenBSD ]; then
    render "$template" > /etc/rc.d/fn
    chmod 0555 /etc/rc.d/fn
    echo "installed /etc/rc.d/fn"
  else
    render "$template" > /etc/systemd/system/fn.service
    systemctl daemon-reload
    echo "installed /etc/systemd/system/fn.service"
  fi
}
# --reader: the node's own web face, a [web] table in its fn.toml (docs/web.md).
web_face() {
  [ "$reader" = yes ] || return 0
  if [ ! -f "$config" ]; then
    echo "--reader: no $config yet: after \`fn operator $config mission ...' writes it, run: sh $prefix/current/install.sh --reader"
    return 0
  fi
  if grep -q '^[[:space:]]*\[web\]' "$config"; then
    echo "--reader: $config already has a [web] table; left as it is"
    return 0
  fi
  domain=$(uname -n)
  case $domain in ''|*[!A-Za-z0-9.-]*) domain=localhost ;; esac
  printf '\n[web]\nport = 8920\nhost = "127.0.0.1"\nproxied = true\nsite = "Friends news"\ndomain = "%s"\n' \
    "$domain" >> "$config"
  echo "--reader: added [web] to $config (127.0.0.1:8920, behind the HTTPS proxy: $prefix/current/share/fn/caddy/fn-web.caddy); edit site and domain, then restart the node"
}

# --- --upgrade ---------------------------------------------------------------
if [ "$mode" = upgrade ]; then
  [ -d "$prefix/releases" ] && [ -L "$prefix/current" ] || {
    echo "install: $prefix holds no installation (releases/ and current): a first install is: sh $here/install.sh" >&2; exit 4; }
  [ -f "$config" ] || { echo "install: $config does not exist: nothing to upgrade" >&2; exit 4; }
  check_release "$here"
  release_name "$here"
  running=$(readlink "$prefix/current")
  if [ -e "$prefix/releases/$name" ]; then
    if [ "$running" = "releases/$name" ]; then
      echo "install: $name is already installed at $prefix/releases/$name and is current" >&2
    else
      echo "install: $name is already installed at $prefix/releases/$name (to run it again: sh $prefix/current/install.sh --rollback when it is previous)" >&2
    fi
    exit 4
  fi
  gap_line
  install_beside "$here" "$name"
  stop_node
  if ! ask "$prefix/releases/$name"; then
    rm -rf "$prefix/releases/$name"
    start_node
    echo "install: $name refuses that store's format (there are no migrations); nothing switched, $prefix/releases/$name removed, the node runs on as before: redeploy fresh (stop the node, move $node aside, install, init)" >&2
    exit 4
  fi
  switch_to "releases/$name" "$running"
  render_service
  start_node
  health_wait
  exit 0
fi

# --- --rollback --------------------------------------------------------------
if [ "$mode" = rollback ]; then
  [ -d "$prefix/releases" ] && [ -L "$prefix/current" ] || {
    echo "install: $prefix holds no installation (releases/ and current)" >&2; exit 4; }
  [ -L "$prefix/previous" ] || { echo "install: nothing to roll back to: $prefix/previous is absent" >&2; exit 4; }
  [ -f "$config" ] || { echo "install: $config does not exist: nothing to roll back" >&2; exit 4; }
  running=$(readlink "$prefix/current")
  before=$(readlink "$prefix/previous")
  [ -d "$prefix/$before" ] || { echo "install: $prefix/previous -> $before, which is not there" >&2; exit 4; }
  check_release "$prefix/$before"
  release_name "$prefix/$before"
  gap_line
  stop_node
  if ! ask "$prefix/$before"; then
    start_node
    echo "install: $name ($before) refuses that store's format: the store moved on since it ran (there are no migrations); nothing switched, the node runs on $running: redeploy fresh under $name if you must (stop the node, move $node aside, install, init)" >&2
    exit 4
  fi
  switch_to "$before" "$running"
  render_service
  start_node
  health_wait
  exit 0
fi

# --- install -----------------------------------------------------------------
check_release "$here"
release_name "$here"
if [ -e "$prefix" ] && [ ! -d "$prefix/releases" ]; then
  echo "install: $prefix exists and holds no releases/: an installation from before the releases layout; stop that node, move $prefix aside and install (its store lives in $node, not there)" >&2
  exit 4
fi
installed_here=no
if [ -d "$prefix/releases/$name" ]; then
  if [ "$here" -ef "$prefix/releases/$name" ]; then
    installed_here=yes
  else
    echo "install: $name is already installed at $prefix/releases/$name (a node moves to a release by: sh fn/install.sh --upgrade; back by: sh $prefix/current/install.sh --rollback)" >&2
    exit 4
  fi
elif [ -L "$prefix/current" ]; then
  echo "install: $prefix already runs $(readlink "$prefix/current"); this release goes beside it by: sh $here/install.sh --upgrade" >&2
  exit 4
fi
if [ -f "$config" ] && [ "$installed_here" = no ]; then
  echo "== $config exists: asking this release whether it opens that node's store"
  if ! ask "$here"; then
    echo "install: this release refuses that store's format (there are no migrations): redeploy fresh: move the node directory aside, install, then init" >&2
    exit 4
  fi
fi
if [ "$installed_here" = no ]; then
  install_beside "$here" "$name"
  ln -sfn "releases/$name" "$prefix/current"
  echo "current -> releases/$name"
fi
if [ "$service" = no ]; then
  render_service
  web_face
  exit 0
fi
[ "$(id -u)" -eq 0 ] || { echo 'install: installing the service needs root (or pass --no-service)' >&2; exit 2; }
mkdir -p "$node"
if ! id "$user" >/dev/null 2>&1; then
  if [ "$system" = OpenBSD ]; then
    useradd -L daemon -d "$node" -s /sbin/nologin -c 'fn news node' "$user"
  else
    useradd --system --home-dir "$node" --no-create-home --shell /usr/sbin/nologin "$user"
  fi
  echo "created account $user"
fi
chown "$user" "$node"
chmod 0750 "$node"
render_service
if [ "$system" = OpenBSD ]; then echo "start it: rcctl enable fn; rcctl start fn"
else echo "start it: systemctl enable --now fn"; fi
web_face
