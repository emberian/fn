#!/usr/bin/env python3
"""Install one commit of fn as a running service on a box, and say how.

This is the deployment the gates are not: a gate builds a directory, drives
it and deletes it.  `live_service.py` puts a tree under `~/fn-live`, gives it
a store with its groups, installs a unit that survives a logout, starts it,
and leaves it running.

    python3 tools/live_service.py install 52eb0db --host persvati \\
        --node fnA --port 11190 --peer fnB --peer-host hbox --peer-port 11190
    python3 tools/live_service.py status --host persvati
    python3 tools/live_service.py stop --host persvati

`packaging/fn.service` is the system unit and assumes `/usr/local/lib/fn`,
`/etc/fn` and a `fn` user.  Nothing here has root on either box, so the unit
installed is that file with its four paths moved under `$HOME/fn-live` and
its `User=`/`Group=` and `ProtectHome=` lines dropped -- a user unit runs as
the invoking user and cannot read a hardening directive about another one.
The installed unit is written out in full in the evidence, so the difference
from the packaged file is reviewable rather than asserted.

Where `systemctl --user` is not available the fallback is a `setsid` wrapper
(`~/fn-live/run.sh`) that detaches the process and writes a pid file.  That
is NOT a supervised service: nothing restarts it, nothing bounds its stop,
and a reboot does not bring it back.  The evidence records which of the two a
host got, and `--supervisor` forces the choice for a comparison.

Certificates are installed from the box's own cache before the first start:
`fn run` loads books through ACL2 and an uncertified book would be certified
at start, inside the service.  If the cache has no pair for a book, this
tool says so and the start will be slow or will fail; it does not certify.
"""

import argparse
import datetime as dt
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parent))
from deploy_gate import Step, compact, resolve            # noqa: E402
from farm import HOSTS as FARM_HOSTS                      # noqa: E402

LIVE = "$HOME/fn-live"
DEFAULT_GROUPS = ("fn.letters", "fn.test")
UNIT_NAME = "fn.service"


class Live:
    """One host's live installation, and every command it took to make it."""

    def __init__(self, host: str, repo: Path, commit: str, rev: str, node: str,
                 port: int, groups: tuple[str, ...], acl2: str, cache: str,
                 supervisor: str):
        self.host = host
        self.repo = repo
        self.commit = commit
        self.rev = rev
        self.node = node
        self.port = port
        self.groups = groups
        self.acl2 = acl2
        self.cache = cache
        self.supervisor = supervisor
        self.tree = "{}/fn".format(LIVE)
        self.store = "{}/store".format(LIVE)
        self.config = "{}/fn.toml".format(LIVE)
        self.log = "{}/fn.log".format(LIVE)
        self.peers = "{}/peers".format(LIVE)
        self.steps: list[Step] = []
        self.facts: dict[str, str] = {}
        self.notes: list[str] = []

    # -- plumbing ---------------------------------------------------------
    def sh(self, name: str, script: str, timeout: int = 600, expect=0,
           note: str = "") -> Step:
        start = time.monotonic()
        try:
            done = subprocess.run(
                ["ssh", "-o", "BatchMode=yes", self.host, "bash", "-s"],
                input=script.encode(), stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=timeout)
            rc, output = done.returncode, done.stdout.decode("utf-8", "replace")
        except subprocess.TimeoutExpired:
            rc, output = 124, "timed out after {}s".format(timeout)
        step = Step(name, compact(script), rc, output,
                    time.monotonic() - start, note, expect)
        self.steps.append(step)
        print("  {:<34} rc={} {}".format(name, rc, step.first_line[:90]), flush=True)
        return step

    def push(self, name: str, text: str, target: str, mode: str = "644") -> Step:
        return self.sh(name, "mkdir -p $(dirname {t})\ncat > {t} <<'FN_LIVE_EOF'\n{b}"
                             "FN_LIVE_EOF\nchmod {m} {t}\n".format(
                                 t=target, b=text if text.endswith("\n") else text + "\n",
                                 m=mode))

    # -- the pieces -------------------------------------------------------
    def ship(self) -> Step:
        archive = subprocess.run(["git", "-C", str(self.repo), "archive", self.commit],
                                 stdout=subprocess.PIPE, check=True).stdout
        start = time.monotonic()
        done = subprocess.run(
            ["ssh", "-o", "BatchMode=yes", self.host,
             "mkdir -p {t} && rm -rf {t} && mkdir -p {t} && tar -x -C {t}".format(
                 t=self.tree)],
            input=archive, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=1800)
        step = Step("ship {}".format(self.rev), "git archive {} | tar -x -C {}".format(
            self.rev, self.tree), done.returncode,
            done.stdout.decode("utf-8", "replace"), time.monotonic() - start)
        self.steps.append(step)
        print("  {:<34} rc={}".format(step.name, step.rc), flush=True)
        return step

    def certificates(self) -> Step:
        step = self.sh("install certificates from the cache", """
cd {tree} || exit 9
export FN_ACL2={acl2} FN_CERT_CACHE={cache} ACL2_BOOK_HASH_ALISTP=NIL
python3 tools/certs.py install --root {tree} --cache {cache} 2>&1 | tail -4
""".format(tree=self.tree, acl2=self.acl2, cache=self.cache), timeout=1800)
        self.facts["certificates"] = step.first_line or "?"
        count = self.sh("certificates on disk",
                        "ls {}/books/*.cert 2>/dev/null | wc -l".format(self.tree))
        self.facts["certificates on disk"] = count.first_line
        if count.first_line.strip() in ("", "0"):
            self.notes.append(
                "no certificate landed in {}: the box's cache holds no pair for "
                "this revision's books, so `fn run` would certify inside the "
                "service. Run a gate for this commit first.".format(self.tree))
        return step

    def configure(self) -> Step:
        groups = " ".join("--group {}".format(g) for g in self.groups)
        step = self.sh("fn init", """
cd {tree} || exit 9
export FN_ACL2={acl2} ACL2_BOOK_HASH_ALISTP=NIL
mkdir -p {live}
./bin/fn --config {config} init --store {store} {groups} \\
  --listen 127.0.0.1:{port} --agent {node}@fn.invalid --log {log} \\
  --acl2 {acl2} --control {store}/control.sock --force 2>&1 | tail -20
""".format(tree=self.tree, live=LIVE, config=self.config, store=self.store,
           groups=groups, port=self.port, node=self.node, log=self.log,
           acl2=self.acl2), timeout=2400)
        self.facts["groups"] = ", ".join(self.groups)
        self.facts["listener"] = "127.0.0.1:{}".format(self.port)
        return step

    def peer_record(self, peer: str, peer_host: str, peer_port: int) -> Step:
        """One record naming the other box, in the shape specs/peering.md 1.2 has.

        `fn peer add` does not exist on this tree: `bin/fn`'s subcommands are
        init, run, post, group, status, recover and anchor, and
        `tools/run_store.py` has no `peer` verb either.  So this writes the
        same stub `tools/twonode_gate.py` writes, with one difference that
        matters and is stated in the file: the transport address is the peer
        BOX, not loopback.  Nothing on this tree reads it. When the peering
        lane lands its CLI, this function calls it and deletes the stub.
        """
        probe = self.sh("peer CLI on this tree", """
cd {tree} || exit 9
if ./bin/fn peer --help >/dev/null 2>&1; then echo FN-PEER
elif python3 tools/run_store.py --store /nonexistent peer --help >/dev/null 2>&1; then
  echo STORE-PEER
else echo NONE; fi
""".format(tree=self.tree))
        kind = (probe.output.strip().splitlines() or ["NONE"])[-1]
        self.facts["peer records"] = kind.lower()
        if kind == "FN-PEER":
            return self.sh("peer record for {}".format(peer), """
cd {tree} || exit 9
./bin/fn --config {config} peer add {peer} {host}:{port} {peer}.fn.invalid 2>&1 | tail -5
""".format(tree=self.tree, config=self.config, peer=peer, host=peer_host,
           port=peer_port), timeout=900)
        stub = """;; A peer record for node {them}, held by node {us} ({us_host}).
;; specs/peering.md 1.2: (fn-cfg-peer-make name path-identity transport
;;                                         inbound outbound auth).
;; NOTHING ON THIS TREE READS THIS FILE.  `bin/fn` has no `peer` subcommand
;; and `tools/run_store.py` has no `peer` verb on {rev}; this file records the
;; configuration the two boxes are meant to hold so that it is reviewable
;; before the peering lane lands the `(:set-peer record)` delta, and so the
;; two-node harness's shape and the live deployment's shape are the same one.
;;
;; The transport address is the PEER BOX, not loopback, and that is exactly
;; why no transit happens today: `fn run` refuses a non-loopback [listener]
;; host (bin/fn, and docs/architecture.md does not authorize a public
;; listener), so {them} is not reachable from {us_host} without a tunnel.
(fn-cfg-peer-make
  "{them}"                                  ; name: the local label
  "{them}.fn.invalid"                       ; path-identity, RFC 5537 3.2
  (:nntp "{host}" {port})                   ; transport: the peer box
  (("fn.*") 1048576 4)                      ; inbound: groups, max octets, max in flight
  (("fn.*") nil 64 1000)                    ; outbound: groups, streaming, queue, backoff ms
  (:source-address "{host}"))               ; auth, specs/peering.md 6
""".format(them=peer, us=self.node, us_host=self.host, rev=self.rev,
           host=peer_host, port=peer_port)
        step = self.push("peer record for {} (stub)".format(peer), stub,
                         "{}/{}.peer".format(self.peers, peer))
        step.note = ("no peer CLI on this tree; the record is a reviewable file "
                     "that nothing reads")
        self.notes.append(
            "the peer record {}/{}.peer is a file, not a configuration record: "
            "no code on {} reads it, so these two nodes are peers on paper "
            "only.".format(self.peers, peer, self.rev))
        return step

    # -- the unit ---------------------------------------------------------
    def unit_text(self, home: str) -> str:
        """`packaging/fn.service`, relocated, with the system-only lines gone."""
        source = (self.repo / "packaging/fn.service").read_text()
        keep = []
        for line in source.splitlines():
            head = line.split("=", 1)[0].strip()
            if head in ("User", "Group", "ProtectHome", "ProtectSystem",
                        "PrivateDevices", "ProtectControlGroups",
                        "ProtectKernelTunables", "ProtectKernelModules",
                        "ProtectClock", "WantedBy", "After", "Wants"):
                continue
            keep.append(line)
        text = "\n".join(keep)
        live = "{}/fn-live".format(home)
        text = text.replace("/usr/local/lib/fn", "{}/fn".format(live))
        text = text.replace("/etc/fn/fn.toml", "{}/fn.toml".format(live))
        text = text.replace("/var/lib/fn/store", "{}/store".format(live))
        text = text.replace("/var/log/fn/fn.log", "{}/fn.log".format(live))
        text = text.replace("ReadWritePaths=/var/lib/fn /var/log/fn",
                            "ReadWritePaths={}".format(live))
        text = text.replace("[Install]", "[Install]\nWantedBy=default.target")
        # systemd does not expand `$HOME` in an `Environment=` value, so the
        # ACL2 path is written out against this user's real home.
        acl2 = self.acl2.replace("$HOME", home).replace("~", home)
        text = text.replace("Environment=PYTHONUNBUFFERED=1",
                            "Environment=PYTHONUNBUFFERED=1\n"
                            "Environment=FN_ACL2={}\n".format(acl2) +
                            "Environment=ACL2_BOOK_HASH_ALISTP=NIL")
        return text

    WRAPPER = """#!/bin/sh
# The fallback supervisor: `setsid` and a pid file, documented as NOT a
# service.  Nothing restarts this, nothing bounds its stop, a reboot loses
# it.  It exists so a box without a user systemd still runs fn the same way.
set -eu
live={live}
case "${{1:-start}}" in
start)
  if [ -f "$live/fn.pid" ] && kill -0 "$(cat "$live/fn.pid")" 2>/dev/null; then
    echo "already running pid=$(cat "$live/fn.pid")"; exit 0; fi
  cd "$live/fn"
  FN_ACL2={acl2} ACL2_BOOK_HASH_ALISTP=NIL PYTHONUNBUFFERED=1 \\
    setsid nohup ./bin/fn --config "$live/fn.toml" run \\
    >> "$live/service.out" 2>&1 < /dev/null &
  echo $! > "$live/fn.pid"
  echo "started pid=$(cat "$live/fn.pid")" ;;
stop)
  [ -f "$live/fn.pid" ] || {{ echo "not running"; exit 0; }}
  kill -TERM "$(cat "$live/fn.pid")" 2>/dev/null || true
  rm -f "$live/fn.pid"; echo stopped ;;
status)
  if [ -f "$live/fn.pid" ] && kill -0 "$(cat "$live/fn.pid")" 2>/dev/null; then
    echo "running pid=$(cat "$live/fn.pid")"; else echo "not running"; fi ;;
esac
"""

    def choose_supervisor(self) -> str:
        if self.supervisor != "auto":
            self.facts["supervisor"] = self.supervisor + " (forced by --supervisor)"
            return self.supervisor
        probe = self.sh("systemctl --user available", """
if systemctl --user is-system-running >/dev/null 2>&1 || \\
   [ "$(systemctl --user is-system-running 2>/dev/null)" = degraded ]; then
  echo "SYSTEMD $(loginctl show-user "$(id -un)" -p Linger 2>/dev/null)"
else echo SETSID; fi
""")
        kind = "systemd" if "SYSTEMD" in probe.output else "setsid"
        self.facts["supervisor"] = kind + (
            " (systemctl --user)" if kind == "systemd" else
            " (no user systemd; a detached process, not a supervised service)")
        if "Linger=no" in probe.output:
            self.notes.append(
                "linger is off for this user on {}: the user manager, and so the "
                "service, stops when the last session closes. `loginctl "
                "enable-linger` needs an administrator; until then this is a "
                "service for as long as a session exists.".format(self.host))
        return kind

    def install_unit(self, kind: str) -> Step:
        home = self.sh("home", "echo $HOME").first_line
        if kind == "systemd":
            self.push("write the user unit", self.unit_text(home),
                      "$HOME/.config/systemd/user/{}".format(UNIT_NAME))
            return self.sh("enable the unit", """
systemctl --user daemon-reload
systemctl --user enable {unit} 2>&1 | tail -2
systemctl --user is-enabled {unit}
""".format(unit=UNIT_NAME))
        self.push("write the setsid wrapper",
                  self.WRAPPER.format(live="$HOME/fn-live", acl2=self.acl2),
                  "{}/run.sh".format(LIVE), mode="755")
        return self.sh("wrapper is executable", "ls -l {}/run.sh".format(LIVE))

    def start(self, kind: str, ready_seconds: int = 900) -> Step:
        if kind == "systemd":
            self.sh("start the unit", "systemctl --user restart {}".format(UNIT_NAME),
                    timeout=ready_seconds)
        else:
            self.sh("start the wrapper", "{}/run.sh start".format(LIVE),
                    timeout=ready_seconds)
        return self.sh("listener is up", """
for i in $(seq 1 {n}); do
  if (exec 3<>/dev/tcp/127.0.0.1/{port}) 2>/dev/null; then
    echo "LISTENING {port}"; exec 3<&-; exit 0; fi
  sleep 5
done
echo "NOT-LISTENING {port} after {n} probes"
tail -20 {log} 2>/dev/null
exit 1
""".format(n=max(6, ready_seconds // 5), port=self.port, log=self.log),
            timeout=ready_seconds + 120)

    def greet(self) -> Step:
        return self.sh("greeting and capabilities", """
python3 - <<'PY'
import socket
s = socket.create_connection(("127.0.0.1", {port}), 30); s.settimeout(30)
f = s.makefile("rwb")
print(f.readline().decode().strip())
f.write(b"CAPABILITIES\\r\\n"); f.flush()
while True:
    line = f.readline().decode().rstrip("\\r\\n")
    print(line)
    if line == "." or line.startswith(("4", "5")):
        break
f.write(b"QUIT\\r\\n"); f.flush(); print(f.readline().decode().strip())
PY
""".format(port=self.port), timeout=180)

    def status(self, kind: str) -> Step:
        if kind == "systemd":
            return self.sh("unit status", """
systemctl --user --no-pager -l status {unit} 2>&1 | head -12
""".format(unit=UNIT_NAME), expect=None)
        return self.sh("wrapper status", "{}/run.sh status".format(LIVE), expect=None)


def render(path: Path, hosts: list[Live], started: str, elapsed: float,
           unit_sample: str) -> Path:
    lines = [
        "# Live deployment: fn as a service on {}".format(
            " and ".join(h.host for h in hosts)),
        "",
        "Not a gate: these two installations are left running. Each holds one",
        "commit under `~/fn-live`, a store with its own groups, a peer record",
        "naming the other box, and a supervisor that keeps the process up.",
        "Produced by `tools/live_service.py install`.",
        "",
        "## Each node",
        "",
        "| node | host | commit | store | listener | groups | supervisor | certificates |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for live in hosts:
        lines.append("| {} | `{}` | `{}` | `{}` | {} | {} | {} | {} |".format(
            live.node, live.host, live.rev, live.store,
            live.facts.get("listener", "-"), live.facts.get("groups", "-"),
            live.facts.get("supervisor", "-"),
            live.facts.get("certificates on disk", "-")))
    for live in hosts:
        lines += ["", "## {} on {}: every command".format(live.node, live.host), "",
                  "| # | step | rc | first line | s |", "| --- | --- | --- | --- | --- |"]
        for index, step in enumerate(live.steps, 1):
            rc = "-" if step.rc is None else "{}{}".format(
                step.rc, "" if not step.failed else " FAIL")
            lines.append("| {} | {} | {} | `{}` | {:.1f} |".format(
                index, step.name, rc, step.first_line.replace("|", "\\|"), step.seconds))
        lines += ["", "```"]
        for index, step in enumerate(live.steps, 1):
            head = "\n".join(step.output.splitlines()[:10])
            lines.append("--- {} {} (rc={})".format(index, step.name, step.rc))
            if head:
                lines.append(head)
        lines += ["```"]
    lines += ["", "## The unit that was installed", "",
              "`packaging/fn.service` relocated under `$HOME/fn-live`, with the",
              "`User=`, `Group=` and the `Protect*`/`Private*` directives a user",
              "manager cannot apply removed. The difference from the packaged",
              "file is here in full rather than asserted:", "", "```ini",
              unit_sample.strip(), "```", "",
              "## What is true of this deployment and what is not", ""]
    for live in hosts:
        for note in live.notes:
            lines.append("- **{}**: {}".format(live.host, note))
    lines += [
        "- A running listener is not a peered network. Both nodes bind",
        "  `127.0.0.1` because `fn run` refuses any other host, so the peer",
        "  records point at addresses neither node can reach; an ssh tunnel is",
        "  how a client (or the other box) reaches one today.",
        "- Nothing here certifies a book. The certificates came from the box's",
        "  cache, which a gate put there; the certificate count per node is in",
        "  the table above and a zero there is a finding, not a detail.",
        "- `fn run` holds the store's exclusive writer lock for its lifetime, so",
        "  one instance per store; a second start fails rather than corrupting.",
        "",
        "| fact | value |", "| --- | --- |",
        "| started | {} |".format(started),
        "| wall time | {:.0f} s |".format(elapsed),
        "| tool | `tools/live_service.py` |",
        "",
    ]
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines))
    return path


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("action", choices=("install", "status", "stop", "start"))
    parser.add_argument("commit", nargs="?", default="HEAD")
    parser.add_argument("--host", action="append", default=[],
                        help="a box to install on; repeat for the pair")
    parser.add_argument("--node", action="append", default=[],
                        help="the node name per --host, in the same order")
    parser.add_argument("--port", action="append", type=int, default=[])
    parser.add_argument("--group", action="append", default=[])
    parser.add_argument("--repo", default=str(ROOT))
    parser.add_argument("--evidence", default=None)
    parser.add_argument("--supervisor", default="auto",
                        choices=("auto", "systemd", "setsid"))
    parser.add_argument("--skip-ship", action="store_true",
                        help="the tree is already there; reconfigure and restart")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve()
    commit, rev = resolve(repo, args.commit)
    hosts = args.host or ["persvati", "hbox"]
    nodes = args.node or ["fn{}".format(chr(ord("A") + i)) for i in range(len(hosts))]
    ports = args.port or [11190] * len(hosts)
    groups = tuple(args.group) or DEFAULT_GROUPS
    if not (len(hosts) == len(nodes) == len(ports)):
        parser.error("--host, --node and --port must come in matching numbers")

    started = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    clock = time.monotonic()
    installs = [Live(host, repo, commit, rev, node, port, groups,
                     FARM_HOSTS.get(host, {}).get("acl2", "acl2"),
                     FARM_HOSTS.get(host, {}).get("cache", "~/fn-certcache"),
                     args.supervisor)
                for host, node, port in zip(hosts, nodes, ports)]
    unit_sample = ""
    for index, live in enumerate(installs):
        print("== {} on {}".format(live.node, live.host), flush=True)
        kind = live.choose_supervisor()
        if args.action in ("status", "stop", "start"):
            if args.action == "stop":
                live.sh("stop", ("systemctl --user stop {}".format(UNIT_NAME)
                                 if kind == "systemd" else
                                 "{}/run.sh stop".format(LIVE)), expect=None)
            elif args.action == "start":
                live.start(kind)
            live.status(kind)
            continue
        if not args.skip_ship:
            if live.ship().failed:
                print("  ship failed; skipping {}".format(live.host))
                continue
        live.certificates()
        live.configure()
        others = [(nodes[j], hosts[j], ports[j]) for j in range(len(hosts))
                  if j != index]
        for peer, peer_host, peer_port in others:
            live.peer_record(peer, peer_host, peer_port)
        if kind == "systemd" and not unit_sample:
            unit_sample = live.unit_text("$HOME")
        live.install_unit(kind)
        live.start(kind)
        live.greet()
        live.status(kind)

    elapsed = time.monotonic() - clock
    if args.action == "install":
        date = dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%d")
        target = Path(args.evidence) if args.evidence else (
            repo / "planning/evidence/live-{}-{}.md".format(rev, date))
        render(target, installs, started, elapsed, unit_sample)
        print("evidence: {}".format(target))
    bad = [(live.host, step) for live in installs for step in live.steps if step.failed]
    print("hosts={} steps={} failed={}".format(
        len(installs), sum(len(live.steps) for live in installs), len(bad)))
    for host, step in bad:
        print("  FAILED {} rc={} {}: {}".format(host, step.rc, step.name,
                                                step.first_line))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
