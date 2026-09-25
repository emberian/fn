#!/usr/bin/env python3
"""One screen for the mission lab: the four nodes, their obligations, pins
and the link.  `python3 tools/mission_lab.py status [--json]`.

What each column comes from, so a reader knows what is live and what is
inferred:

    owner/web/bp/relay   the PID the lab started, checked with kill -0
    groups               NNTP GROUP over STARTTLS+AUTHINFO as the human login
    verdict              HDR :fn-verified of the newest article in fn.mission
    obligations          `bp-obligation status` per undertaken work (the DTN
                         image, offline: it opens the BP store read-only
                         beside the serving node)
    pins                 `store ROOT retention` (offline; refused while an
                         owner holds the store, and then reported as such)
    relay bundles        dtnquery -p WEB bundles
    link                 the controller's state file and its last log line

;; SPIKE: defers a status verb on the control socket (status, headroom, pins
;; and held obligations are offline commands today; see operator.md).
"""
from __future__ import annotations

import argparse
import json
import subprocess
import time
from pathlib import Path

from mission_lab import HUMAN, NODES, RELAYS, Lab, LabError


def nntp_view(lab: Lab, name):
    out = dict(groups={}, verdict=None)
    try:
        session = lab.session(name)
    except Exception as error:  # noqa: BLE001 - one screen, every failure named
        out["error"] = f"{type(error).__name__}: {error}"
        return out
    try:
        for group in ("fn.mission", "control.cancel"):
            status, _ = session.cmd(f"GROUP {group}")
            words = status.split()
            out["groups"][group] = (dict(count=int(words[1]), low=int(words[2]), high=int(words[3]))
                                    if status.startswith("211") else status)
        high = out["groups"].get("fn.mission", {}).get("high") if isinstance(
            out["groups"].get("fn.mission"), dict) else None
        if high:
            status, body = session.cmd(f"HDR :fn-verified {high}", multiline=True)
            out["verdict"] = body[0] if body else status
            status, body = session.cmd(f"HDR Message-ID {high}", multiline=True)
            out["newest"] = body[0].split(None, 1)[1] if body else None
    finally:
        session.close()
    return out


def bp_view(lab: Lab, name):
    node = lab.state["nodes"][name]
    bp = node.get("bp")
    if not bp:
        return None
    out = dict(port=bp["port"], eid=bp["eid"], works={}, pins=None)
    for work in bp.get("works", []):
        record = lab.fn("dtn-developer", "bp-obligation", "status", bp["store"], bp["workflow"],
                        work["work"], check=False, timeout=60)
        out["works"][work["work"]] = (record["stdout"].strip() or record["stderr"].strip()
                                      or f"exit {record['rc']}")
    record = lab.fn("dtn-developer", "store", bp["store"], "retention", check=False, timeout=60)
    out["pins"] = (record["stdout"].strip() if record["rc"] == 0
                   else f"refused: {(record['stdout'] + record['stderr']).strip()[:80]}")
    log = Path(bp["dir"]) / "serve.log"
    if log.exists():
        lines = log.read_text("utf-8", "replace").splitlines()
        out["serve_tail"] = [l for l in lines if l.startswith("BP node")][-3:]
    return out


def relay_view(lab: Lab, name):
    spec = RELAYS[name]
    out = dict(alive=lab.alive(f"relay-{name}"), cla=spec["cla"])
    query = lab.dtn7 / "target" / "release" / "dtnquery"
    for what in ("bundles", "peers"):
        try:
            result = subprocess.run([str(query), "-p", str(spec["web"]), what], capture_output=True,
                                    timeout=10, text=True)
            out[what] = [l for l in result.stdout.splitlines() if l.strip()]
        except (OSError, subprocess.TimeoutExpired) as error:
            out[what] = f"{type(error).__name__}"
    return out


def link_view(lab: Lab):
    log = Path(lab.state["link"]["log"])
    lines = log.read_text("utf-8", "replace").splitlines() if log.exists() else []
    return dict(state=lab.link_state(), controller=lab.alive("link"), last=lines[-1] if lines else None)


def gather(lab: Lab):
    nodes = {}
    for name in NODES:
        nodes[name] = dict(
            owner=lab.alive(f"owner-{name}"), web=lab.alive(f"web-{name}"),
            nntp=lab.state["nodes"][name]["nntp"], web_port=lab.state["nodes"][name]["web"],
            view=nntp_view(lab, name), bp=bp_view(lab, name),
            bp_serving=lab.alive(f"bp-{name}") if "bp" in NODES[name] else None)
    return dict(at=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), root=str(lab.root),
                images=str(lab.images), link=link_view(lab),
                relays={r: relay_view(lab, r) for r in RELAYS}, nodes=nodes)


def render(view):
    on = lambda flag: "up" if flag else ("--" if flag is None else "DOWN")  # noqa: E731
    rows = [f"mission lab  {view['at']}  root {view['root']}",
            f"images {view['images']}",
            f"link {view['link']['state'].upper():5} controller {on(view['link']['controller'])}"
            f"  {view['link']['last'] or ''}", ""]
    rows.append(f"{'node':5}{'owner':7}{'web':6}{'bp':6}{'fn.mission':16}{'control.cancel':16}verdict of newest")
    for name, node in view["nodes"].items():
        groups = node["view"].get("groups", {})

        def cell(group):
            g = groups.get(group)
            return f"{g['count']}/{g['high']}" if isinstance(g, dict) else str(g or node["view"].get("error", "?"))[:14]
        rows.append(f"{name:5}{on(node['owner']):7}{on(node['web']):6}{on(node['bp_serving']):6}"
                    f"{cell('fn.mission'):16}{cell('control.cancel'):16}{node['view'].get('verdict') or ''}")
    rows.append("")
    for name, node in view["nodes"].items():
        bp = node.get("bp")
        if not bp:
            continue
        rows.append(f"{name} bp {bp['eid']} port {bp['port']}  pins: {bp['pins']}")
        for work, status in bp["works"].items():
            rows.append(f"    {work}: {status}")
        for line in bp.get("serve_tail", []):
            rows.append(f"    | {line}")
    for name, relay in view["relays"].items():
        bundles = relay["bundles"] if isinstance(relay["bundles"], list) else [relay["bundles"]]
        rows.append(f"relay {name} {on(relay['alive'])} cla {relay['cla']}  bundles {len(bundles)}: "
                    + "; ".join(bundles)[:160])
    return "\n".join(rows)


def main(lab: Lab, argv) -> int:
    parser = argparse.ArgumentParser(prog="mission_lab.py status", description=__doc__)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    if "nodes" not in lab.state:
        print("not provisioned; run `mission_lab.py up`")
        return 1
    try:
        view = gather(lab)
    except LabError as error:
        print(f"status failed: {error}")
        return 1
    print(json.dumps(view, indent=1) if args.json else render(view))
    return 0
