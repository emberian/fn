#!/usr/bin/env python3
"""fn's TCPCLv4 against dtn7-rs's, one bundle each way, on loopback.

dtn7-rs's `tcp` convergence layer is RFC 9174 (`core/dtn7/src/cla/tcp/proto.rs`
carries the Table 2 message types and the CAN_TLS contact flag), so the two
implementations can hold a session.  What they cannot yet do is agree on a
*bundle*: nothing in fn encodes BPv7 (`specs/bp-design.md` section 1.4,
`books/bp-bundle.lisp`, is a design), so fn's convergence layer carries opaque
octets and a bundle fn authored would be rejected by dtn7's parser.

So the direction of authorship is dtn7's, both ways:

  1. dtn7 authors a bundle and dials fn's listener.  fn completes the contact
     exchange and SESS_INIT, acknowledges the transfer and stages the octets.
  2. fn sends *those same octets* back to dtn7's CLA.  The bundle is valid
     BPv7 because dtn7 wrote it; fn is a convergence-layer peer carrying a
     bundle it did not author, which is exactly what this can honestly claim.

Every reply is recorded verbatim: fn's own event digests (computed in ACL2 by
`fn-tcl-host-event-digests`) and dtn7's log lines.

Usage:
  python3 tests/bp-dtn7/run_fn_tcpcl_interop.py \
      --image build/fn-host --dtn7-repo /tank/fn/dtn7/repo --work /tmp/fn-dtn7
"""
import argparse
import json
import re
import shutil
import socket
import subprocess
import sys
import time
from pathlib import Path

LISTENING = re.compile(rb"TCPCL LISTENING (\d+)")
EVENT = re.compile(r"TCPCL (\S+) (event|aux) (.*)$")


def free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def tail(path: Path, n=400):
    if not path.exists():
        return []
    return path.read_text(errors="replace").splitlines()[-n:]


def fn_events(path: Path):
    out = []
    for line in tail(path, 10000):
        m = EVENT.match(line.strip())
        if m:
            out.append("{} {} {}".format(m.group(1), m.group(2), m.group(3)))
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--image", default="build/fn-host")
    ap.add_argument("--dtn7-repo", required=True)
    ap.add_argument("--work", default="/tmp/fn-dtn7-interop")
    ap.add_argument("--settle", type=float, default=12.0)
    args = ap.parse_args(argv)

    image = Path(args.image).resolve()
    repo = Path(args.dtn7_repo).resolve()
    dtnd, dtnsend = repo / "target/release/dtnd", repo / "target/release/dtnsend"
    work = Path(args.work)
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    report = {"scenario": "fn-dtn7-tcpcl", "image": str(image), "dtn7": str(repo)}
    for name, path in (("image", image), ("dtnd", dtnd), ("dtnsend", dtnsend)):
        if not path.exists():
            report.update(ok=False, reason="missing {}: {}".format(name, path))
            print(json.dumps(report, indent=2, sort_keys=True))
            return 2
    report["dtn7_version"] = subprocess.run(
        [str(dtnd), "--version"], capture_output=True, text=True).stdout.strip()
    report["dtn7_revision"] = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"],
        capture_output=True, text=True).stdout.strip()

    spool = work / "fn-spool"
    fn_log = work / "fn-listen.log"
    dtn_log = work / "dtnd.log"
    dtn_port, fn_port, web_port = free_port(), free_port(), free_port()

    # fn listens first: dtn7's static peer must resolve at startup.
    fn_listen = subprocess.Popen(
        [str(image), "--fn", "tcpcl", "listen", str(fn_port), "1", str(spool),
         "dtn://fn-b/", "-", "10", "4096", "1048576", "-", "-"],
        stdout=fn_log.open("wb"), stderr=subprocess.STDOUT)
    daemon = None
    try:
        deadline = time.time() + 20
        while time.time() < deadline:
            if LISTENING.search(fn_log.read_bytes() or b""):
                break
            if fn_listen.poll() is not None:
                report.update(ok=False, reason="fn listener exited",
                              fn_log=tail(fn_log, 40))
                print(json.dumps(report, indent=2, sort_keys=True))
                return 1
            time.sleep(0.05)
        report["fn_port"] = fn_port

        daemon = subprocess.Popen(
            [str(dtnd), "-n", "dtn7x", "-C", "tcp:port={}".format(dtn_port),
             "-e", "incoming", "-w", str(web_port), "-i", "0",
             "-s", "tcp://127.0.0.1:{}/fn-b".format(fn_port), "-d"],
            stdout=dtn_log.open("wb"), stderr=subprocess.STDOUT, cwd=str(work))
        time.sleep(3.0)

        payload = work / "payload.txt"
        payload.write_bytes(b"fn <-> dtn7 tcpcl interop\n")
        sent = subprocess.run(
            [str(dtnsend), "-r", "dtn://fn-b/incoming", "-i", str(payload),
             "-p", str(web_port)],
            capture_output=True, text=True, timeout=60)
        report["dtnsend_rc"] = sent.returncode
        report["dtnsend_out"] = (sent.stdout + sent.stderr).strip()[:800]

        # Leg 1: dtn7 -> fn.  The listener exits after one session.
        try:
            fn_listen.wait(timeout=args.settle)
        except subprocess.TimeoutExpired:
            pass
        staged = sorted(spool.glob("*.bundle"))
        report["leg1"] = dict(
            staged=[p.name for p in staged],
            octets=[p.stat().st_size for p in staged],
            fn_events=fn_events(fn_log),
            fn_rc=fn_listen.poll())
    finally:
        if fn_listen.poll() is None:
            fn_listen.kill()
        fn_listen.wait(timeout=10)

    leg1_ok = bool(report.get("leg1", {}).get("staged"))
    # Leg 2: fn -> dtn7, returning the bundle dtn7 authored.
    if leg1_ok and daemon is not None:
        bundle = sorted(spool.glob("*.bundle"))[0]
        back = subprocess.run(
            [str(image), "--fn", "tcpcl", "send", "127.0.0.1", str(dtn_port),
             str(bundle), str(work / "fn-out-spool"), "dtn://fn-a/", "-",
             "10", "4096", "1048576", "0", "-"],
            capture_output=True, text=True, timeout=120)
        (work / "fn-send.log").write_text(back.stdout + back.stderr)
        time.sleep(3.0)
        report["leg2"] = dict(
            fn_rc=back.returncode,
            fn_events=fn_events(work / "fn-send.log"),
            bundle_octets=bundle.stat().st_size)
    else:
        report["leg2"] = dict(skipped="leg 1 staged nothing")

    if daemon is not None:
        daemon.terminate()
        try:
            daemon.wait(timeout=10)
        except subprocess.TimeoutExpired:
            daemon.kill()
    report["dtn7_log"] = tail(dtn_log, 200)
    report["ok"] = bool(leg1_ok and report["leg2"].get("fn_rc") == 0)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
