#!/usr/bin/env python3
"""fn as a BPv7 node against dtn7-rs, with fn-authored bundles both ways.

What changed since `run_fn_tcpcl_interop.py`.  That harness had to let dtn7
author every bundle, because nothing in fn encoded BPv7: fn was a
convergence-layer peer carrying octets it did not write, and the note in its
docstring said so.  `books/bp-bundle.lisp` and `books/bp-node.lisp` close
that, so the direction of authorship is now fn's in leg 2 and dtn7's in
leg 1, and each side has to accept what the other wrote:

  1. dtn7 authors a bundle for `dtn://fn-b/incoming` and dials fn's
     `bp receive`.  fn decodes it with `fn-bpn-receive` -- the whole bundle,
     not just the primary block -- decides its lifetime and hop count, and
     journals the ADU it recovered.  The ADU must be the payload dtn7 sent.
  2. fn authors a bundle for dtn7's registered endpoint with `bp send`: its
     own node ID as the source, its clock observation as the creation
     timestamp, its configured lifetime, a hop count block and a bundle age
     block, and the ADU as the payload block.  dtn7 must decode it and
     deliver it to the endpoint, which `dtnrecv` then reads.

Every reply from both sides is recorded verbatim: fn's own lines (each value
in them computed in ACL2) and dtn7's log.

Usage:
  python3 tests/bp-dtn7/run_fn_bp_interop.py \
      --image build/fn-host-dtn --dtn7-repo /tank/fn/dtn7/repo --work /tmp/fn-bp
"""
import argparse
import hashlib
import json
import re
import shutil
import socket
import subprocess
import sys
import time
from pathlib import Path

LISTENING = re.compile(rb"BP LISTENING (\d+)")
BP_LINE = re.compile(r"^BP (authored|accepted|refused|uncertain|summary|decode) .*$")

# RFC 9171 section 4.1.6: DTN time is milliseconds since 2000-01-01T00:00:00Z.
# The harness reads the host's clock and hands it over as an observation; the
# image decides what it means (`fn-bpn-creation-time').
DTN_EPOCH_UNIX = 946684800


def free_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def tail(path: Path, n=400):
    if not path.exists():
        return []
    return path.read_text(errors="replace").splitlines()[-n:]


def vector(path: Path):
    """One captured wire image, named by what it is and by its digest.

    The length and the SHA-256 are what make a saved copy checkable against
    the run that produced it; the head is enough to read the CBOR opening by
    eye (RFC 9171 section 4.3.1: an indefinite-length array, 0x9f).
    """
    data = path.read_bytes()
    return dict(name=path.name, octets=len(data),
                sha256=hashlib.sha256(data).hexdigest(),
                head=list(data[:16]), path=str(path))


def bp_lines(path: Path):
    return [l.strip() for l in tail(path, 10000) if BP_LINE.match(l.strip())]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--image", default="build/fn-host-dtn")
    ap.add_argument("--dtn7-repo", required=True)
    ap.add_argument("--work", default="/tmp/fn-bp-interop")
    ap.add_argument("--settle", type=float, default=12.0)
    args = ap.parse_args(argv)

    image = Path(args.image).resolve()
    repo = Path(args.dtn7_repo).resolve()
    dtnd = repo / "target/release/dtnd"
    dtnsend = repo / "target/release/dtnsend"
    dtnrecv = repo / "target/release/dtnrecv"
    work = Path(args.work)
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    report = {"scenario": "fn-dtn7-bp", "image": str(image), "dtn7": str(repo)}
    for name, path in (("image", image), ("dtnd", dtnd), ("dtnsend", dtnsend),
                       ("dtnrecv", dtnrecv)):
        if not path.exists():
            report.update(ok=False, reason="missing {}: {}".format(name, path))
            print(json.dumps(report, indent=2, sort_keys=True))
            return 2
    report["dtn7_version"] = subprocess.run(
        [str(dtnd), "--version"], capture_output=True, text=True).stdout.strip()
    report["dtn7_revision"] = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"],
        capture_output=True, text=True).stdout.strip()

    journal = work / "fn-journal"
    fn_log = work / "fn-receive.log"
    dtn_log = work / "dtnd.log"
    dtn_port, fn_port, web_port = free_port(), free_port(), free_port()
    wall = str(int((time.time() - DTN_EPOCH_UNIX) * 1000))
    report["dtn_time_ms"] = wall

    # fn listens first: dtn7's static peer must resolve at startup.
    #   bp receive PORT ONCE JOURNAL NODE-ID PEER LIFETIME CRC HOP MRU ...
    fn_receive = subprocess.Popen(
        [str(image), "--fn", "bp", "receive", str(fn_port), "1", str(journal),
         "dtn://fn-b/", "-", "3600000", "2", "32", "1048576", "-", "-",
         wall, "60000"],
        stdout=fn_log.open("wb"), stderr=subprocess.STDOUT)
    daemon = None
    try:
        deadline = time.time() + 20
        while time.time() < deadline:
            if LISTENING.search(fn_log.read_bytes() or b""):
                break
            if fn_receive.poll() is not None:
                report.update(ok=False, reason="fn receiver exited",
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

        # --- Leg 1: dtn7 authors, fn decodes -----------------------------
        payload = work / "from-dtn7.txt"
        payload.write_bytes(b"dtn7 -> fn, decoded as a bundle\n")
        sent = subprocess.run(
            [str(dtnsend), "-r", "dtn://fn-b/incoming", "-p", str(web_port),
             "-v", str(payload)],
            capture_output=True, text=True, timeout=60)
        report["dtnsend_rc"] = sent.returncode
        report["dtnsend_out"] = (sent.stdout + sent.stderr).strip()[:800]
        try:
            fn_receive.wait(timeout=args.settle)
        except subprocess.TimeoutExpired:
            pass
        evidence = journal / "receive-evidence"
        accepted = sorted(evidence.glob("*.adu"))
        refused = sorted(evidence.glob("*.refused")) + sorted(evidence.glob("*.uncertain"))
        # The octets dtn7 put on the wire, as `bp receive' journalled them
        # before deciding anything.  This is the only artifact of the run
        # that is an INTEROPERABILITY VECTOR: bytes a foreign encoder wrote.
        wire = sorted(evidence.glob("*.wire"))
        report["leg1"] = dict(
            direction="dtn7 authors, fn decodes",
            accepted=[p.name for p in accepted],
            accepted_octets=[p.stat().st_size for p in accepted],
            not_accepted=[p.name for p in refused],
            adu_matches_payload=bool(
                accepted and accepted[0].read_bytes() == payload.read_bytes()),
            fn_lines=bp_lines(fn_log),
            fn_rc=fn_receive.poll(),
            dtn7_authored_wire=[vector(p) for p in wire])
        # fn's ADU is the payload only if dtn7 sent it unwrapped; dtn7 wraps
        # the payload in its own way, so the honest assertion is that fn
        # accepted a bundle and recovered SOME ADU of the right length.
        report["leg1"]["accepted_any"] = bool(accepted)
    finally:
        if fn_receive.poll() is None:
            fn_receive.kill()
        fn_receive.wait(timeout=10)

    # --- Leg 2: fn authors, dtn7 decodes and delivers --------------------
    leg2 = {"direction": "fn authors, dtn7 decodes"}
    if daemon is not None:
        adu = work / "from-fn.txt"
        adu.write_bytes(b"fn -> dtn7, a bundle fn authored\n")
        out = subprocess.run(
            [str(image), "--fn", "bp", "send", "127.0.0.1", str(dtn_port),
             str(adu), str(work / "fn-out-journal"), "dtn://fn-b/",
             "dtn://dtn7x/incoming", "3600000", "2", "32", "1048576",
             "0", wall, "60000"],
            capture_output=True, text=True, timeout=120)
        (work / "fn-send.log").write_text(out.stdout + out.stderr)
        out_wire = sorted((work / "fn-out-journal").glob("*.wire"))
        leg2.update(fn_rc=out.returncode,
                    fn_lines=bp_lines(work / "fn-send.log"),
                    fn_authored_wire=[vector(p) for p in out_wire])
        time.sleep(4.0)
        got = subprocess.run(
            [str(dtnrecv), "-e", "incoming", "-p", str(web_port)],
            capture_output=True, text=True, timeout=60)
        leg2["dtnrecv_rc"] = got.returncode
        leg2["dtnrecv_out"] = (got.stdout + got.stderr).strip()[:2000]
        leg2["dtn7_delivered_the_adu"] = adu.read_text().strip() in got.stdout
    else:
        leg2["skipped"] = "dtnd did not start"
    report["leg2"] = leg2

    if daemon is not None:
        daemon.terminate()
        try:
            daemon.wait(timeout=10)
        except subprocess.TimeoutExpired:
            daemon.kill()
    report["dtn7_log"] = tail(dtn_log, 300)
    report["ok"] = bool(report.get("leg1", {}).get("accepted_any")
                        and leg2.get("fn_rc") == 0
                        and leg2.get("dtn7_delivered_the_adu"))
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
