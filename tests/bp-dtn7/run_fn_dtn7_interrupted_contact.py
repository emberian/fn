#!/usr/bin/env python3
"""An interrupted contact between the fn DTN image and pinned dtn7-rs.

Topology, all on loopback, every process started and stopped by PID:

    fn-a (`bp send`) --[byte relay]--> dtn7c (carrier, sled store) --> dtn7d

Steps, each reported with the three outcomes kept apart (accepted by the
peer's convergence layer, refused, uncertain) and never inferred from a
later step:

  1. interrupted: the relay forwards one byte of fn's contact and severs
     both sides.  fn must report the send uncertain, not sent.
  2. retry: the same ADU from the same fn journal, straight to the carrier.
     The report records both authored creation/sequence lines, so it says
     whether the retry carried the original bundle identity.
  3. carrier death: the carrier holds the bundle with no route to dtn7d and
     is SIGKILLed by PID; it restarts on the same sled store with dtn7d and
     fn-a as static peers.  dtn7d's endpoint is drained; the count of
     deliveries of the ADU is the exactly-once observation at the far BPA.
  4. return: dtn7d sends a receipt ADU for `dtn://fn-a/incoming` back through
     the carrier to fn-a's `bp receive`.  fn's verdict line is recorded as
     is: this is where an fn application receipt would have to arrive.

dtn7-rs is a lab dependency (tests/bp-dtn7/pin.json), not part of the image.
The byte relay is `tests.test_bp_contact_relay_native.ByteRelay`; it never
answers a protocol message.  No power-loss claim follows.
"""
import argparse
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tests.test_bp_contact_relay_native import ByteRelay  # noqa: E402
sys.path.insert(0, str(Path(__file__).resolve().parent))
from run_fn_bp_interop import (  # noqa: E402
    DTN_EPOCH_UNIX, LISTENING, bp_lines, free_port, tail, vector)

AUTHORED = re.compile(r"BP authored creation=(\d+) sequence=(\d+)")


def wait_for(predicate, timeout, step=0.2):
    deadline = time.time() + timeout
    while time.time() < deadline:
        value = predicate()
        if value:
            return value
        time.sleep(step)
    return predicate()


class Dtnd:
    def __init__(self, repo, work, name, endpoint=None, peers=(), db="mem"):
        self.bin = repo / "target/release/dtnd"
        self.work = work / name
        self.work.mkdir(parents=True, exist_ok=True)
        self.name, self.endpoint, self.db = name, endpoint, db
        self.cla_port, self.web_port = free_port(), free_port()
        self.proc = None
        self.starts = []
        self.start(peers)

    def start(self, peers):
        cmd = [str(self.bin), "-n", self.name, "-W", str(self.work),
               "-D", self.db, "-C", "tcp:port={}".format(self.cla_port),
               "-w", str(self.web_port), "-i", "0", "--disable_nd", "-d"]
        if self.endpoint:
            cmd += ["-e", self.endpoint]
        for peer in peers:
            cmd += ["-s", peer]
        log = self.work / "dtnd-{}.log".format(len(self.starts))
        self.proc = subprocess.Popen(cmd, stdout=log.open("wb"),
                                     stderr=subprocess.STDOUT, cwd=str(self.work))
        self.starts.append(dict(pid=self.proc.pid, cmd=cmd, log=str(log)))
        time.sleep(2.5)

    def peer_uri(self):
        return "tcp://127.0.0.1:{}/{}".format(self.cla_port, self.name)

    def kill(self):
        self.proc.send_signal(signal.SIGKILL)
        self.proc.wait(timeout=10)
        self.starts[-1]["stopped"] = "SIGKILL rc={}".format(self.proc.returncode)

    def stop(self):
        if self.proc and self.proc.poll() is None:
            self.proc.terminate()
            try:
                self.proc.wait(timeout=10)
                self.starts[-1]["stopped"] = "SIGTERM rc={}".format(self.proc.returncode)
            except subprocess.TimeoutExpired:
                self.proc.kill()
                self.proc.wait(timeout=10)
                self.starts[-1]["stopped"] = "SIGKILL fallback"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--image", required=True)
    ap.add_argument("--dtn7-repo", required=True, type=Path)
    ap.add_argument("--work", required=True, type=Path)
    ap.add_argument("--settle", type=float, default=30.0)
    args = ap.parse_args(argv)
    image = Path(args.image).resolve()
    repo = args.dtn7_repo.resolve()
    work = args.work
    work.mkdir(parents=True, exist_ok=False)
    wall = str(int((time.time() - DTN_EPOCH_UNIX) * 1000))
    dtnsend = repo / "target/release/dtnsend"
    dtnrecv = repo / "target/release/dtnrecv"
    report = {"image": str(image), "dtn7": str(repo), "dtn_time_ms": wall,
              "dtn7_revision": subprocess.run(
                  ["git", "-C", str(repo), "rev-parse", "HEAD"],
                  capture_output=True, text=True).stdout.strip(),
              "dtn7_version": subprocess.run(
                  [str(repo / "target/release/dtnd"), "--version"],
                  capture_output=True, text=True).stdout.strip()}
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    adu = work / "article.adu"
    adu.write_bytes(b"fn-a -> dtn7d across an interrupted contact\n")
    journal = work / "fn-a-send"
    relay = ByteRelay()
    fn_recv = None
    carrier = dest = None

    def fn_send(port, tag):
        out = subprocess.run(
            [str(image), "--fn", "bp", "send", "127.0.0.1", str(port), str(adu),
             str(journal), "dtn://fn-a/", "dtn://dtn7d/incoming", "3600000",
             "2", "32", "1048576", "0", wall, "60000"],
            capture_output=True, text=True, timeout=120, env=env, cwd=str(ROOT))
        (work / "fn-send-{}.log".format(tag)).write_text(out.stdout + out.stderr)
        m = AUTHORED.search(out.stdout)
        return dict(rc=out.returncode, lines=bp_lines(work / "fn-send-{}.log".format(tag)),
                    tcpcl=[l for l in out.stdout.splitlines() if "outbound" in l
                           or "summary" in l],
                    authored=(m.groups() if m else None))

    def drain(node):
        got = []
        for _ in range(8):
            r = subprocess.run([str(dtnrecv), "-e", "incoming", "-p", str(node.web_port)],
                               capture_output=True, text=True, timeout=30)
            if r.returncode != 0 or not r.stdout.strip():
                break
            got.append(r.stdout.strip()[:400])
        return got

    try:
        dest = Dtnd(repo, work, "dtn7d", endpoint="incoming")
        carrier = Dtnd(repo, work, "dtn7c", db="sled")
        # 1. interrupted contact
        relay.route(carrier.cla_port, cut_next=True)
        s1 = fn_send(relay.port, "1-interrupted")
        s1["outcome"] = {0: "accepted", 3: "uncertain"}.get(s1["rc"], "refused-or-other")
        report["step1_interrupted"] = s1
        # 2. retry straight to the carrier
        s2 = fn_send(carrier.cla_port, "2-retry")
        s2["outcome"] = {0: "accepted", 3: "uncertain"}.get(s2["rc"], "refused-or-other")
        s2["same_identity_as_step1"] = (s1["authored"] is not None
                                        and s1["authored"] == s2["authored"])
        s2["authored_wire"] = [vector(p) for p in sorted(journal.glob("**/*.wire"))]
        report["step2_retry"] = s2
        time.sleep(2.0)
        report["dest_before_carrier_death"] = drain(dest)
        # fn-a listens for the return leg before the carrier restarts, since
        # a dtn7 static peer is resolved at startup.
        fn_port = free_port()
        fn_log = work / "fn-a-receive.log"
        fn_recv = subprocess.Popen(
            [str(image), "--fn", "bp", "receive", str(fn_port), "1",
             str(work / "fn-a-receive"), "dtn://fn-a/", "-", "3600000", "2",
             "32", "1048576", "-", "-", wall, "60000"],
            stdout=fn_log.open("wb"), stderr=subprocess.STDOUT, env=env, cwd=str(ROOT))
        wait_for(lambda: LISTENING.search(fn_log.read_bytes() or b""), 30)
        report["fn_a_receive_pid"] = fn_recv.pid
        # 3. carrier death while it holds the bundle, then restart
        carrier.kill()
        carrier.start([dest.peer_uri(), "tcp://127.0.0.1:{}/fn-a".format(fn_port)])
        delivered = []
        deadline = time.time() + args.settle
        while time.time() < deadline:
            delivered += drain(dest)
            time.sleep(2.0)
        text = adu.read_text().strip()
        report["step3_carrier_restart"] = dict(
            carrier_pids=[s["pid"] for s in carrier.starts],
            dest_deliveries=delivered,
            copies_of_adu=sum(d.count(text) for d in delivered))
        # 4. application receipt back toward fn-a
        receipt = work / "receipt.adu"
        receipt.write_bytes(b"receipt: dtn7d holds <fn-a article>\n")
        sent = subprocess.run(
            [str(dtnsend), "-r", "dtn://fn-a/incoming", "-p", str(dest.web_port),
             str(receipt)], capture_output=True, text=True, timeout=60)
        # dtn7d has no route to fn-a but the carrier does: make dtn7d a
        # carrier client by adding the carrier as its static peer is not
        # possible at run time, so the receipt is also injected at the carrier.
        sent_c = subprocess.run(
            [str(dtnsend), "-r", "dtn://fn-a/incoming", "-p", str(carrier.web_port),
             str(receipt)], capture_output=True, text=True, timeout=60)
        try:
            fn_recv.wait(timeout=args.settle)
        except subprocess.TimeoutExpired:
            pass
        ev = work / "fn-a-receive" / "receive-evidence"
        report["step4_return"] = dict(
            dtnsend_dest_rc=sent.returncode, dtnsend_carrier_rc=sent_c.returncode,
            fn_rc=fn_recv.poll(), fn_lines=bp_lines(fn_log),
            accepted=sorted(p.name for p in ev.glob("*.adu")),
            refused=sorted(p.name for p in ev.glob("*.refused")),
            uncertain=sorted(p.name for p in ev.glob("*.uncertain")),
            refusal_reasons=[p.read_text().strip() for p in sorted(ev.glob("*.refused"))])
    finally:
        relay.close()
        if fn_recv is not None and fn_recv.poll() is None:
            fn_recv.kill()
            fn_recv.wait(timeout=10)
        for node in (carrier, dest):
            if node is not None:
                node.stop()
        report["dtnd_processes"] = {n.name: n.starts for n in (carrier, dest) if n}
    report["carrier_log_tail"] = tail(Path(carrier.starts[-1]["log"]), 60) if carrier else []
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
