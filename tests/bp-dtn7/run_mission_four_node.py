#!/usr/bin/env python3
"""The mission's four fn BP nodes across two dtn7-rs relays, with outages.

Topology, all on loopback, every process started and stopped by PID:

    A (dtn://fn-a/) --TCPCL--> X (dtn://fn-x/, fn relay) --> dtn7 r1
        --> dtn7 r2 --> Y (dtn://fn-y/, fn relay) --> B (dtn://fn-b/)

and the reverse path for receipts and the reply.  The relays r1 and r2 are
dtn7-rs with static routes (`idx src dst via`); X and Y are `bp-node serve`
of the DTN developer image forwarding held transit by their route tables
(spec bp-node-machine 4.6).

Steps (each row keeps accepted, refused and uncertain apart and says
whether its assertions held; no step is inferred from a later one):

  0. setup.  Stores, boundaries (D23: each fn endpoint's neighbour boundary
     `carries' the far endpoint, which is enrolled under its own EID with
     the inbound scope), routes.  Two hybrid authors (Ed25519 + ML-DSA-65)
     are enrolled in A's and B's Stores through each node's developer
     owner; A's author signs and injects the report (`hybrid-author'); B's
     and A's consumers are registered and then left asleep.  A's work is
     enqueued and undertaken (`app-journal', `bp-obligation undertake').
  1. A's `bp-obligation request' toward dtn://fn-b/ via X.  X announces a
     small Transfer MRU, so A fragments; X reassembles; r1 is down, so X
     holds the transit bundle.
  2. X is SIGKILLed by PID; r1 starts; X restarts and forwards from durable
     state to r1; r2 starts later; r2 hands the bundle to Y, Y to B.
  3. B admits (D23 carried), takes kind-5 custody, delivers to its Store
     and queues the receipt toward dtn://fn-a/ through Y.
  4. The receipt crosses its own outage: X is down while Y, r2 and r1
     carry the receipt; A's node is SIGKILLed and restarted meanwhile; X
     restarts; A answers `receipt-accepted' and `bp-obligation status'
     shows `pinned=no', all before B's consumer wakes.
  5. B's consumer wakes: B's node stops (K6: node and owner each take the
     Store writer lock), `store inspect' + `hybrid-verify-source' check the
     delivered copy, B's owner serves `consumer poll' / `consumer ack', B's
     author signs a reply, and B requests it toward dtn://fn-a/ with its own
     obligation.
  6. The reply crosses back; A delivers it; A's receipt returns and releases
     B's pin; A's consumer wakes, polls and acks.
  7. The identity table and every log's SHA-256.

Python here is only an external driver: every verdict is a native
process's own line, exit code or verb output.  No power-loss claim follows.

The relays serve both directions at once, with no driver turns (PKT-261,
PKT-291 (1); planning/evidence/multi-peer-relay-2026-09-26.md).  X and Y run
`bp-node serve -': the node binds ACL2's listener set, one listener per
transport-bp boundary row of its configuration (fn-bpaj-listener-ports), and
routes each held bundle to the neighbour its route table names for the
bundle's own destination (fn-bpnp-progress-dispatch-names-the-routed-hop,
fn-bpnp-forward-plan).  Each process is started once per incarnation with
the same argv; the only stops are the mission's outages (X SIGKILLed while
holding, X down while the receipt crosses, A SIGKILLed) and the Store
writer-lock hand-offs of K6 (a node and its owner or an offline verb each
take the Store's writer lock: B's node stops for B's owner in step 5 and
serves again for A's receipt in step 6; A's node stops for its status and
owner reads).

Each relay boundary has its own listener (PRF-128, D23): the loopback policy
names the neighbour by the listener it arrives on
(fn-bpaj-session-principal), so two boundaries on one listener are
`ambiguous-peer' and refused.  `--case ambiguous-peer' provisions the relays
with both boundaries on one listener, serves X on that port explicitly (the
listener set would bind nothing) and runs steps 0 and 1 only: X must refuse
A's transfer with the policy's reason and take no custody.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1]))
sys.path.insert(0, str(HERE))
from run_fn_bp_interop import free_port  # noqa: E402
from run_fn_dtn7_interrupted_contact import Dtnd  # noqa: E402
from run_fn_dtn7_app_receipt import ROOT, Lab, lines_of, outcome_of  # noqa: E402

A, B, X, Y = "dtn://fn-a/", "dtn://fn-b/", "dtn://fn-x/", "dtn://fn-y/"
R1, R2 = "dtn://dtn7-r1/", "dtn://dtn7-r2/"
REPORT_ID = "<mission-report@fn-a.invalid>"
REPLY_ID = "<mission-reply@fn-b.invalid>"
WORK_A, WORK_B = "work-a-report", "work-b-reply"
SCOPE = ["fn.test", "32768", "16"]
# Key-history generations: each enrolment in a Store takes the next one.
GENERATION = {"author-a": "1", "author-b": "2"}
# RFC 8032 section 7.1, tests 1 and 2: the two authors' Ed25519 keys.
ED_KEYS = {
    "author-a": ("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
                 "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"),
    "author-b": ("3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
                 "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb"),
}


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class Relay(Dtnd):
    """dtn7-rs with static routes and a janitor, so a held bundle is offered
    again once its next hop listens (the mission lab's relay argv)."""

    def __init__(self, repo, work, name, cla, web, routes, peers):
        self.bin = repo / "target/release/dtnd"
        self.work = work / name
        self.work.mkdir(parents=True, exist_ok=True)
        self.name, self.endpoint, self.db = name, None, "sled"
        self.cla_port, self.web_port = cla, web
        self.proc, self.starts, self.peers = None, [], peers
        self.routes = self.work / "static.routes"
        self.routes.write_text(routes, encoding="ascii")

    def start(self, peers=None):
        cmd = [str(self.bin), "-n", self.name, "-W", str(self.work), "-D", self.db,
               "-C", "tcp:port={}".format(self.cla_port), "-w", str(self.web_port),
               "-i", "0", "-j", "5s", "-p", "1h", "--disable_nd", "-d",
               "-r", "static", "-R", "static.routes={}".format(self.routes)]
        for peer in self.peers:
            cmd += ["-s", peer]
        log = self.work / "dtnd-{}.log".format(len(self.starts))
        self.proc = subprocess.Popen(cmd, stdout=log.open("wb"),
                                     stderr=subprocess.STDOUT, cwd=str(self.work))
        self.starts.append(dict(pid=self.proc.pid, cmd=cmd, log=str(log),
                                at=time.strftime("%H:%M:%S")))
        time.sleep(2.5)


class Stop(Exception):
    """The case ends after its last step; the report is still written."""


class Mission:
    def __init__(self, args):
        self.args = args
        self.lab = Lab(args)
        self.owner_image = Path(args.owner_image).resolve()
        self.steps, self.findings = [], []
        self.t0 = time.monotonic()
        lab = self.lab
        self.nodes = {}
        for name, eid in (("a", A), ("b", B), ("x", X), ("y", Y)):
            d = dict(name=name, eid=eid, port=free_port(),
                     store=lab.path(name + "-store"), fnbs=lab.path(name + "-fnbs"),
                     wf=lab.path(name + "-fnwf"), rj=lab.path(name + "-fnrj"),
                     config=lab.path(name + ".toml"),
                     owner_config=lab.path(name + "-owner.toml"),
                     control=lab.path(name + "-control.sock"),
                     serve=None, incarnations=[])
            self.nodes[name] = d
        # A relay's second listener: the far (dtn7-facing) boundary's.
        for name in ("x", "y"):
            self.nodes[name]["port_far"] = (
                self.nodes[name]["port"] if args.case == "ambiguous-peer" else free_port())
        self.r_ports = {r: (free_port(), free_port()) for r in ("r1", "r2")}
        self.relays = {}

    # --- processes ---------------------------------------------------------
    def ofn(self, tag, *args, timeout=180, binary=False):
        """One owner-image (fn-host-developer) command, logged."""
        log = self.lab.path("{}.log".format(tag))
        out = subprocess.run([str(self.owner_image), "--fn", *map(str, args)],
                             capture_output=True, timeout=timeout,
                             env=self.lab.env, cwd=str(ROOT))
        log.write_bytes(("$ fn[developer] {}\n".format(" ".join(map(str, args)))).encode()
                        + out.stdout + out.stderr + b"\n# rc=%d\n" % out.returncode)
        self.lab.logs[tag] = log
        return out

    def dfn(self, tag, *args, timeout=180):
        """One DTN-developer-image command (text), logged by Lab.fn."""
        return self.lab.fn(tag, *args, timeout=timeout)

    def serve(self, name, peer, mru, tag):
        n = self.nodes[name]
        contact = dict(a=self.nodes["x"]["port"], b=self.nodes["y"]["port"],
                       x=self.r_ports["r1"][0], y=self.r_ports["r2"][0])[name]
        # A relay binds its listener set ("-"); an endpoint its one boundary's
        # port; the ambiguous-peer case serves X on the shared port.
        port = ("-" if name in ("x", "y") and self.args.case == "mission"
                else n["port"])
        proc, log = self.lab.spawn(
            tag, "bp-node", "serve", port, n["fnbs"], n["store"], n["rj"], n["wf"],
            n["eid"], peer, n["eid"], "native-policy", n["eid"], "127.0.0.1", contact,
            "0", 3600000, 2, 32, mru, self.lab.wall, 60000)
        listening = self.lab.wait_log(log, r"BP NODE LISTENING", 180)
        n["serve"] = proc
        n["incarnations"].append(dict(tag=tag, pid=proc.pid, peer=peer, mru=mru, port=port,
                                      listening=bool(listening),
                                      at=round(time.monotonic() - self.t0, 1)))
        return proc, log

    def stop_node(self, name, how="SIGTERM"):
        n = self.nodes[name]
        if n["serve"] is not None:
            self.lab.stop(n["serve"], how)
            n["incarnations"][-1]["stopped"] = next(
                p["stopped"] for p in self.lab.procs if p["proc"] is n["serve"])
            n["serve"] = None

    def owner(self, name, tag):
        n = self.nodes[name]
        log = self.lab.path(tag + ".log")
        handle = log.open("wb")
        argv = [str(self.owner_image), "--fn", "operator", str(n["owner_config"]), "run"]
        handle.write(("$ fn[developer] operator {} run\n".format(n["owner_config"])).encode())
        handle.flush()
        proc = subprocess.Popen(argv, stdout=handle, stderr=subprocess.STDOUT,
                                env=self.lab.env, cwd=str(ROOT))
        self.lab.procs.append(dict(tag=tag, pid=proc.pid, proc=proc))
        self.lab.logs[tag] = log
        ready = self.lab.wait_log(log, r"LISTENING ", 180)
        return proc, bool(ready)

    def wait(self, log, pattern, timeout=None, after=0):
        """Wait for PATTERN in LOG beyond character offset AFTER."""
        deadline = time.time() + (timeout or self.args.settle)
        rx = re.compile(pattern)
        while time.time() < deadline:
            text = Path(log).read_text(errors="replace")[after:]
            m = rx.search(text)
            if m:
                return m
            time.sleep(0.3)
        return None

    def wait_count(self, log, pattern, count, timeout=None):
        """Wait until PATTERN occurs COUNT times in LOG."""
        deadline = time.time() + (timeout or self.args.settle)
        rx = re.compile(pattern)
        while time.time() < deadline:
            if len(rx.findall(Path(log).read_text(errors="replace"))) >= count:
                return True
            time.sleep(0.3)
        return False

    def size(self, log):
        return len(Path(log).read_text(errors="replace"))

    # --- reporting ---------------------------------------------------------
    def step(self, name, outcome, held, tags, **extra):
        row = dict(step=name, outcome=outcome, held=bool(held),
                   t=round(time.monotonic() - self.t0, 1), **extra)
        row["logs"] = {t: dict(file=self.lab.logs[t].name, sha256=sha256(self.lab.logs[t]),
                               lines=lines_of(self.lab.logs[t]))
                       for t in tags if t in self.lab.logs}
        self.steps.append(row)
        print("STEP {} held={} outcome={}".format(name, row["held"], outcome), flush=True)
        return row

    def finding(self, text, classification, line=None, where=None):
        self.findings.append(dict(finding=text, classification=classification,
                                  line=line, where=where))
        print("FINDING [{}] {} :: {}".format(classification, text, line), flush=True)

    def grep(self, tag, prefix):
        return [l for l in lines_of(self.lab.logs[tag]) if l.startswith(prefix)] \
            if tag in self.lab.logs else []

    def frames(self, name):
        d = self.nodes[name]["fnbs"] / "lifecycle"
        return sorted(p.name for p in d.glob("*.fnb")) if d.exists() else []


def forward_lines(log):
    """The relay's forwarding lines, the attempt key (printed over several
    lines by the host) joined, and its bundle ID's EID octets shown as text."""
    text = Path(log).read_text(errors="replace")
    out = []
    for m in re.finditer(r"^(BP forwarding (?:attempt durable key=|result durable|route)"
                         r".*(?:\n[ \t]+.*)*)", text, re.M):
        line = " ".join(m.group(1).split())
        eid = re.search(r"\(:DTN ((?:\d+ ?)+)\)", line)
        if eid:
            line += "  [bundle source dtn:{}]".format(
                bytes(int(v) for v in eid.group(1).split()).decode("ascii", "replace"))
        out.append(line)
    return out


def make_author(lab, name, principal_byte, openssl):
    d = lab.path(name)
    d.mkdir(parents=True, exist_ok=True)
    (d / "principal").write_bytes(bytes([principal_byte]) * 32)
    public, secret = ED_KEYS[name]
    (d / "ed25519.public").write_bytes(bytes.fromhex(public))
    (d / "ed25519.secret").write_bytes(bytes.fromhex(secret + public))
    subprocess.run([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                    str(d / "ml-dsa-65.private.pem")], check=True, timeout=60)
    subprocess.run([openssl, "pkey", "-in", str(d / "ml-dsa-65.private.pem"), "-pubout",
                    "-out", str(d / "ml-dsa-65.public.pem")], check=True, timeout=60)
    return d


def article(msgid, subject, author, lines, what, path=False):
    body = b"".join(b"line %04d of the %s\r\n" % (i, what.encode()) for i in range(lines))
    return ((b"Path: " + path.encode() + b"!not-for-mail\r\n" if path else b"") + b"From: " + author.encode() + b"@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: " + subject.encode() + b"\r\n"
            b"Date: Fri, 25 Sep 2026 12:00:00 +0000\r\n"
            b"Message-ID: " + msgid.encode() + b"\r\n\r\n" + body)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--image", required=True, help="fn-host-dtn-developer (BP nodes)")
    ap.add_argument("--owner-image", required=True,
                    help="fn-host-developer (owners, consumer, hybrid verbs)")
    ap.add_argument("--dtn7-repo", required=True, type=Path)
    ap.add_argument("--work", required=True, type=Path)
    ap.add_argument("--settle", type=float, default=90.0)
    ap.add_argument("--x-mru", type=int, default=4096,
                    help="X's announced TCPCL Transfer MRU while it carries the request")
    ap.add_argument("--report", choices=("signed", "unsigned"), default="signed",
                    help="signed (the default): A's author signs the report and "
                         "`hybrid-author' stores its portable carrier; unsigned: the "
                         "control, `store post' of a Path-bearing source")
    ap.add_argument("--report-lines", type=int, default=110,
                    help="body lines of the report (the request must exceed --x-mru)")
    ap.add_argument("--openssl", default=os.environ.get("FN_TEST_OPENSSL", "openssl"))
    ap.add_argument("--case", choices=("mission", "ambiguous-peer"), default="mission",
                    help="mission (the default): all seven steps; ambiguous-peer: the "
                         "relays' two boundaries share one listener, steps 0 and 1")
    args = ap.parse_args(argv)
    m = Mission(args)
    lab, nodes = m.lab, m.nodes
    repo = args.dtn7_repo.resolve()
    report = dict(image=str(lab.image), image_sha256=sha256(lab.image),
                  owner_image=str(m.owner_image), owner_image_sha256=sha256(m.owner_image),
                  dtn_time_ms=lab.wall, x_request_mru=args.x_mru,
                  dtn7_revision=subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                                               capture_output=True, text=True).stdout.strip(),
                  topology="A -> X -> dtn7 r1 -> dtn7 r2 -> Y -> B and back",
                  case=args.case,
                  ports=dict({k: v["port"] for k, v in nodes.items()},
                             x_far=nodes["x"]["port_far"], y_far=nodes["y"]["port_far"],
                             r1=m.r_ports["r1"], r2=m.r_ports["r2"]))
    identity = {}
    try:
        # === 0. setup ======================================================
        setup = {}

        def ok(tag, result):
            setup[tag] = result.returncode
            return result

        for n in nodes.values():
            ok("setup-init-" + n["name"], m.dfn("setup-init-" + n["name"], "store",
                                                n["store"], "init", "fn.test"))
            n["config"].write_text('[store]\npath = "{}"\n'.format(n["store"]), encoding="ascii")
            n["owner_config"].write_text(
                '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                '[control]\npath = "{}"\n[log]\npath = "{}"\n'.format(
                    n["store"], free_port(), n["control"],
                    lab.path(n["name"] + "-owner-service.log")), encoding="ascii")
            ok("setup-path-" + n["name"], m.dfn(
                "setup-path-" + n["name"], "operator", n["config"], "policy", "set",
                "path-identity", "{}.mission.invalid".format(n["name"])))
        # Boundaries: (node, name, remote path, eid, extra, contact port).
        # PORT (the 4th operand) is this node's own listener: the boundary is
        # observed on it.  An author boundary names a port nothing listens on.
        xp, yp = nodes["x"]["port"], nodes["y"]["port"]
        xf, yf = nodes["x"]["port_far"], nodes["y"]["port_far"]
        rows = [
            ("a", "x-boundary", "x.mission.invalid", X, nodes["a"]["port"],
             ["carries", B, "releases-for", B], xp),
            ("a", "b-author", "b.mission.invalid", B, free_port(), SCOPE, None),
            ("b", "y-boundary", "y.mission.invalid", Y, nodes["b"]["port"],
             ["carries", A, "releases-for", A], yp),
            ("b", "a-author", "a.mission.invalid", A, free_port(), SCOPE, None),
            ("x", "a-boundary", "a.mission.invalid", A, xp, [], nodes["a"]["port"]),
            ("x", "r1-boundary", "r1.mission.invalid", R1, xf, [], m.r_ports["r1"][0]),
            ("y", "b-boundary", "b.mission.invalid", B, yp, [], nodes["b"]["port"]),
            ("y", "r2-boundary", "r2.mission.invalid", R2, yf, [], m.r_ports["r2"][0]),
        ]
        for node, name, remote, eid, port, extra, contact in rows:
            tag = "setup-{}-{}".format(node, name)
            ok(tag, m.dfn(tag, "operator", nodes[node]["config"], "bp-boundary", "add",
                          name, remote, eid, port, *extra,
                          *(["contact", contact] if contact else [])))
        routes = [("a", B, "x-boundary"), ("b", A, "y-boundary"),
                  ("x", B, "r1-boundary"), ("x", A, "a-boundary"),
                  ("y", A, "r2-boundary"), ("y", B, "b-boundary")]
        for node, dest, via in routes:
            tag = "setup-{}-route-{}".format(node, via)
            ok(tag, m.dfn(tag, "operator", nodes[node]["config"], "bp-route", "add",
                          dest + "*", via))
        authors = {k: make_author(lab, k, b, args.openssl)
                   for k, b in (("author-a", 0x41), ("author-b", 0x42))}
        report["authors"] = {k: (d / "principal").read_bytes().hex() for k, d in authors.items()}
        src_a = lab.path("report.source")
        src_a.write_bytes(article(REPORT_ID, "mission report from fn-a", "author-a",
                                  args.report_lines, "mission report carried by bp",
                                  path=args.report == "unsigned" and "a.mission.invalid"))
        src_b = lab.path("reply.source")
        src_b.write_bytes(article(REPLY_ID, "Re: mission report from fn-a", "author-b", 12,
                                  "mission reply",
                                  path=args.report == "unsigned" and "b.mission.invalid"))

        def sign(tag, author, source):
            d = authors[author]
            out = m.ofn(tag, "hybrid-sign", d / "principal", d / "ed25519.public",
                        d / "ed25519.secret", d / "ml-dsa-65.public.pem",
                        d / "ml-dsa-65.private.pem", source)
            setup[tag] = out.returncode
            parts = dict(l.split() for l in out.stdout.decode().splitlines()
                         if len(l.split()) == 2)
            ed, ml = source.with_suffix(".ed.sig"), source.with_suffix(".ml.sig")
            ed.write_bytes(bytes.fromhex(parts.get("ed25519", "")))
            ml.write_bytes(bytes.fromhex(parts.get("ml-dsa-65", "")))
            return ed, ml

        consumer_out = {}

        def enroll(name, author):
            d = authors[author]
            tag = "setup-{}-enroll-{}".format(name, author)
            ok(tag, m.ofn(tag, "hybrid-enroll", nodes[name]["control"], GENERATION[author],
                          d / "principal", d / "ed25519.public", d / "ml-dsa-65.public.pem"))

        def consumer(tag, name, verb, *rest):
            out = m.ofn(tag, "consumer", verb, nodes[name]["control"], *rest)
            consumer_out[tag] = dict(rc=out.returncode, outcome=outcome_of(out.returncode),
                                     stdout=out.stdout.decode(errors="replace").strip())
            return out

        def drain(name, reader, target, tag):
            """Poll and ack one event at a time until the event naming TARGET
            (a Message-ID) arrives or a poll returns no event.  Each poll and
            ack is the owner's own answer; the driver only reads which
            Message-ID the returned event octets carry."""
            seen = []
            for i in range(16):
                cursor = lab.path("{}-{}.fncu".format(tag, i))
                event = lab.path("{}-{}.event".format(tag, i))
                polled = consumer("{}-poll-{}".format(tag, i), name, "poll", reader,
                                  cursor, event)
                octets = event.read_bytes() if event.exists() else b""
                found = re.search(rb"(?im)^Message-ID: *(<[^>\r\n]*>)", octets)
                row = dict(poll=outcome_of(polled.returncode), octets=len(octets),
                           sha256=hashlib.sha256(octets).hexdigest(),
                           message_id=found.group(1).decode() if found else None)
                seen.append(row)
                if polled.returncode != 0 or not octets:
                    return seen, None, octets
                acked = consumer("{}-ack-{}".format(tag, i), name, "ack", cursor)
                row["ack"] = outcome_of(acked.returncode)
                if acked.returncode != 0:
                    return seen, None, octets
                if target.encode() in octets:
                    return seen, row, octets
            return seen, None, b""

        # A's owner: enrol both authors, author the report, register A's
        # consumer after it (so A's poll can only see what arrives later).
        if args.report == "unsigned":
            # The control: the report is posted before A's consumer registers.
            ok("setup-a-post-unsigned", m.dfn("setup-a-post-unsigned", "store",
                                              nodes["a"]["store"], "post", REPORT_ID, src_a,
                                              "-", "-", "fn.test"))
        owner_a, ready = m.owner("a", "setup-a-owner")
        setup["setup-a-owner-ready"] = 0 if ready else 1
        enroll("a", "author-a")
        if args.report == "signed":
            ed, ml = sign("setup-a-sign", "author-a", src_a)
            signed_a = m.ofn("setup-a-author", "hybrid-author", nodes["a"]["control"],
                             GENERATION["author-a"], src_a, ed, ml,
                             authors["author-a"] / "ml-dsa-65.public.pem")
            report["report_signed"] = signed_a.returncode == 0
        else:
            report["report_signed"] = None
        enroll("a", "author-b")
        setup["setup-a-bootstrap"] = consumer("setup-a-bootstrap", "a", "bootstrap").returncode
        setup["setup-a-register"] = consumer("setup-a-register", "a", "register", "a-reader",
                                             "fn.test", lab.path("a-registered.fncu")).returncode
        lab.stop(owner_a)
        # B's owner: enrol both authors, register B's consumer (asleep).
        owner_b, ready = m.owner("b", "setup-b-owner")
        setup["setup-b-owner-ready"] = 0 if ready else 1
        enroll("b", "author-a")
        enroll("b", "author-b")
        setup["setup-b-bootstrap"] = consumer("setup-b-bootstrap", "b", "bootstrap").returncode
        setup["setup-b-register"] = consumer("setup-b-register", "b", "register", "b-reader",
                                             "fn.test", lab.path("b-registered.fncu")).returncode
        lab.stop(owner_b)
        if report["report_signed"] is False:
            # Keep the transport scenario going with the unsigned source.
            m.finding("hybrid-author refused the report on A; posted unsigned instead",
                      "see-evidence", (lines_of(lab.logs["setup-a-author"]) or
                                       [lab.logs["setup-a-author"].read_text()[-200:]])[-1], "A")
            ok("setup-a-post-unsigned", m.dfn("setup-a-post-unsigned", "store",
                                              nodes["a"]["store"], "post", REPORT_ID, src_a,
                                              "-", "-", "fn.test"))
        # The stored report as A's Store holds it (what the request carries).
        inspect_a = subprocess.run([str(lab.image), "--fn", "store", str(nodes["a"]["store"]),
                                    "inspect", REPORT_ID], capture_output=True,
                                   env=lab.env, cwd=str(ROOT), timeout=120)
        lab.path("a-stored.report").write_bytes(inspect_a.stdout)
        setup["setup-a-inspect"] = inspect_a.returncode
        # A's and B's obligations' workflows.
        for tag, argv in (
                ("setup-a-wf-init", ("app-journal", "workflow-init", nodes["a"]["store"],
                                     nodes["a"]["wf"], A, B, "native-policy", B, 3600000,
                                     "origin-native", "wire-auth")),
                ("setup-a-wf-enqueue", ("app-journal", "workflow-enqueue", nodes["a"]["store"],
                                        nodes["a"]["wf"], 1, 0, WORK_A, REPORT_ID,
                                        "forward-report", B, "native-policy", "terms-native")),
                ("setup-a-undertake", ("bp-obligation", "undertake", nodes["a"]["store"],
                                       nodes["a"]["wf"], WORK_A, 3)),
                ("setup-b-wf-init", ("app-journal", "workflow-init", nodes["b"]["store"],
                                     nodes["b"]["wf"], B, A, "native-policy", A, 3600000,
                                     "origin-native", "wire-auth"))):
            ok(tag, m.dfn(tag, *argv))
        a_status0 = m.dfn("a-status-0", "bp-obligation", "status", nodes["a"]["store"],
                          nodes["a"]["wf"], WORK_A).stdout.strip()
        report["setup_rcs"] = setup
        setup_ok = all(v == 0 for v in setup.values())
        m.step("0 setup: stores, D23 boundaries, routes, {} report, consumers asleep, "
               "A's obligation undertaken".format(args.report), "accepted" if setup_ok else "refused", setup_ok,
               [t for t in lab.logs if t.startswith("setup")] + ["a-status-0"],
               rcs=setup, a_status=a_status0, consumers=consumer_out,
               a_stored_report=dict(rc=inspect_a.returncode,
                                    octets=len(inspect_a.stdout),
                                    sha256=hashlib.sha256(inspect_a.stdout).hexdigest()))
        identity["authored_source_report_sha256"] = sha256(src_a)
        identity["a_stored_report_sha256"] = hashlib.sha256(inspect_a.stdout).hexdigest()

        # dtn7 relays (not started yet).
        r1p, r2p = m.r_ports["r1"], m.r_ports["r2"]
        m.relays["r1"] = Relay(repo, lab.work, "dtn7-r1", *r1p,
                               "1 {}* {}* {}\n2 {}* {}* {}\n".format(A, B, R2, B, A, X),
                               ["tcp://127.0.0.1:{}/dtn7-r2".format(r2p[0]),
                                "tcp://127.0.0.1:{}/fn-x".format(xf)])
        m.relays["r2"] = Relay(repo, lab.work, "dtn7-r2", *r2p,
                               "1 {}* {}* {}\n2 {}* {}* {}\n".format(A, B, Y, B, A, R1),
                               ["tcp://127.0.0.1:{}/dtn7-r1".format(r1p[0]),
                                "tcp://127.0.0.1:{}/fn-y".format(yf)])
        r1, r2 = m.relays["r1"], m.relays["r2"]

        # === 1. A's request, fragmented to X; r1 down, X holds ==============
        _, b_log = m.serve("b", A, 1048576, "b-serve-1")
        _, y_log = m.serve("y", B, 1048576, "y-serve-1")
        _, x_log = m.serve("x", B, args.x_mru, "x-serve-1")
        req = m.dfn("a-1-request", "bp-obligation", "request", nodes["a"]["store"],
                    nodes["a"]["wf"], WORK_A, WORK_A + "-a1", nodes["a"]["fnbs"], A,
                    "127.0.0.1", xp, 3600000, 2, 32, 1048576, lab.wall, 60000)
        if args.case == "ambiguous-peer":
            # PRF-128: the refused channel's transfer is refused with the
            # policy's reason; X writes no kind-5 custody for it.
            refused = m.wait(x_log, r"BP refused xfer=\d+ reason=ambiguous-peer", 60)
            admission = m.wait(x_log, r"BP channel admission refused reason=ambiguous-peer", 5)
            time.sleep(3.0)
            a_status1 = m.dfn("a-status-1", "bp-obligation", "status", nodes["a"]["store"],
                              nodes["a"]["wf"], WORK_A).stdout.strip()
            custody = m.grep("x-serve-1", "BP accepted")
            m.step("1 ambiguous-peer: X's two boundaries share one listener; X refuses A's "
                   "transfer with the policy's reason and takes no custody; A keeps its pin",
                   outcome_of(req.returncode),
                   bool(refused and admission and not custody and "pinned=yes" in a_status1),
                   ["a-1-request", "x-serve-1", "a-status-1"],
                   x_refused=m.grep("x-serve-1", "BP refused"),
                   x_admission=m.grep("x-serve-1", "BP channel admission"),
                   x_custody=custody, x_frames=m.frames("x"), a_status=a_status1,
                   a_request=lines_of(lab.logs["a-1-request"]))
            raise Stop()
        family = m.wait(x_log, r"BP fragment family durable")
        unavailable = m.wait(x_log, r"BP forwarding session unavailable", 60)
        reqlines = lines_of(lab.logs["a-1-request"])
        frag = [l for l in reqlines if l.startswith("BP fragmenting")]
        pieces = int(frag[0].rsplit("fragments=", 1)[1]) if frag else 0
        accepted_frags = [l for l in reqlines if re.match(r"BP fragment \d+ transfer accepted", l)]
        held1 = (req.returncode == 0 and pieces > 1 and "peer-mru={} ".format(args.x_mru)
                 in frag[0] + " " and bool(family) and bool(unavailable))
        m.step("1 A requests via X; X's MRU forces fragments; X reassembles and holds "
               "(r1 down)", outcome_of(req.returncode), held1, ["a-1-request", "x-serve-1"],
               fragmenting=frag, fragments_accepted=accepted_frags,
               x_family=bool(family), x_forward_unavailable=bool(unavailable),
               x_frames=m.frames("x"))
        identity["a_request_attempt"] = [l for l in reqlines if l.startswith(
            ("BP obligation request durable", "BP obligation request carrier",
             "BP queue accepted", "BP queue route", "BP queued job"))]

        # === 2. X SIGKILLed; r1 up; X restarts and forwards; r2 later ======
        m.stop_node("x", "SIGKILL")
        r1.start()
        _, x_log2 = m.serve("x", B, args.x_mru, "x-serve-2")
        sent_x = m.wait(x_log2, r"BP forwarding result durable arrival=\d+ status=sent")
        recovered = m.wait(x_log2, r"BP FNBS recovered held=\d+", 5)
        time.sleep(3.0)
        r2.start()
        m.step("2 X SIGKILLed while holding; r1 starts; X restarts from FNBS and forwards "
               "to r1; r2 starts later", "accepted" if sent_x else "no-forward",
               bool(sent_x and recovered), ["x-serve-2"],
               x_killed=nodes["x"]["incarnations"][0],
               x_recovered=recovered.group(0) if recovered else None,
               x_route=m.grep("x-serve-2", "BP forwarding route"),
               x_attempts=m.grep("x-serve-2", "BP forwarding attempt durable"),
               x_results=m.grep("x-serve-2", "BP forwarding result"))
        # X goes down now: the receipt meets its own outage (step 4).
        m.stop_node("x", "SIGTERM")

        # === 3. B admits, custody, Store, receipt queued ===================
        verdict = m.wait(b_log, r"BP node delivery (request-\S+)")
        queued = m.wait(b_log, r"BP node receipt queued id=\S+", 30)
        contact = m.wait(b_log, r"BP node receipt contact peer=\S+", 30)
        time.sleep(3.0)
        blines = lines_of(b_log)
        held3 = bool(verdict and verdict.group(1) == "request-accepted" and queued)
        m.step("3 B admits (D23 carried), kind-5 custody, Store delivery, receipt queued "
               "toward fn-a via Y", verdict.group(1) if verdict else "no-verdict", held3,
               ["y-serve-1", "b-serve-1"],
               y_forward=m.grep("y-serve-1", "BP forwarding"),
               b_transport=[l for l in blines if l.startswith("BP accepted")],
               b_source=[l for l in blines if l.startswith("BP node source")],
               b_application=[l for l in blines if l.startswith(("BP node delivery",
                                                                  "BP application"))],
               b_receipt=[l for l in blines if "receipt" in l],
               b_frames=m.frames("b"))
        if not verdict:
            m.finding("B never delivered the request", "unknown-see-logs",
                      (lines_of(b_log) or [None])[-1], "B")
        elif verdict.group(1) != "request-accepted":
            m.finding("B's BP application refused the {} report after custody and D23 "
                      "admission (ACL2's reason is on the refusal line)".format(args.report),
                      "implementation", " | ".join(
                          l for l in blines if l.startswith(("BP node source",
                                                             "BP application",
                                                             "BP node delivery"))), "B")

        # === 4. the receipt's own outage ===================================
        # B offered its receipt to Y on b-boundary's listener right after the
        # delivery (Y binds both of its boundaries); Y routes it (destination
        # fn-a) to r2, r2 to r1, and r1 holds it: X is down.
        y_had = m.wait(y_log, r"BP accepted.*[\s\S]*BP accepted", 20)
        _, a_log1 = m.serve("a", B, 1048576, "a-serve-1")
        y_sent = m.wait_count(y_log, r"BP forwarding result durable arrival=\d+ status=sent", 2)
        # r1 now holds the receipt: X is down.  A dies meanwhile, by SIGKILL.
        time.sleep(6.0)
        m.stop_node("a", "SIGKILL")
        _, a_log = m.serve("a", B, 1048576, "a-serve-2")
        # X's outage ends: the same argv as before.
        _, x_log3 = m.serve("x", B, 1048576, "x-serve-3")
        receipt = m.wait(a_log, r"BP node delivery (receipt-\S+)")
        time.sleep(2.0)
        m.stop_node("a", "SIGTERM")
        a_status = m.dfn("a-status-4", "bp-obligation", "status", nodes["a"]["store"],
                         nodes["a"]["wf"], WORK_A).stdout.strip()
        settled = bool(receipt and receipt.group(1) == "receipt-accepted"
                       and "pinned=no" in a_status)
        m.step("4 B's receipt crosses its own outage (X down, A SIGKILLed) and settles at A "
               "before B's consumer wakes", receipt.group(1) if receipt else "no-receipt",
               settled and bool(y_sent), ["y-serve-1", "b-serve-1", "x-serve-3", "a-serve-1",
                                          "a-serve-2", "a-status-4"],
               y_first_held_receipt=bool(y_had), y_forwarded=bool(y_sent),
               x_forward=m.grep("x-serve-3", "BP forwarding"),
               a_receipt=m.grep("a-serve-2", "BP node"), a_status=a_status,
               a_frames=m.frames("a"))
        identity["a_receipt_outcome"] = receipt.group(1) if receipt else None
        identity["a_obligation_after_receipt"] = a_status

        # === 5. B's consumer wakes; B's node stops for B's owner (K6) =======
        m.stop_node("b", "SIGTERM")
        inspect_b = subprocess.run([str(lab.image), "--fn", "store", str(nodes["b"]["store"]),
                                    "inspect", REPORT_ID], capture_output=True,
                                   env=lab.env, cwd=str(ROOT), timeout=120)
        b_copy = lab.path("b-delivered.report")
        b_copy.write_bytes(inspect_b.stdout)
        verify = m.ofn("b-5-verify-source", "hybrid-verify-source", b_copy,
                       authors["author-a"] / "ml-dsa-65.public.pem")
        vline = verify.stdout.decode(errors="replace").strip()
        exported = vline.split()[-1] if vline.startswith("fn-portable-v1") else None
        exported_sha = (hashlib.sha256(bytes.fromhex(exported)).hexdigest()
                        if exported else None)
        identity["b_delivered_report_sha256"] = hashlib.sha256(inspect_b.stdout).hexdigest()
        identity["b_verified_source_sha256"] = exported_sha
        if verify.returncode != 0 and args.report == "signed":
            m.finding("B's delivered copy does not verify with hybrid-verify-source",
                      "unexercised-capability-or-implementation", vline[:200], "B")
        owner_b, ready_b = m.owner("b", "b-5-owner")
        polls_b, hit_b, event_octets = drain("b", "b-reader", REPORT_ID, "b-5")
        if hit_b is None and held3:
            m.finding("B's consumer never polled an event carrying the BP-delivered report",
                      "unexercised-capability", json.dumps(polls_b), "B")
        if (args.report == "signed" and hit_b and event_octets
                and src_a.read_bytes() not in event_octets):
            m.finding("B's poll event does not contain the exact authored source octets",
                      "see-evidence", None, "B")
        if args.report == "signed":
            ed, ml = sign("b-5-sign-reply", "author-b", src_b)
            authored_b = m.ofn("b-5-author-reply", "hybrid-author", nodes["b"]["control"],
                               GENERATION["author-b"], src_b, ed, ml,
                               authors["author-b"] / "ml-dsa-65.public.pem")
            report["reply_signed"] = authored_b.returncode == 0
        else:
            authored_b, report["reply_signed"] = None, None
        lab.stop(owner_b)
        if authored_b is None or authored_b.returncode != 0:
            if authored_b is not None:
                m.finding("hybrid-author refused the reply on B; posted unsigned instead",
                          "see-evidence", lab.logs["b-5-author-reply"].read_text()[-200:], "B")
            m.dfn("b-5-post-unsigned", "store", nodes["b"]["store"], "post", REPLY_ID, src_b,
                  "-", "-", "fn.test")
        for tag, argv in (
                ("b-5-enqueue", ("app-journal", "workflow-enqueue", nodes["b"]["store"],
                                 nodes["b"]["wf"], 1, 0, WORK_B, REPLY_ID, "forward-reply", A,
                                 "native-policy", "terms-native")),
                ("b-5-undertake", ("bp-obligation", "undertake", nodes["b"]["store"],
                                   nodes["b"]["wf"], WORK_B, 3))):
            m.dfn(tag, *argv)
        # A listens before the reply arrives; X and Y serve both directions.
        _, a_log3 = m.serve("a", B, 1048576, "a-serve-3")
        req_b = m.dfn("b-5-request", "bp-obligation", "request", nodes["b"]["store"],
                      nodes["b"]["wf"], WORK_B, WORK_B + "-a1", nodes["b"]["fnbs"], B,
                      "127.0.0.1", yp, 3600000, 2, 32, 1048576, lab.wall, 60000)
        # K6: B's node serves again (its owner has released the Store's
        # writer lock) to hear A's receipt for the reply.
        _, b_log2 = m.serve("b", A, 1048576, "b-serve-2")
        held5 = ((verify.returncode == 0 or args.report == "unsigned") and ready_b
                 and hit_b is not None and req_b.returncode == 0)
        m.step("5 B's consumer wakes after A settled: verify, poll, ack; B signs a reply "
               "and requests it toward fn-a", outcome_of(req_b.returncode), held5,
               ["b-5-verify-source", "b-5-owner"] + [t for t in lab.logs if t.startswith(
                   ("b-5-poll", "b-5-ack"))] + ["b-5-sign-reply",
                "b-5-author-reply", "b-5-enqueue", "b-5-undertake", "b-5-request"],
               verify=dict(rc=verify.returncode, line=vline[:160],
                           exported_equals_authored=(exported is not None and
                                                     bytes.fromhex(exported) ==
                                                     src_a.read_bytes())),
               b_inspect=dict(rc=inspect_b.returncode, octets=len(inspect_b.stdout)),
               polls=polls_b, report_event=hit_b,
               event_contains_authored_source=src_a.read_bytes() in event_octets,
               reply_author_rc=(authored_b.returncode if authored_b else None),
               reply_signed=report["reply_signed"],
               reply_request=[l for l in lines_of(lab.logs["b-5-request"])])
        identity["authored_source_reply_sha256"] = sha256(src_b)
        identity["b_request_attempt"] = [l for l in lines_of(lab.logs["b-5-request"])
                                         if l.startswith(("BP obligation request",
                                                          "BP queue accepted",
                                                          "BP queue route"))]

        # === 6. the reply crosses back; A's receipt releases B's pin =======
        a_verdict = m.wait(a_log3, r"BP node delivery (request-\S+)")
        a_queued = m.wait(a_log3, r"BP node receipt queued id=\S+", 30)
        a_contact = m.wait(a_log3, r"BP node receipt contact peer=\S+", 30)
        time.sleep(3.0)
        # A offered its receipt to X on a-boundary's listener right after the
        # delivery; X routes it (destination fn-b) to r1, r1 to r2, r2 to Y
        # on r2-boundary's listener, and Y to B.  No turns, no restarts.
        x_sent = m.wait_count(x_log3, r"BP forwarding result durable arrival=\d+ status=sent", 3)
        b_receipt = m.wait(b_log2, r"BP node delivery (receipt-\S+)")
        time.sleep(2.0)
        m.stop_node("b", "SIGTERM")
        m.stop_node("a", "SIGTERM")
        b_status = m.dfn("b-6-status", "bp-obligation", "status", nodes["b"]["store"],
                         nodes["b"]["wf"], WORK_B).stdout.strip()
        # A's consumer wakes.
        owner_a, ready_a = m.owner("a", "a-6-owner")
        polls_a, hit_a, event_a_octets = drain("a", "a-reader", REPLY_ID, "a-6")
        status_a_consumer = consumer("a-6-consumer-status", "a", "status", "a-reader")
        lab.stop(owner_a)
        if a_verdict and a_verdict.group(1) != "request-accepted":
            m.finding("A's BP application refused B's {} reply (ACL2's reason is on the "
                      "refusal line)".format("signed" if report.get("reply_signed") else "unsigned"),
                      "implementation", " | ".join(
                          l for l in lines_of(a_log3) if l.startswith(
                              ("BP node source", "BP application", "BP node delivery"))), "A")
        if hit_a is None and a_verdict and a_verdict.group(1) == "request-accepted":
            m.finding("A's consumer never polled an event carrying the BP-delivered reply",
                      "unexercised-capability", json.dumps(polls_a), "A")
        held6 = bool(a_verdict and a_verdict.group(1) == "request-accepted" and b_receipt
                     and b_receipt.group(1) == "receipt-accepted" and "pinned=no" in b_status
                     and hit_a is not None)
        m.step("6 the reply crosses back; A delivers; A's receipt releases B's pin; A's "
               "consumer wakes, polls and acks",
               a_verdict.group(1) if a_verdict else "no-verdict", held6,
               ["a-serve-3", "x-serve-3", "y-serve-1", "b-serve-2", "b-6-status",
                "a-6-owner", "a-6-consumer-status"] + [t for t in lab.logs if t.startswith(
                    ("a-6-poll", "a-6-ack"))],
               a_application=m.grep("a-serve-3", "BP node"),
               a_receipt_queued=bool(a_queued), a_receipt_contact=bool(a_contact),
               x_forward=m.grep("x-serve-3", "BP forwarding"),
               y_forward=m.grep("y-serve-1", "BP forwarding"),
               b_receipt=m.grep("b-serve-2", "BP node"), b_status=b_status,
               polls=polls_a, reply_event=hit_a,
               event_contains_reply_source=src_b.read_bytes() in event_a_octets,
               consumer_status=consumer_out.get("a-6-consumer-status"))
        identity["b_receipt_outcome"] = b_receipt.group(1) if b_receipt else None
        identity["b_obligation_after_receipt"] = b_status
        if not x_sent and a_verdict and a_verdict.group(1) == "request-accepted":
            m.finding("X did not forward A's receipt toward fn-b", "see-logs",
                      (m.grep("x-serve-3", "BP forwarding") or [None])[-1], "X")
    except Stop:
        pass
    finally:
        for p in lab.procs:
            if p["proc"].poll() is None:
                lab.stop(p["proc"])
            p.setdefault("stopped", "exited rc={}".format(p["proc"].returncode))
        for d in m.relays.values():
            d.stop()
        # --- 7. identities and log digests ---------------------------------
        bundles = {}
        for d in m.relays.values():
            for s in d.starts:
                text = Path(s["log"]).read_text(errors="replace")
                ids = sorted(set(re.findall(r"dtn://fn-[abxy]/-\d+-\d+(?:-\d+-\d+)?", text)))
                bundles[Path(s["log"]).parent.name + "/" + Path(s["log"]).name] = ids
        identity["bundles_as_logged_by_dtn7"] = bundles
        identity["forwarding_attempts"] = {
            t: forward_lines(lab.logs[t]) for t in lab.logs if re.match(r"[xy]-serve-\d", t)}
        identity["channel_admission_refusals"] = {
            t: len(re.findall(r"BP channel admission refused reason=\S+",
                              lab.logs[t].read_text(errors="replace")))
            for t in lab.logs if re.match(r"[abxy]-serve-\d", t)}
        identity["fnbs_lifecycle_frames"] = {k: len(m.frames(k)) for k in nodes}
        identity["work"] = dict(a=dict(work=WORK_A, attempt=WORK_A + "-a1",
                                       message_id=REPORT_ID),
                                b=dict(work=WORK_B, attempt=WORK_B + "-a1",
                                       message_id=REPLY_ID))
        report["identity"] = identity
        report["incarnations"] = {k: v["incarnations"] for k, v in nodes.items()}
        report["processes"] = [dict(tag=p["tag"], pid=p["pid"], stopped=p["stopped"])
                               for p in lab.procs]
        report["dtnd_processes"] = {d.name: d.starts for d in m.relays.values()}
        logs = {t: sha256(p) for t, p in lab.logs.items() if Path(p).exists()}
        for d in m.relays.values():
            for s in d.starts:
                if Path(s["log"]).exists():
                    logs[Path(s["log"]).parent.name + "/" + Path(s["log"]).name] = sha256(s["log"])
        report["log_sha256"] = logs
        report["steps"] = m.steps
        report["findings"] = m.findings
        report["wall_seconds"] = round(time.monotonic() - m.t0, 1)
        report["all_steps_held"] = bool(m.steps) and \
            len(m.steps) == (7 if args.case == "mission" else 2) and \
            all(s["held"] for s in m.steps)
        out = lab.path("report.json")
        out.write_text(json.dumps(report, indent=2, sort_keys=True))
        print("REPORT {} all_steps_held={}".format(out, report["all_steps_held"]), flush=True)
    return 0 if report["all_steps_held"] else 1


if __name__ == "__main__":
    sys.exit(main())
