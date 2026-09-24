"""External-kill campaign on the production image: SIGKILL by pid, no selector.

The production image refuses every developer cut selector at start (exit 5,
`fnn-developer-selector-gate`), so the cut campaign
(`native_operator_campaign`) takes its cuts on the developer twin.  This
driver takes deaths on the production image itself: it starts one
`operator CFG run` owner on a fresh store, drives a stream of NNTP POSTs
through a separate client process per POST, and at scheduled instants sends
the owner SIGKILL by its recorded pid.  After each death it records the
store's state, the owner log, a read-only `store ROOT inspect` of the killed
article, and restarts the owner from the same store (the owner recovers at
start, as the served node does under its unit).  It then rereads every POST
of the iteration by NNTP ARTICLE, resubmits every POST that died without a
reply, and takes the group's number map (GROUP, HDR Message-ID) before the
kill and after the restart.  At the end it stops the owner, rereads every
article by `inspect` and by a restarted owner's ARTICLE, and stops it again.

Kill instants: a calibration phase POSTs each size class unkilled and polls
the store directories to time the owner's visible phases (a stage file, the
new transaction, the stage removed, the reply).  The schedule then draws
delays, measured from the instant the client sent the article's terminating
line, in three bands per size: `early` (before the transaction appears),
`window` (from just before the transaction appears to just after the
reply: the durable-completion window, sampled most densely) and `late`
(after the reply), plus `mid-article` deaths with part of the article sent.
Concurrent kills hold two clients with bodies sent, release both
terminators, and kill after the second.

The client (`client` subcommand) exits 0 on `240`, 1 on any other `441`, 3
on `441 ... uncertain` or a connection that ended with no reply, and 4 on
anything else.  The driver judges nothing; the `judge` subcommand computes
every verdict from the JSON record.

Run on hbox with the frozen image directory:

    python3 -m tests.campaign.native_production_kill run \\
        --image /abs/gate/build/fn-host --work /abs/scratch/work \\
        --out run.json --seed 1
    python3 -m tests.campaign.native_production_kill judge run.json
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
import random
import select
import shutil
import signal
import socket
import statistics
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(ROOT))
from tests.campaign.native_operator_campaign import (  # noqa: E402
    GROUP, Node, injected_from, public, sha)

ACCEPTED, REFUSED, UNCERTAIN, UNEXPECTED = 0, 1, 3, 4
# Payload octets per size class.  fn-own-body-limit is 32768
# (books/owner.lisp *fn-store-max-payload*); `over` exceeds it.
# The default store profile (the one `operator init` writes and the live node
# runs) holds 128 transactions (tools/run_store.py MAX_TRANSACTION_COUNT; the
# owner refuses at host/native/owner.lisp `fnn-owner-attempt`).  A store is
# closed and a fresh one started before an iteration could reach it, so
# every kill meets a store with room to write.
ROTATE_AT = 116
SIZES = {"tiny": 180, "small": 2100, "medium": 12500, "large": 31000, "over": 33600}
NORMAL = ("tiny", "small", "medium", "large")


# ---------------------------------------------------------------------------
# The client: one POST, one process, an exit code per outcome.

def classify(reply: bytes | None) -> int:
    if reply is None:
        return UNEXPECTED
    if reply == b"":
        return UNCERTAIN
    if reply.startswith(b"240"):
        return ACCEPTED
    if reply.startswith(b"441"):
        return UNCERTAIN if b"uncertain" in reply else REFUSED
    return UNEXPECTED


class Wire:
    """A line reader over a raw socket; b"" is end of stream."""

    def __init__(self, port: int, timeout=30.0):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=timeout)
        self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.buf, self.eof, self.error = b"", False, None

    def readline(self, timeout: float) -> bytes | None:
        deadline = time.perf_counter() + timeout
        while b"\r\n" not in self.buf and not self.eof:
            left = deadline - time.perf_counter()
            if left <= 0:
                self.error = self.error or "timeout"
                return None
            if not select.select([self.sock], [], [], left)[0]:
                continue
            try:
                data = self.sock.recv(65536)
            except OSError as error:
                self.error, data = type(error).__name__, b""
            if not data:
                self.eof = True
            self.buf += data
        if b"\r\n" in self.buf:
            line, self.buf = self.buf.split(b"\r\n", 1)
            return line + b"\r\n"
        line, self.buf = self.buf, b""
        return line

    def send(self, data: bytes) -> str | None:
        try:
            self.sock.sendall(data)
            return None
        except OSError as error:
            return type(error).__name__


def text(line):
    return None if line is None else line.decode("latin-1")


def client(port: int, payload: bytes, stop_after: int | None, hold: bool) -> int:
    """POST `payload`.  Prints `SENT <perf_counter>` the moment the article's
    terminating line (or, with `stop_after`, that many octets) is written,
    then one JSON line; exits with `classify` of the reply."""
    rec = {"t_start": time.perf_counter()}
    reply = None
    try:
        wire = Wire(port)
        rec["greeting"] = text(wire.readline(30))
        rec["post_send_error"] = wire.send(b"POST\r\n")
        post_reply = wire.readline(30)
        rec["post_reply"] = text(post_reply)
        if post_reply is None or not post_reply.startswith(b"340"):
            reply = post_reply
        else:
            body = payload if stop_after is None else payload[:stop_after]
            rec["body_send_error"] = wire.send(body)
            if hold:
                print("READY", flush=True)
                sys.stdin.readline()
            if stop_after is None:
                rec["terminator_send_error"] = wire.send(b".\r\n")
            rec["t_sent"] = time.perf_counter()
            rec["sent_octets"] = len(body) + (3 if stop_after is None else 0)
            print("SENT {!r}".format(rec["t_sent"]), flush=True)
            reply = wire.readline(60)
            rec["t_reply"] = time.perf_counter()
            rec["eof"], rec["recv_error"] = wire.eof, wire.error
            if reply:
                wire.send(b"QUIT\r\n")
                rec["quit_reply"] = text(wire.readline(2))
    except OSError as error:
        rec["error"] = "{}: {}".format(type(error).__name__, error)
        reply = b"" if reply is None else reply
    rec["reply"] = text(reply)
    rec["code"] = classify(reply)
    print("RESULT " + json.dumps(rec), flush=True)
    return rec["code"]


def spawn_client(port: int, payload_path: Path, stop_after=None, hold=False):
    argv = [sys.executable, "-m", "tests.campaign.native_production_kill", "client",
            "--port", str(port), "--payload", str(payload_path)]
    if stop_after is not None:
        argv += ["--stop-after", str(stop_after)]
    if hold:
        argv.append("--hold")
    return subprocess.Popen(argv, cwd=ROOT, stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def wait_line(proc, prefix: bytes, timeout=60.0):
    """The next stdout line of `proc` that starts with `prefix`, or None."""
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if not select.select([proc.stdout], [], [], 1)[0]:
            if proc.poll() is not None:
                return None
            continue
        line = proc.stdout.readline()
        if not line:
            return None
        if line.startswith(prefix):
            return line
    return None


def reap_client(proc, timeout=90) -> dict:
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        out, err = proc.communicate()
    rec = {"rc": proc.returncode, "pid": proc.pid,
           "stderr": err.decode("utf-8", "replace")[-500:]}
    for line in out.splitlines():
        if line.startswith(b"RESULT "):
            rec.update(json.loads(line[7:]))
    return rec


def post_once(port: int, payload_path: Path) -> dict:
    proc = spawn_client(port, payload_path)
    return reap_client(proc)


# ---------------------------------------------------------------------------
# Articles, the store and the wire.

def make_article(message_id: str, size_class: str, seq: int) -> bytes:
    head = ("From: campaign@campaign.invalid\r\nNewsgroups: {}\r\n"
            "Subject: production kill {} {}\r\nMessage-ID: {}\r\n\r\n").format(
                GROUP, size_class, seq, message_id)
    marker = "article {} class {} {}\r\n".format(seq, size_class,
                                                 hashlib.sha256(message_id.encode()).hexdigest())
    body, target = [marker], SIZES[size_class] - len(head) - len(marker)
    row = 0
    while target > 0:
        line = ("{:06d} ".format(row) + "abcdefghijklmnopqrstuvwxyz" * 3)[:max(1, min(70, target - 2))] + "\r\n"
        body.append(line)
        target -= len(line)
        row += 1
    return (head + "".join(body)).encode("ascii")


def store_state(store: Path, pre: dict | None = None) -> dict:
    def names(d):
        try:
            return sorted(os.listdir(store / d))
        except FileNotFoundError:
            return None
    frontier = store / "allocation-frontier.json"
    state = {"transactions": names("transactions"), "staging": names("staging"),
             "frontier": frontier.read_text("ascii", "replace") if frontier.is_file() else None}
    if pre is not None:
        new = sorted(set(state["transactions"] or []) - set(pre["transactions"] or []))
        state["new_transactions"] = {n: sha((store / "transactions" / n).read_bytes())
                                     for n in new}
        state["lost_transactions"] = sorted(set(pre["transactions"] or []) -
                                            set(state["transactions"] or []))
    return state


def number_map(port: int) -> dict:
    """GROUP then HDR Message-ID over the group's range: {number: msgid}."""
    out = {"map": {}}
    try:
        wire = Wire(port)
        out["greeting"] = text(wire.readline(30))
        wire.send("GROUP {}\r\n".format(GROUP).encode())
        group = wire.readline(30)
        out["group"] = text(group)
        words = (group or b"").split()
        if group and group.startswith(b"211") and int(words[1]) > 0:
            wire.send("HDR Message-ID {}-{}\r\n".format(int(words[2]), int(words[3])).encode())
            status = wire.readline(30)
            out["hdr"] = text(status)
            if status and status.startswith(b"225"):
                while True:
                    line = wire.readline(30)
                    if line in (b".\r\n", b"", None):
                        break
                    number, _, msgid = line.strip().decode("latin-1").partition(" ")
                    out["map"][number] = msgid
        wire.send(b"QUIT\r\n")
    except OSError as error:
        out["error"] = "{}: {}".format(type(error).__name__, error)
    return out


def owner_log(node: Node, owner: dict) -> list[str]:
    path = node.dir / Path(owner["log"].name).name
    try:
        return path.read_text("utf-8", "replace").splitlines()
    except FileNotFoundError:
        return []


def pid_gone(pid: int, core: str) -> bool:
    try:
        cmdline = Path("/proc/{}/cmdline".format(pid)).read_bytes()
    except FileNotFoundError:
        return True
    return core.encode() not in cmdline


# ---------------------------------------------------------------------------
# The campaign.

class Campaign:
    def __init__(self, image: Path, work: Path, seed: int, rotate_at=ROTATE_AT):
        self.image, self.work, self.seed, self.rotate_at = image, work, seed, rotate_at
        self.rng = random.Random(seed)
        self.seq = 0
        self.ledger: dict[str, dict] = {}
        self.owner = None
        self.result = {"image": str(image), "seed": seed, "stores": [],
                       "iterations": [], "calibration": []}
        self.node = None
        self.open_store()

    def open_store(self):
        index = len(self.result["stores"])
        self.node = Node(self.image, self.work, "node{}".format(index))
        self.payloads = self.node.dir / "payloads"
        self.payloads.mkdir()
        self.all_nodes = getattr(self, "all_nodes", []) + [self.node]
        entry = {"index": index, "port": self.node.port, "store": str(self.node.store)}
        self.result["stores"].append(entry)
        entry["init"] = public(self.node.operator("init", GROUP))
        entry["first_owner"] = self.start_owner()

    # POST bookkeeping -----------------------------------------------------
    def new_post(self, size_class: str) -> tuple[str, Path]:
        msgid = "<pk-{}-{:04d}@production-kill.invalid>".format(self.seed, self.seq)
        payload = make_article(msgid, size_class, self.seq)
        path = self.payloads / "{:04d}.art".format(self.seq)
        path.write_bytes(payload)
        self.ledger[msgid] = {"seq": self.seq, "size_class": size_class,
                              "store": len(self.result["stores"]) - 1,
                              "octets": len(payload), "payload_sha256": sha(payload),
                              "path": str(path), "events": []}
        self.seq += 1
        return msgid, path

    def start_owner(self) -> dict:
        owner = self.node.start_owner()
        self.owner = owner
        return {"pid": owner["pid"], "ready": owner["ready"], "lines": owner["lines"][:4]}

    def kill_owner(self) -> dict:
        t_kill = time.perf_counter()
        wall = time.time()
        os.kill(self.owner["pid"], signal.SIGKILL)
        return {"t_kill": t_kill, "wall": wall}

    # Observations ---------------------------------------------------------
    def reread(self, msgid: str) -> dict:
        got = self.node.nntp_article(msgid)
        payload = Path(self.ledger[msgid]["path"]).read_bytes()
        return {"status": got["status"], "sha256": sha(got["octets"]) if got["octets"] else None,
                "octets": len(got["octets"]),
                "identical": injected_from(got["octets"], payload) if got["octets"] else None}

    def resubmit(self, msgid: str) -> dict:
        before = store_state(self.node.store)
        rec = post_once(self.node.port, Path(self.ledger[msgid]["path"]))
        after = store_state(self.node.store, before)
        rec["new_transactions"] = len(after["new_transactions"])
        return rec

    def settle(self, msgid: str, post: dict, iteration: int) -> dict:
        """After the restart: ARTICLE, and a resubmission for a death without reply."""
        obs = {"msgid": msgid, "iteration": iteration, "post": post,
               "reread": self.reread(msgid)}
        if post.get("code") in (UNCERTAIN, UNEXPECTED):
            obs["resubmit"] = self.resubmit(msgid)
            obs["reread_after_resubmit"] = self.reread(msgid)
        self.ledger[msgid]["events"].append(obs)
        return obs

    def stream_post(self, size_class: str) -> tuple[str, dict]:
        msgid, path = self.new_post(size_class)
        return msgid, post_once(self.node.port, path)

    # Calibration ----------------------------------------------------------
    def calibrate(self, rounds=3):
        """Unkilled POSTs per size class, polling the store to time phases."""
        for _ in range(rounds):
            for size_class in (*NORMAL, "over"):
                msgid, path = self.new_post(size_class)
                pre = store_state(self.node.store)
                proc = spawn_client(self.node.port, path)
                sent = wait_line(proc, b"SENT ")
                t0 = float(sent.split()[1]) if sent else time.perf_counter()
                seen = {}
                while proc.poll() is None:
                    now = time.perf_counter()
                    st = store_state(self.node.store)
                    kinds = {n.split("-")[0] + "-" for n in st["staging"] or []}
                    for kind in kinds:
                        seen.setdefault(kind + "seen", (now - t0) * 1000)
                    for key in [k for k in seen if k.endswith("-seen")]:
                        if key[:-4] not in kinds:
                            seen.setdefault(key[:-4] + "gone", (now - t0) * 1000)
                    if st["staging"] and "stage" not in seen:
                        seen["stage"] = (now - t0) * 1000
                    if st["frontier"] != pre["frontier"] and "frontier" not in seen:
                        seen["frontier"] = (now - t0) * 1000
                    if len(st["transactions"]) > len(pre["transactions"]) and "txn" not in seen:
                        seen["txn"] = (now - t0) * 1000
                    if "stage" in seen and not st["staging"] and "stage_cleared" not in seen:
                        seen["stage_cleared"] = (now - t0) * 1000
                rec = reap_client(proc)
                if "t_reply" in rec and "t_sent" in rec:
                    seen["reply"] = (rec["t_reply"] - rec["t_sent"]) * 1000
                self.result["calibration"].append(
                    {"msgid": msgid, "size_class": size_class, "code": rec.get("code"),
                     "reply": rec.get("reply"), "phases_ms": seen})
                self.ledger[msgid]["events"].append(
                    {"msgid": msgid, "iteration": "calibration", "post": rec,
                     "reread": self.reread(msgid)})

    def medians(self) -> dict:
        out = {}
        for size_class in (*NORMAL, "over"):
            rows = [c["phases_ms"] for c in self.result["calibration"]
                    if c["size_class"] == size_class]
            med = {}
            for key in sorted({k for r in rows for k in r}):
                vals = [r[key] for r in rows if key in r]
                if vals:
                    med[key] = statistics.median(vals)
            out[size_class] = med
        return out

    # Schedule -------------------------------------------------------------
    def schedule(self, kills: int, concurrent: int) -> list[dict]:
        med = self.medians()
        rng = self.rng

        def band_delay(size_class, band):
            m = med[size_class]
            reply = m.get("reply", 100.0)
            txn = m.get("txn", reply * 0.7)
            if band == "early":
                return rng.uniform(0.0, 0.9 * txn)
            if band == "window":
                return rng.uniform(0.9 * txn, reply + 3.0)
            return rng.uniform(reply + 3.0, 1.4 * reply + 5.0)

        items = []
        mid = 8
        over = 6
        rest = kills - mid - over
        window = rest // 2
        early = (rest - window) * 3 // 5
        late = rest - window - early
        for band, count in (("early", early), ("window", window), ("late", late)):
            for _ in range(count):
                size_class = rng.choice(NORMAL)
                items.append({"kind": "single", "mode": "after-terminator", "band": band,
                              "sizes": [size_class],
                              "delay_ms": band_delay(size_class, band)})
        for _ in range(mid):
            size_class = rng.choice(NORMAL)
            items.append({"kind": "single", "mode": "mid-article", "band": "mid-article",
                          "sizes": [size_class], "fraction": rng.uniform(0.1, 0.95),
                          "delay_ms": rng.uniform(0.0, 20.0)})
        for i in range(over):
            if i < 3:
                items.append({"kind": "single", "mode": "mid-article", "band": "over-limit",
                              "sizes": ["over"], "fraction": rng.uniform(0.5, 1.0),
                              "delay_ms": rng.uniform(0.0, 30.0)})
            else:
                items.append({"kind": "single", "mode": "after-terminator", "band": "over-limit",
                              "sizes": ["over"], "delay_ms": rng.uniform(0.0, 40.0)})
        cbands = ["window"] * (concurrent - concurrent // 4 * 2) + \
            ["early"] * (concurrent // 4) + ["late"] * (concurrent // 4)
        for band in cbands:
            sizes = [rng.choice(NORMAL), rng.choice(NORMAL)]
            slow = max(sizes, key=lambda s: med[s].get("reply", 0))
            items.append({"kind": "concurrent", "mode": "after-terminator", "band": band,
                          "sizes": sizes, "delay_ms": band_delay(slow, band)})
        rng.shuffle(items)
        for item in items:
            item["stream"] = [rng.choice((*NORMAL, *NORMAL, "over")) if rng.random() < 0.9
                              else "over" for _ in range(rng.choice((0, 1, 1, 2)))]
        return items

    # One iteration ----------------------------------------------------------
    def iterate(self, index: int, item: dict) -> dict:
        if len(store_state(self.node.store)["transactions"]) >= self.rotate_at:
            self.close_store()
            self.open_store()
        it = {"index": index, "item": item, "stream": [],
              "store": len(self.result["stores"]) - 1}
        for size_class in item["stream"]:
            msgid, rec = self.stream_post(size_class)
            it["stream"].append({"msgid": msgid, "post": rec})
        it["map_before"] = number_map(self.node.port)
        pre = store_state(self.node.store)
        it["pre"] = pre
        victims = [self.new_post(s) for s in item["sizes"]]
        it["victims"] = [m for m, _ in victims]
        owner_pid = self.owner["pid"]
        it["owner_pid"] = owner_pid
        procs = []
        if item["kind"] == "single":
            msgid, path = victims[0]
            stop_after = None
            if item["mode"] == "mid-article":
                stop_after = int(len(path.read_bytes()) * item["fraction"])
            procs.append(spawn_client(self.node.port, path, stop_after=stop_after))
            sent = wait_line(procs[0], b"SENT ")
            t0 = float(sent.split()[1]) if sent else time.perf_counter()
        else:
            for _, path in victims:
                procs.append(spawn_client(self.node.port, path, hold=True))
            ready = [wait_line(p, b"READY") is not None for p in procs]
            it["held_ready"] = ready
            for p in procs:
                try:
                    p.stdin.write(b"\n")
                    p.stdin.flush()
                except OSError:
                    pass
            sents = [wait_line(p, b"SENT ") for p in procs]
            times = [float(s.split()[1]) for s in sents if s]
            t0 = max(times) if times else time.perf_counter()
            it["terminator_spread_ms"] = ((max(times) - min(times)) * 1000
                                          if len(times) == 2 else None)
        deadline = t0 + item["delay_ms"] / 1000.0
        while True:
            left = deadline - time.perf_counter()
            if left <= 0:
                break
            if left > 0.002:
                time.sleep(left - 0.0015)
        kill = self.kill_owner()
        kill["after_t0_ms"] = (kill["t_kill"] - t0) * 1000
        it["kill"] = kill
        posts = [reap_client(p) for p in procs]
        for post in posts:
            if "t_reply" in post:
                post["reply_ms"] = (post["t_reply"] - post.get("t_sent", t0)) * 1000
                post["reply_before_kill"] = post["t_reply"] < kill["t_kill"]
        it["posts"] = posts
        it["owner"] = self.node.stop_owner(self.owner, signal.SIGKILL)
        it["owner_log_tail"] = owner_log(self.node, self.owner)[-8:]
        it["death"] = store_state(self.node.store, pre)
        it["inspect_before_restart"] = {}
        for msgid in it["victims"]:
            got = self.node.inspect(msgid)
            payload = Path(self.ledger[msgid]["path"]).read_bytes()
            it["inspect_before_restart"][msgid] = {
                "rc": got["rc"], "sha256": sha(got["_out"]) if got["_out"] else None,
                "identical": injected_from(got["_out"], payload) if got["_out"] else None,
                "stderr": got["stderr"][-300:]}
        it["after_inspect"] = store_state(self.node.store)
        it["restart"] = self.start_owner()
        if not it["restart"]["ready"]:
            return it
        it["settled"] = [self.settle(msgid, post, index)
                         for msgid, post in zip(it["victims"], posts)]
        it["stream_settled"] = [self.settle(s["msgid"], s["post"], index)
                                for s in it["stream"]]
        it["map_after"] = number_map(self.node.port)
        return it

    def run(self, kills: int, concurrent: int, out: Path):
        self.result["image_sha256"] = {
            p.name: sha(p.read_bytes()) for p in (self.image, self.image.with_suffix(".core"))}
        self.calibrate()
        self.result["medians_ms"] = self.medians()
        items = self.schedule(kills, concurrent)
        self.result["schedule"] = items
        started = time.monotonic()
        for index, item in enumerate(items):
            print("iteration", index, item["kind"], item["band"],
                  round(item["delay_ms"], 2), flush=True)
            it = self.iterate(index, item)
            self.result["iterations"].append(it)
            if not it["restart"]["ready"]:
                print("owner did not restart; stopping", flush=True)
                break
            if index % 10 == 9:
                self.dump(out)
        self.result["seconds"] = round(time.monotonic() - started, 1)
        self.close_store()
        self.result["pids"] = [
            {"pid": o["pid"], "rc": o.get("rc"), "stopped_by": o.get("stopped_by"),
             "gone": pid_gone(o["pid"], str(self.image.with_suffix(".core")))}
            for node in self.all_nodes for o in node.owners]
        self.dump(out)

    def close_store(self):
        """Every article of this store by ARTICLE, then by `inspect` with the owner stopped."""
        index = len(self.result["stores"]) - 1
        mine = {m: e for m, e in self.ledger.items() if e["store"] == index}
        final = self.result["stores"][index]["final"] = {}
        final["map"] = number_map(self.node.port)
        final["article"] = {m: self.reread(m) for m in mine}
        final["owner"] = self.node.stop_owner(self.owner)
        final["inspect"] = {}
        for msgid, entry in mine.items():
            got = self.node.inspect(msgid)
            payload = Path(entry["path"]).read_bytes()
            final["inspect"][msgid] = {
                "rc": got["rc"], "sha256": sha(got["_out"]) if got["_out"] else None,
                "identical": injected_from(got["_out"], payload) if got["_out"] else None}
        self.node.reap()

    def dump(self, out: Path):
        self.result["ledger"] = self.ledger
        out.write_text(json.dumps(self.result, indent=1, default=str))


# ---------------------------------------------------------------------------
# The judge: every verdict from the record.

def load(path):
    return json.load(gzip.open(path) if str(path).endswith(".gz") else open(path))


def store_phase(pre: dict, death: dict) -> str:
    staging = death.get("staging") or []
    kinds = sorted({n.split("-")[0] + "-" if "-" in n else n for n in staging})
    new = len(death.get("new_transactions") or {})
    tag = "+".join(kinds) if kinds else "no-stage"
    if new:
        return "linked({}),{}".format(new, tag)
    if kinds:
        return "staged,{}".format(tag)
    if death.get("frontier") != pre.get("frontier"):
        return "frontier-advanced"
    return "untouched"


def log_phase(lines: list[str], victims: list[str]) -> str:
    marks = []
    for msgid in victims:
        hit = [l for l in lines if "message-id={}".format(msgid) in l]
        marks.append(hit[-1].split(" path=")[0] + " logged" if hit else "not logged")
    return "; ".join(marks)


def verdict(obs: dict, size_class: str = "") -> str:
    code = obs["post"].get("code")
    rr = obs["reread"]
    present = rr["status"].startswith("220")
    absent = rr["status"].startswith("430")
    if code == ACCEPTED:
        if present and rr["identical"]:
            return "240-identical"
        return "lost-240" if absent else "torn"
    if code == REFUSED:
        return "refused" if absent else "refused-but-present"
    if code in (UNCERTAIN, UNEXPECTED):
        sub = obs.get("resubmit", {})
        after = obs.get("reread_after_resubmit", {})
        if present and not rr["identical"]:
            return "torn"
        if present:
            ok = sub.get("code") != ACCEPTED and sub.get("new_transactions") == 0
            return "died-present-identical" if ok else "died-present-resubmit-accepted"
        if absent and size_class == "over":
            # Over fn-own-body-limit: the resubmission must be refused as
            # not received, and nothing may be stored.
            ok = sub.get("code") == REFUSED and sub.get("new_transactions") == 0
            return "died-absent" if ok else "died-absent-resubmit-failed"
        if absent:
            ok = (sub.get("code") == ACCEPTED and after.get("identical")
                  and sub.get("new_transactions") == 1)
            return "died-absent" if ok else "died-absent-resubmit-failed"
        return "reread-failed"
    return "unexpected-code"


def judge(paths: list[str]) -> int:
    failures_total = 0
    for path in paths:
        rec = load(path)
        failures = []
        counts: dict[str, int] = {}
        rows = []
        bands: dict[tuple, int] = {}
        phases: dict[tuple, list] = {}
        victim_counts: dict[tuple, int] = {}
        exit_codes: dict[str, set] = {}
        num_to_id: dict[str, str] = {}
        id_to_num: dict[str, str] = {}
        accepted: set[str] = set()

        def check_map(m, where):
            for n, msgid in m.get("map", {}).items():
                if n in num_to_id and num_to_id[n] != msgid:
                    failures.append("reused-number {} at {}: was {} now {}".format(
                        n, where, num_to_id[n], msgid))
                    counts["reused-number"] = counts.get("reused-number", 0) + 1
                if msgid in id_to_num and id_to_num[msgid] != n:
                    failures.append("renumbered {} at {}: {} -> {}".format(
                        msgid, where, id_to_num[msgid], n))
                num_to_id[n], id_to_num[msgid] = msgid, n
            present = set(m.get("map", {}).values())
            for n, msgid in num_to_id.items():
                if msgid not in present:
                    failures.append("number {} ({}) vanished at {}".format(n, msgid, where))
            for msgid in accepted:
                if msgid not in present:
                    failures.append("lost-240 {} absent from the map at {}".format(msgid, where))
                    counts["lost-240"] = counts.get("lost-240", 0) + 1

        def finals(store_index):
            final = rec["stores"][store_index].get("final", {})
            where = "store {} close".format(store_index)
            check_map(final.get("map", {}), where)
            for msgid, art in final.get("article", {}).items():
                ins = final["inspect"][msgid]
                present = art["status"].startswith("220")
                if msgid in accepted and not (present and art["identical"] and ins["identical"]
                                              and ins["sha256"] == art["sha256"]):
                    failures.append("{}: accepted {} ARTICLE {} identical {} inspect rc {} "
                                    "identical {}".format(where, msgid, art["status"],
                                                          art["identical"], ins["rc"],
                                                          ins["identical"]))
                    counts["lost-240"] = counts.get("lost-240", 0) + 1
                if present and not art["identical"]:
                    failures.append("{}: torn {}".format(where, msgid))
                    counts["torn"] = counts.get("torn", 0) + 1
                if (ins["rc"] == 0) != present:
                    failures.append("{}: readers disagree on {}".format(where, msgid))
                if present and ins["sha256"] != art["sha256"]:
                    failures.append("{}: ARTICLE and inspect differ on {}".format(where, msgid))
            finals_done.append(store_index)

        finals_done: list[int] = []

        def note_code(post):
            exit_codes.setdefault(str(post.get("rc")), set()).add(
                (post.get("reply") or "<no reply>").strip()[:60])
            if post.get("rc") != post.get("code"):
                failures.append("client rc {} != classified {} for reply {!r}".format(
                    post.get("rc"), post.get("code"), post.get("reply")))

        current = {"store": 0}

        def switch(store):
            if store != current["store"]:
                num_to_id.clear()
                id_to_num.clear()
                accepted.clear()
                current["store"] = store

        for c in rec["calibration"]:
            obs = rec["ledger"][c["msgid"]]["events"][0]
            note_code(obs["post"])
            v = verdict(obs, c["size_class"])
            counts[v] = counts.get(v, 0) + 1
            if v == "240-identical":
                accepted.add(c["msgid"])
            elif v != "refused":
                failures.append("calibration {} {}".format(c["msgid"], v))
        for it in rec["iterations"]:
            where = "iteration {}".format(it["index"])
            if it.get("store", 0) != current["store"]:
                finals(current["store"])
                switch(it.get("store", 0))
            check_map(it.get("map_before", {}), where + " before kill")
            if not it["restart"]["ready"]:
                failures.append("{}: owner did not restart: {}".format(where, it["restart"]))
                continue
            for obs in it.get("stream_settled", []):
                note_code(obs["post"])
                if obs["post"].get("code") == ACCEPTED:
                    accepted.add(obs["msgid"])
            verdicts = []
            for obs in it.get("settled", []) + it.get("stream_settled", []):
                v = verdict(obs, rec["ledger"][obs["msgid"]]["size_class"])
                counts[v] = counts.get(v, 0) + 1
                note_code(obs["post"])
                if "resubmit" in obs:
                    note_code(obs["resubmit"])
                if v == "240-identical":
                    accepted.add(obs["msgid"])
                if obs.get("resubmit", {}).get("code") == ACCEPTED:
                    accepted.add(obs["msgid"])
                if v not in ("240-identical", "died-absent", "died-present-identical",
                             "refused"):
                    failures.append("{} {}: {}; post reply {!r}; reread {}; resubmit {}".format(
                        where, obs["msgid"], v, obs["post"].get("reply"), obs["reread"],
                        {k: obs.get("resubmit", {}).get(k) for k in ("rc", "reply",
                                                                   "new_transactions")}))
                if obs in it.get("settled", []):
                    verdicts.append(v)
                    key = (it["item"]["kind"], v)
                    victim_counts[key] = victim_counts.get(key, 0) + 1
                    ins = it["inspect_before_restart"].get(obs["msgid"], {})
                    present = obs["reread"]["status"].startswith("220")
                    if (ins.get("rc") == 0) != present or (
                            present and ins.get("sha256") != obs["reread"]["sha256"]):
                        failures.append("{} {}: inspect before restart rc {} sha {} vs "
                                        "ARTICLE {} sha {}".format(
                                            where, obs["msgid"], ins.get("rc"), ins.get("sha256"),
                                            obs["reread"]["status"], obs["reread"]["sha256"]))
            if it["death"].get("lost_transactions"):
                failures.append("{}: transactions lost at death {}".format(
                    where, it["death"]["lost_transactions"]))
            if it["after_inspect"]["transactions"] != it["death"]["transactions"] or \
                    it["after_inspect"]["staging"] != it["death"]["staging"]:
                failures.append("{}: inspect changed the store".format(where))
            check_map(it.get("map_after", {}), where + " after restart")
            sp = store_phase(it["pre"], it["death"])
            lp = log_phase(it.get("owner_log_tail", []), it["victims"])
            bands[(it["item"]["band"], sp)] = bands.get((it["item"]["band"], sp), 0) + 1
            phases.setdefault((sp, lp), []).append(it["kill"]["after_t0_ms"])
            rows.append("| {} | {} | {} | {} | {} | {:.1f} | {:.1f} | {} | {} | {} | {} |".format(
                it["index"], it.get("store", 0), it["item"]["kind"], it["item"]["band"],
                ",".join(it["item"]["sizes"]), it["item"]["delay_ms"],
                it["kill"]["after_t0_ms"],
                " / ".join("{} ({})".format((p.get("reply") or "none").strip()[:28], p.get("rc"))
                           for p in it["posts"]),
                sp, lp, ", ".join(verdicts)))
        finals(current["store"])
        final = {"map": {"map": {}}}
        for store in rec["stores"]:
            final["map"]["map"].update(store.get("final", {}).get("map", {}).get("map", {}))
        final["pids"] = rec.get("pids", [])
        for p in final.get("pids", []):
            if not p["gone"]:
                failures.append("pid {} not confirmed gone".format(p["pid"]))
        overlap = [(a, b) for a in exit_codes for b in exit_codes
                   if a < b and exit_codes[a] & exit_codes[b]]
        if overlap:
            failures.append("exit codes overlap on a reply: {}".format(overlap))
        kills = rec["iterations"]
        print("# {}\n".format(path))
        print("stores {} (closed and swept: {})\n".format(len(rec["stores"]), finals_done))
        print("seed {}; {} iterations ({} single, {} concurrent); {} POSTs in the ledger; "
              "{} final articles present; {} owner pids, all gone: {}\n".format(
                  rec["seed"], len(kills),
                  sum(1 for k in kills if k["item"]["kind"] == "single"),
                  sum(1 for k in kills if k["item"]["kind"] == "concurrent"),
                  len(rec["ledger"]),
                  sum(len(st.get("final", {}).get("map", {}).get("map", {}))
                      for st in rec["stores"]),
                  len(final.get("pids", [])), all(p["gone"] for p in final.get("pids", []))))
        print("calibration medians (ms from terminator sent): {}\n".format(
            json.dumps({k: {kk: round(vv, 1) for kk, vv in v.items()}
                        for k, v in rec["medians_ms"].items()})))
        print("## Verdicts\n")
        for key in ("240-identical", "died-absent", "died-present-identical", "refused",
                    "torn", "lost-240", "reused-number"):
            print("- {}: {}".format(key, counts.pop(key, 0)))
        for key, value in sorted(counts.items()):
            print("- {}: {}".format(key, value))
        print("\n## Verdicts of the killed POSTs only\n")
        print("| kill kind | verdict | POSTs |\n|---|---|---|")
        for (kind, v), n in sorted(victim_counts.items()):
            print("| {} | {} | {} |".format(kind, v, n))
        print("\n## Client exit codes by reply\n")
        for code, replies in sorted(exit_codes.items()):
            print("- rc {}: {}".format(code, sorted(replies)))
        print("\n## Kill band against the store state at death\n")
        print("| band | store state at death | kills |\n|---|---|---|")
        for (band, sp), n in sorted(bands.items()):
            print("| {} | {} | {} |".format(band, sp, n))
        print("\n## Kill instants against the phase reached\n")
        print("| store state at death | owner log at death | kills | killed at ms (min to max) |")
        print("|---|---|---|---|")
        for (sp, lp), ms in sorted(phases.items(), key=lambda kv: min(kv[1])):
            print("| {} | {} | {} | {:.1f} to {:.1f} |".format(sp, lp, len(ms), min(ms), max(ms)))
        print("\n## Per kill\n")
        print("| # | store | kind | band | sizes | scheduled ms | killed at ms | replies (rc) | "
              "store at death | owner log at death | verdict |")
        print("|---|---|---|---|---|---|---|---|---|---|---|")
        for row in rows:
            print(row)
        print("\n## Failures: {}\n".format(len(failures)))
        for f in failures:
            print("- " + f)
        print()
        failures_total += len(failures)
    return 1 if failures_total else 0


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = parser.add_subparsers(dest="verb", required=True)
    c = sub.add_parser("client")
    c.add_argument("--port", type=int, required=True)
    c.add_argument("--payload", type=Path, required=True)
    c.add_argument("--stop-after", type=int)
    c.add_argument("--hold", action="store_true")
    r = sub.add_parser("run")
    r.add_argument("--image", type=Path, required=True)
    r.add_argument("--work", type=Path, required=True)
    r.add_argument("--out", type=Path, required=True)
    r.add_argument("--seed", type=int, default=1)
    r.add_argument("--kills", type=int, default=80)
    r.add_argument("--concurrent", type=int, default=12)
    r.add_argument("--rotate-at", type=int, default=ROTATE_AT)
    j = sub.add_parser("judge")
    j.add_argument("records", nargs="+")
    args = parser.parse_args(argv)
    if args.verb == "client":
        return client(args.port, args.payload.read_bytes(), args.stop_after, args.hold)
    if args.verb == "judge":
        return judge(args.records)
    args.work, args.image = args.work.resolve(), args.image.resolve()
    if args.work.exists():
        shutil.rmtree(args.work)
    args.work.mkdir(parents=True)
    campaign = Campaign(args.image, args.work, args.seed, args.rotate_at)
    try:
        campaign.run(args.kills, args.concurrent, args.out)
    finally:
        for node in campaign.all_nodes:
            node.reap()
        campaign.dump(args.out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
