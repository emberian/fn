#!/usr/bin/env python3
"""The mission demo: one signed article from A to D and its receipt back,
then a cancel, across NNTP, a BP link and an optional partition.

    python3 tools/mission_lab.py demo [--partition SECONDS] [--settle S] [--no-cancel]

Steps (each prints its wire lines, the new log lines and their SHA-256):

    1  A: the enrolled author signs and injects an article (hybrid-author)
    2  B: the article arrives over the A-B streaming feed; B's verdict
    3  B: the article is bridged into B's BP store and requested toward C
       (`bp-obligation request` to relay r1); with --partition the link is
       down first, so r1 holds the bundle
    4  the link comes up; r1 forwards to r2; C's node delivers the request
    5  C: the article is bridged into C's NNTP store; the C-D feed carries it
       to D; verdicts on C and D
    6  C's application receipt travels r2 -> r1 -> B and releases B's
       obligation; A's own NNTP obligation was released at step 2
    7  a cancel (Control: cancel) posted on A is filed on every node (C1);
       the article stays readable (C3 is not implemented)
    8  latencies and the SHA-256 of every log

;; SPIKE: defers K6.  Steps 3 and 5 move the article between a node's NNTP
;; store and its BP store host-side (`store post` / `store inspect` /
;; `operator post`), because the two stores have two owners.
;; SPIKE: defers the receipt's return past B.  NNTP has no application
;; receipt; A's obligation to B is discharged by B's streaming reply.
"""
from __future__ import annotations

import argparse
import email.utils
import json
import secrets
import subprocess
import time
from pathlib import Path

from mission_lab import (BP_CRC, BP_HOPS, BP_LIFETIME, BP_MRU, BP_WALL_ERROR, HUMAN, NODES,
                         RELAYS, Lab, LabError, dtn_wall_ms, sha256, utc)


class Demo:
    def __init__(self, lab: Lab, args):
        self.lab, self.args = lab, args
        self.tag = args.tag or time.strftime("%Y%m%dT%H%M%SZ", time.gmtime()) + "-" + secrets.token_hex(2)
        self.dir = lab.root / "demo" / self.tag
        self.dir.mkdir(parents=True, exist_ok=True)
        self.record = dict(tag=self.tag, started=utc(), partition=args.partition, steps=[],
                           latencies={}, findings=[], images=str(lab.images))
        self.marks = {}
        self.t = {}
        self.logs = self.log_paths()

    # -- reporting -------------------------------------------------------------
    def log_paths(self):
        paths = {}
        for name, node in self.lab.state["nodes"].items():
            paths[f"{name}.fn.log"] = Path(node["log"])
            paths[f"{name}.owner.stdout"] = Path(node["dir"]) / "owner.stdout"
            if "bp" in node:
                paths[f"{name}.bp.serve.log"] = Path(node["bp"]["dir"]) / "serve.log"
        for relay in RELAYS:
            paths[f"relay.{relay}.log"] = self.lab.root / "relays" / f"{relay}.log"
        paths["link.log"] = Path(self.lab.state["link"]["log"])
        return paths

    def mark(self):
        for key, path in self.logs.items():
            self.marks[key] = len(path.read_bytes()) if path.exists() else 0

    def new_lines(self, keys=None, keep=None):
        out = {}
        for key, path in self.logs.items():
            if keys and key not in keys:
                continue
            if not path.exists():
                continue
            data = path.read_bytes()
            fresh = data[self.marks.get(key, 0):].decode("utf-8", "replace").splitlines()
            if keep:
                fresh = [l for l in fresh if keep(key, l)]
            if fresh:
                out[key] = fresh
        return out

    def say(self, text=""):
        print(text, flush=True)

    def step(self, number, title, wire=None, lines=None, **extra):
        entry = dict(step=number, title=title, at=utc(), wire=wire or [],
                     lines={k: [dict(sha256=sha256(l.encode())[:16], line=l) for l in v]
                            for k, v in (lines or {}).items()}, **extra)
        self.record["steps"].append(entry)
        self.say(f"\n== step {number}: {title}  [{entry['at']}]")
        for line in wire or []:
            self.say(f"   {line}")
        for key, items in entry["lines"].items():
            for item in items:
                self.say(f"   {key:18} {item['sha256']}  {item['line']}")
        for key, value in extra.items():
            self.say(f"   {key}: {json.dumps(value) if not isinstance(value, str) else value}")
        self.save()
        return entry

    def finding(self, what, line=None, where=None):
        self.record["findings"].append(dict(at=utc(), what=what, line=line, where=where))
        self.say(f"   FINDING: {what}" + (f"  [{where}] {line}" if line else ""))

    def save(self):
        (self.dir / "demo.json").write_text(json.dumps(self.record, indent=1))

    # -- NNTP helpers -----------------------------------------------------------
    def article_on(self, name, message_id, timeout, wire=None):
        """Poll ARTICLE on NAME until 220; return (status, lines)."""
        deadline = time.monotonic() + timeout
        last = None
        while True:
            trace = []
            session = self.lab.session(name, wire=trace)
            try:
                status, body = session.cmd(f"ARTICLE {message_id}", multiline=True)
            finally:
                session.close()
            last = status
            if status.startswith("220"):
                if wire is not None:
                    wire.extend(trace + [f"S: {status}", f"   ... {len(body)} lines"])
                return status, body
            if time.monotonic() > deadline:
                if wire is not None:
                    wire.extend(trace + [f"S: {status}"])
                return status, []
            time.sleep(0.5)

    def verdict_on(self, name, message_id, wire=None):
        session = self.lab.session(name, wire=wire)
        try:
            status, body = session.cmd(f"HDR :fn-verified {message_id}", multiline=True)
            if wire is not None:
                wire.append(f"S: {status}")
                wire.extend(f"   {l}" for l in body)
            return body[0] if body else status
        finally:
            session.close()

    def group_view(self, name, wire=None):
        session = self.lab.session(name, wire=wire)
        try:
            out = {}
            for group in ("fn.mission", "control.cancel"):
                status, _ = session.cmd(f"GROUP {group}")
                out[group] = status
                if wire is not None:
                    wire.append(f"S: {status}")
            return out
        finally:
            session.close()

    def post_on(self, name, article: bytes, wire=None):
        session = self.lab.session(name, wire=wire)
        try:
            status, _ = session.cmd("POST")
            if wire is not None:
                wire.append(f"S: {status}")
            if not status.startswith("340"):
                return status
            for line in article.decode("utf-8").split("\r\n"):
                if line == "" and article.decode("utf-8").endswith("\r\n") and line is None:
                    continue
                session.sock.sendall((("." + line) if line.startswith(".") else line).encode() + b"\r\n")
            session.sock.sendall(b".\r\n")
            status = session.line()
            if wire is not None:
                wire.append(f"C: <{len(article)} octets>")
                wire.append(f"S: {status}")
            return status
        finally:
            session.close()

    @staticmethod
    def octets_of(lines):
        return ("\r\n".join(lines) + "\r\n").encode("utf-8")

    # -- BP helpers --------------------------------------------------------------
    def bridge_to_bp(self, name, message_id, article: bytes, label):
        """Put ARTICLE into NAME's BP store as a new work item and request it
        toward the far node through the relay.  The serving node is stopped
        for the store's writer lock and restarted after the request."""
        lab, node = self.lab, self.lab.state["nodes"][name]
        bp = node["bp"]
        path = Path(bp["dir"]) / f"{label}.article"
        path.write_bytes(article)
        bp["sequence"] += 1
        work = f"work-{label}"
        how = lab.stop(f"bp-{name}")
        records = []
        try:
            for argv in (("store", bp["store"], "post", message_id, path, "-", "-", "fn.mission"),
                         ("app-journal", "workflow-enqueue", bp["store"], bp["workflow"],
                          bp["sequence"], 0, work, message_id, f"forward-{work}", bp["far_eid"],
                          "native-policy", "terms-native"),
                         ("bp-obligation", "undertake", bp["store"], bp["workflow"], work, 3)):
                records.append(lab.fn("dtn-developer", *argv, log=self.dir / "commands.jsonl"))
            wall = dtn_wall_ms()
            request = lab.fn("dtn-developer", "bp-obligation", "request", bp["store"], bp["workflow"],
                             work, work + "-attempt", bp["service"], bp["eid"], "127.0.0.1",
                             bp["contact"], BP_LIFETIME, BP_CRC, BP_HOPS, BP_MRU, wall, BP_WALL_ERROR,
                             check=False, timeout=180, log=self.dir / "commands.jsonl")
            records.append(request)
        finally:
            lab.start_bp_serve(name)
        bp["works"].append(dict(work=work, message_id=message_id, requested=utc(), rc=request["rc"]))
        lab.save()
        lines = [l for r in records for l in (r["stdout"] + r["stderr"]).splitlines() if l.strip()]
        return work, request["rc"], lines, how

    def obligation(self, name, work):
        bp = self.lab.state["nodes"][name]["bp"]
        record = self.lab.fn("dtn-developer", "bp-obligation", "status", bp["store"], bp["workflow"],
                             work, check=False, timeout=60, log=self.dir / "commands.jsonl")
        if record["rc"] != 0:
            # The serving node holds the store; ask again with it stopped.
            self.lab.stop(f"bp-{name}")
            try:
                record = self.lab.fn("dtn-developer", "bp-obligation", "status", bp["store"],
                                     bp["workflow"], work, check=False, timeout=60,
                                     log=self.dir / "commands.jsonl")
            finally:
                self.lab.start_bp_serve(name)
        return (record["stdout"] + record["stderr"]).strip()

    def relay_bundles(self, relay):
        query = self.lab.dtn7 / "target" / "release" / "dtnquery"
        try:
            result = subprocess.run([str(query), "-p", str(RELAYS[relay]["web"]), "bundles"],
                                    capture_output=True, timeout=10, text=True)
            return [l for l in result.stdout.splitlines() if l.strip()]
        except (OSError, subprocess.TimeoutExpired) as error:
            return [f"dtnquery: {type(error).__name__}"]

    def bp_lines(self, key, line):
        if key.startswith("relay."):
            return any(w in line for w in ("Forwarding", "forward", "Received", "received",
                                            "Transmission", "ERROR", "WARN", "delivered", "Sending",
                                            "Storing", "custody", "session"))
        return True

    def deliver_over_bp(self, source, message_id, article, label, partition):
        """Steps 3 and 4 for one article: bridge at SOURCE, partition, deliver at the far node."""
        far = NODES[source]["bp"]["far"]
        far_bp = self.lab.state["nodes"][far]["bp"]
        serve_log = Path(far_bp["dir"]) / "serve.log"
        if partition:
            self.lab.set_link("down")
            self.say(f"   link DOWN for {partition}s")
        self.mark()
        self.t[f"bp_request_{label}"] = time.time()
        work, rc, lines, how = self.bridge_to_bp(source, message_id, article, label)
        at_relay = self.relay_bundles(NODES[source]["bp"]["relay"])
        self.step(3 if label == "article" else "7b",
                  f"{source}: {label} bridged into the BP store and requested toward {far}"
                  + (" while the link is down" if partition else ""),
                  wire=[f"$ {' '.join(map(str, r))}" for r in ()],
                  lines=dict(**{f"{source}.bp.request": lines},
                             **self.new_lines({f"relay.{NODES[source]['bp']['relay']}.log",
                                               f"{source}.bp.serve.log"}, keep=self.bp_lines)),
                  work=work, request_exit=rc, serving_node_stopped=how, link=self.lab.link_state(),
                  relay_bundles=at_relay)
        if rc != 0:
            self.finding(f"bp-obligation request exit {rc} at {source}", lines[-1] if lines else None,
                         f"{source}.bp.request")
        start = len(serve_log.read_bytes()) if serve_log.exists() else 0
        self.mark()
        if partition:
            time.sleep(partition)
            self.lab.set_link("up")
            self.say(f"   link UP at {utc()}")
        self.t[f"link_up_{label}"] = time.time()
        try:
            match = self.lab.wait_for(serve_log, r"BP node delivery (request-\S+)", self.args.settle, start)
            delivery = match.group(1)
            if delivery != "request-accepted":
                source_lines = [l for l in serve_log.read_text("utf-8", "replace")[start:].splitlines()
                                if l.startswith("BP node source")]
                self.finding(f"{far} judged the carried request {delivery}",
                             source_lines[-1] if source_lines else None, f"{far}.bp.serve.log")
        except LabError:
            delivery = None
        self.t[f"delivered_{label}"] = time.time()
        self.step(4 if label == "article" else "7c",
                  f"the link is up; r1 -> r2 -> {far}: {label} delivered as {delivery}",
                  lines=self.new_lines(keep=self.bp_lines),
                  relay_bundles={r: self.relay_bundles(r) for r in RELAYS},
                  seconds_from_request=round(self.t[f"delivered_{label}"] - self.t[f"bp_request_{label}"], 2),
                  seconds_from_link_up=round(self.t[f"delivered_{label}"] - self.t[f"link_up_{label}"], 2))
        if delivery is None:
            self.finding(f"{label} never delivered at {far} within {self.args.settle}s", where=f"{far}.bp.serve.log")
        return delivery

    def bridge_to_nntp(self, name, message_id, label):
        """Read the delivered article out of NAME's BP store and submit it to
        NAME's NNTP owner over the control socket."""
        node = self.lab.state["nodes"][name]
        bp = node["bp"]
        inspect = self.lab.fn("dtn-developer", "store", bp["store"], "inspect", message_id,
                              check=False, timeout=60, log=self.dir / "commands.jsonl")
        if inspect["rc"] != 0:
            self.lab.stop(f"bp-{name}")
            try:
                inspect = self.lab.fn("dtn-developer", "store", bp["store"], "inspect", message_id,
                                      check=False, timeout=60, log=self.dir / "commands.jsonl")
            finally:
                self.lab.start_bp_serve(name)
        if inspect["rc"] != 0:
            return None, inspect
        octets = inspect["stdout"].encode("utf-8")
        path = Path(node["dir"]) / f"{label}.from-bp.article"
        path.write_bytes(octets)
        post = self.lab.fn("developer", "operator", node["config"], "post", "--message-id", message_id,
                           "--payload", path, "--group", "fn.mission", check=False, timeout=60,
                           log=self.dir / "commands.jsonl")
        return octets, post

    # -- the run -------------------------------------------------------------------
    def run(self):
        lab = self.lab
        a = lab.state["nodes"]["A"]
        author = lab.state["author"]
        message_id = f"<mission-{self.tag}@a.mission.invalid>"
        date = email.utils.format_datetime(email.utils.localtime())
        source = (f"From: {HUMAN} <{HUMAN}@a.mission.invalid>\r\nNewsgroups: fn.mission\r\n"
                  f"Subject: mission {self.tag}\r\nMessage-ID: {message_id}\r\nDate: {date}\r\n\r\n"
                  f"A signed article authored on A at {utc()}, bound for B over NNTP, C over BP"
                  f" and D over NNTP.\r\nTag {self.tag}.\r\n").encode("utf-8")
        src = self.dir / "source.article"
        src.write_bytes(source)
        # -- 1 ----------------------------------------------------------------
        self.mark()
        signed = lab.fn("developer", "hybrid-sign", author["principal"], author["ed_public"],
                        author["ed_secret"], author["ml_public"], author["ml_private"], src,
                        log=self.dir / "commands.jsonl")
        values = dict(l.split() for l in signed["stdout"].splitlines() if len(l.split()) == 2)
        (self.dir / "ed.sig").write_bytes(bytes.fromhex(values["ed25519"]))
        (self.dir / "ml.sig").write_bytes(bytes.fromhex(values["ml-dsa-65"]))
        self.t["author"] = time.time()
        if self.args.unsigned:
            wire = []
            status = self.post_on("A", source, wire)
            injected = dict(rc=0 if status.startswith("240") else 1, stdout=status, stderr="")
            wire = ["(unsigned: POST as ember)"] + wire
        else:
            injected = lab.fn("developer", "hybrid-author", a["control"], "1", src, self.dir / "ed.sig",
                              self.dir / "ml.sig", author["ml_public"], check=False, timeout=120,
                              log=self.dir / "commands.jsonl")
            wire = [f"$ hybrid-sign ... -> ed25519 {values['ed25519'][:16]}... ml-dsa-65 {values['ml-dsa-65'][:16]}...",
                    f"$ hybrid-author {a['control']} 1 source.article ed.sig ml.sig -> exit {injected['rc']}",
                    *[f"   {l}" for l in (injected['stdout'] + injected['stderr']).splitlines()]]
        time.sleep(0.5)
        self.step(1, f"A: {'ember posts' if self.args.unsigned else 'the enrolled author signs and injects'} {message_id}",
                  wire=wire, lines=self.new_lines({"A.fn.log", "A.owner.stdout"}),
                  message_id=message_id, source_sha256=sha256(source))
        if injected["rc"] != 0:
            self.finding(f"injection exit {injected['rc']}: {injected['stdout']}", where="A")
            return self.finish()
        # -- 2 ----------------------------------------------------------------
        wire = []
        status, body = self.article_on("B", message_id, self.args.settle, wire)
        self.t["B"] = time.time()
        verdict_b = self.verdict_on("B", message_id, wire) if status.startswith("220") else None
        time.sleep(0.5)
        self.step(2, f"B: {message_id} arrived over the A-B feed; B's verdict",
                  wire=wire, lines=self.new_lines({"A.fn.log", "A.owner.stdout", "B.fn.log", "B.owner.stdout"}),
                  verdict=verdict_b, seconds_from_author=round(self.t["B"] - self.t["author"], 2),
                  a_feed_journal={p.name: dict(octets=p.stat().st_size, sha256=sha256(p))
                                  for p in (Path(a["store"]) / "feed").glob("*") if p.is_file()}
                  if (Path(a["store"]) / "feed").exists() else {})
        if not status.startswith("220"):
            self.finding(f"article did not reach B within {self.args.settle}s: {status}", where="B")
            return self.finish()
        article_b = self.octets_of(body)
        # -- 3, 4 ---------------------------------------------------------------
        delivery = self.deliver_over_bp("B", message_id, article_b, "article", self.args.partition)
        if delivery is None:
            return self.finish()
        # -- 5 ----------------------------------------------------------------
        self.mark()
        octets, post = self.bridge_to_nntp("C", message_id, "article")
        wire = [f"$ store inspect {message_id} -> {len(octets) if octets else 'refused'} octets",
                f"$ operator C post --message-id {message_id} -> exit {post['rc']} {(post['stdout'] + post['stderr']).strip()}"]
        status_c, _ = self.article_on("C", message_id, self.args.settle, wire)
        self.t["C"] = time.time()
        verdict_c = self.verdict_on("C", message_id, wire) if status_c.startswith("220") else None
        status_d, _ = self.article_on("D", message_id, self.args.settle, wire)
        self.t["D"] = time.time()
        verdict_d = self.verdict_on("D", message_id, wire) if status_d.startswith("220") else None
        time.sleep(0.5)
        self.step(5, "C: the article bridged into C's NNTP store; the C-D feed carries it to D",
                  wire=wire, lines=self.new_lines({"C.fn.log", "C.owner.stdout", "D.fn.log", "D.owner.stdout"}),
                  verdict_c=verdict_c, verdict_d=verdict_d,
                  seconds_author_to_D=round(self.t["D"] - self.t["author"], 2),
                  octets_identical_B_C=(octets == article_b) if octets else None)
        if octets and octets != article_b:
            self.finding("the article's octets differ between B's NNTP copy and C's BP store copy",
                         where="C.bp.store")
        if post["rc"] != 0:
            self.finding(f"operator post at C exit {post['rc']}", (post["stdout"] + post["stderr"]).strip(), "C")
        if not status_d.startswith("220"):
            self.finding(f"article did not reach D within {self.args.settle}s: {status_d}", where="D")
        # -- 6 ----------------------------------------------------------------
        self.mark()
        b_serve = Path(lab.state["nodes"]["B"]["bp"]["dir"]) / "serve.log"
        start = len(b_serve.read_bytes())
        c_bp = lab.state["nodes"]["C"]["bp"]
        tick = None
        try:
            lab.wait_for(b_serve, r"BP node delivery (receipt-\S+)", 20, start)
        except LabError:
            # The serving node queued the receipt; a contact tick carries it.
            lab.stop("bp-C")
            try:
                tick = lab.fn("dtn-developer", "bp-contact", "tick", c_bp["service"], c_bp["eid"],
                              c_bp["far_eid"], 0, 60000, BP_LIFETIME, BP_CRC, BP_HOPS, BP_MRU,
                              dtn_wall_ms(), BP_WALL_ERROR, check=False, timeout=180,
                              log=self.dir / "commands.jsonl")
            except Exception as error:  # noqa: BLE001 - recorded, the demo goes on
                tick = dict(rc=-1, stdout="", stderr=f"{type(error).__name__}: {error}")
            finally:
                try:
                    lab.start_bp_serve("C")
                except LabError as error:
                    self.finding(f"C's node did not restart after the tick: {error}", where="C.bp")
        try:
            match = lab.wait_for(b_serve, r"BP node delivery (receipt-\S+)", self.args.settle, start)
            receipt = match.group(1)
        except LabError:
            receipt = None
        self.t["receipt"] = time.time()
        time.sleep(1.0)
        status_b = self.obligation("B", "work-article")
        self.step(6, f"C's receipt carried r2 -> r1 -> B: {receipt}; B's obligation released",
                  wire=([f"$ bp-contact tick {c_bp['service']} -> exit {tick['rc']}"]
                        + [f"   {l}" for l in (tick['stdout'] + tick['stderr']).splitlines()] if tick else
                        ["(B's node received the receipt without a contact tick)"]),
                  lines=self.new_lines(keep=self.bp_lines),
                  b_obligation=status_b,
                  seconds_receipt_from_request=round(self.t["receipt"] - self.t["bp_request_article"], 2),
                  a_release="A's obligation to B: the streaming reply at step 2 (no application receipt over NNTP)")
        if receipt is None:
            self.finding("no receipt reached B", where="B.bp.serve.log")
        elif "pinned=no" not in status_b:
            self.finding("B's obligation not released after the receipt", status_b, "B.bp")
        # -- 7 ----------------------------------------------------------------
        if not self.args.no_cancel:
            self.cancel(message_id)
        return self.finish()

    def cancel(self, message_id):
        lab = self.lab
        cancel_id = f"<cancel-{self.tag}@a.mission.invalid>"
        date = email.utils.format_datetime(email.utils.localtime())
        cancel = (f"From: {HUMAN} <{HUMAN}@a.mission.invalid>\r\nNewsgroups: fn.mission\r\n"
                  f"Subject: cmsg cancel {message_id}\r\nControl: cancel {message_id}\r\n"
                  f"Message-ID: {cancel_id}\r\nDate: {date}\r\n\r\n"
                  f"cancel {message_id} (mission demo {self.tag})\r\n").encode("utf-8")
        self.mark()
        wire = []
        self.t["cancel"] = time.time()
        status = self.post_on("A", cancel, wire)
        status_b, body_b = self.article_on("B", cancel_id, self.args.settle, wire)
        self.step("7a", f"A: cancel {cancel_id} posted by {HUMAN}; filed (C1) and fed to B",
                  wire=wire, lines=self.new_lines({"A.fn.log", "A.owner.stdout", "B.fn.log", "B.owner.stdout"}),
                  post_status=status, groups_a=self.group_view("A"), groups_b=self.group_view("B"))
        if not status.startswith("240"):
            self.finding(f"cancel refused at A: {status}", where="A")
            return
        if not status_b.startswith("220"):
            self.finding(f"cancel not fed to B: {status_b}", where="B")
            return
        delivery = self.deliver_over_bp("B", cancel_id, self.octets_of(body_b), "cancel", 0)
        if delivery is None:
            return
        self.mark()
        octets, post = self.bridge_to_nntp("C", cancel_id, "cancel")
        wire = [f"$ operator C post --message-id {cancel_id} -> exit {post['rc']} {(post['stdout'] + post['stderr']).strip()}"]
        status_c, _ = self.article_on("C", cancel_id, self.args.settle, wire)
        status_d, _ = self.article_on("D", cancel_id, self.args.settle, wire)
        self.t["cancel_D"] = time.time()
        still = {}
        for name in NODES:
            s, _ = self.article_on(name, message_id, 5)
            still[name] = s.split()[0]
        self.step("7d", "the cancel is filed on C and D; is the cancelled article withdrawn anywhere?",
                  wire=wire, lines=self.new_lines({"C.fn.log", "D.fn.log"}),
                  cancel_on=dict(C=status_c.split()[0], D=status_d.split()[0]),
                  original_article_status=still, groups={n: self.group_view(n) for n in NODES},
                  seconds_cancel_to_D=round(self.t["cancel_D"] - self.t["cancel"], 2))
        if all(s == "220" for s in still.values()):
            self.finding("the cancel is filed in control.cancel on every node and withdraws nothing:"
                         " C1 files, C3 (withdrawal record, hidden view) is not implemented",
                         where="all nodes")

    def finish(self):
        t = self.t
        lat = self.record["latencies"]
        if "D" in t:
            lat["author_to_D_seconds"] = round(t["D"] - t["author"], 2)
        if "B" in t:
            lat["author_to_B_seconds"] = round(t["B"] - t["author"], 2)
        if "delivered_article" in t:
            lat["bp_request_to_C_delivery_seconds"] = round(t["delivered_article"] - t["bp_request_article"], 2)
            lat["link_up_to_C_delivery_seconds"] = round(t["delivered_article"] - t["link_up_article"], 2)
        if "receipt" in t:
            lat["receipt_back_to_B_from_request_seconds"] = round(t["receipt"] - t["bp_request_article"], 2)
        if "cancel_D" in t:
            lat["cancel_author_to_D_seconds"] = round(t["cancel_D"] - t["cancel"], 2)
        self.record["log_sha256"] = {k: dict(path=str(p), sha256=sha256(p), octets=p.stat().st_size)
                                     for k, p in self.logs.items() if p.exists()}
        self.record["finished"] = utc()
        self.record["link"] = self.lab.link_state()
        self.save()
        self.say(f"\n== latencies (partition {self.args.partition}s): {json.dumps(lat)}")
        self.say("== findings: " + (json.dumps(self.record["findings"], indent=1) if self.record["findings"] else "none"))
        self.say("== logs:")
        for key, item in self.record["log_sha256"].items():
            self.say(f"   {item['sha256']}  {key} ({item['octets']} octets)")
        self.say(f"== record: {self.dir / 'demo.json'}")
        return 0 if not self.record["findings"] else 1


def main(lab: Lab, argv) -> int:
    parser = argparse.ArgumentParser(prog="mission_lab.py demo", description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--partition", type=float, default=0.0, help="seconds the B-C link is down")
    parser.add_argument("--settle", type=float, default=120.0, help="seconds to wait per hop")
    parser.add_argument("--no-cancel", action="store_true")
    parser.add_argument("--unsigned", action="store_true", help="POST as ember instead of hybrid-author")
    parser.add_argument("--tag")
    args = parser.parse_args(argv)
    if "nodes" not in lab.state:
        print("not provisioned; run `mission_lab.py up`")
        return 1
    return Demo(lab, args).run()
