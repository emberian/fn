#!/usr/bin/env python3
"""spike/control: the two-node control-message lab (design 2026-09-25, C2-C4).

Two saved-image owners peer over loopback, feeding fn.* and control.*.  Both
grant principal P authority over fn.* (`control grant`); principal Q has no
grant.  Each node decides every control article again under its own rows
(the relayed article carries its carrier intact; no field says "executed").

  * an unsigned cancel and Q's signed cancel of an article Q did not write are
    filed and change nothing (HDR :fn-control "declined ...");
  * P's signed cancel of an unsigned article withdraws it on both nodes
    (430 by Message-ID, absent from LISTGROUP) and Q's signed cancel of its
    own article withdraws that one by author;
  * P's signed newgroup (FN-Control-Serial 1) creates the group on both;
    P's rmgroup (serial 2) retires it; a replayed serial-1 newgroup is
    declined stale-serial; Q's newgroup is declined;
  * P's checkgroups yields a report on both, and `control apply-checkgroups`
    applies it on one;
  * after a restart the withdrawal still holds.

Run: FN_RUN_HYBRID_E2E=1 FN_NATIVE_HOST=<launcher> FN_TEST_OPENSSL=<openssl 3.5>
     python3 -m unittest -v tests.test_native_control_exec
Each observation is printed as a `LAB` line.
"""
import os
from pathlib import Path
import socket
import subprocess
import tempfile
import time
import unittest

from tests.native_process import wait_for_announcement, stop_and_diagnostics

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_HOST", ROOT / "build" / "fn-host"))
OPENSSL = os.environ.get("FN_TEST_OPENSSL", "openssl")
GROUPS = ["fn.test", "control.cancel", "control.newgroup", "control.rmgroup",
          "control.checkgroups"]


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]


def lab(*words):
    print("LAB", *words, flush=True)


class Reader:
    def __init__(self, port):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=15)
        self.stream = self.sock.makefile("rwb", buffering=0)
        assert self.stream.readline().startswith(b"200 ")

    def cmd(self, text):
        self.stream.write(text.encode() + b"\r\n")
        return self.stream.readline().decode().rstrip("\r\n")

    def block(self):
        lines = []
        while True:
            line = self.stream.readline().decode().rstrip("\r\n")
            if line == ".":
                return lines
            lines.append(line[1:] if line.startswith("..") else line)

    def post(self, octets):
        status = self.cmd("POST")
        if not status.startswith("340"):
            return status
        self.stream.write(octets + b".\r\n")
        return self.stream.readline().decode().rstrip("\r\n")

    def close(self):
        try:
            self.cmd("QUIT")
        finally:
            self.sock.close()


@unittest.skipUnless(os.environ.get("FN_RUN_HYBRID_E2E") == "1",
                     "set FN_RUN_HYBRID_E2E=1 for the OpenSSL 3.5 saved-image lab")
@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "FN_NATIVE_HOST is required")
class NativeControlExecLab(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-control-exec-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.p = self.root / "p.bin"
        self.q = self.root / "q.bin"
        self.p.write_bytes(bytes([85]) * 32)
        self.q.write_bytes(bytes([86]) * 32)
        self.p_hex, self.q_hex = "55" * 32, "56" * 32
        self.ed_public = self.root / "ed-public.bin"
        self.ed_secret = self.root / "ed-secret.bin"
        self.ed_public.write_bytes(bytes.fromhex(
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ed_secret.write_bytes(bytes.fromhex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
        self.ml = {}
        for who in ("p", "q"):
            private = self.root / (who + "-ml.pem")
            public = self.root / (who + "-ml-public.pem")
            subprocess.run([OPENSSL, "genpkey", "-algorithm", "ML-DSA-65", "-out",
                            str(private)], timeout=60, check=True)
            subprocess.run([OPENSSL, "pkey", "-in", str(private), "-pubout", "-out",
                            str(public)], timeout=60, check=True)
            self.ml[who] = (private, public)
        self.owners = []
        self.addCleanup(self.stop_all)
        self.nodes = {}
        for name, identity in (("a", "a.example.invalid"), ("b", "b.example.invalid")):
            store = self.root / (name + "-store")
            self.ok("store", store, "init", *GROUPS)
            port = free_port()
            config = self.root / (name + ".toml")
            config.write_text(
                '[store]\npath = "{}"\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
                '[control]\npath = "{}"\n'.format(store, port,
                                                   self.root / (name + ".sock")),
                encoding="ascii")
            self.nodes[name] = {"config": config, "port": port, "identity": identity,
                                "control": self.root / (name + ".sock")}
        for me, other in (("a", "b"), ("b", "a")):
            n, o = self.nodes[me], self.nodes[other]
            self.ok("operator", n["config"], "policy", "set", "path-identity", n["identity"])
            self.ok("operator", n["config"], "peer", "add", "other", o["identity"],
                    "127.0.0.1", o["port"], "fn.*,control.*", "fn.*,control.*",
                    "127.0.0.1", "true")
            granted = self.ok("operator", n["config"], "control", "grant", "fn.*",
                              self.p_hex, "cancel", "newgroup", "rmgroup",
                              "checkgroups")
            lab("grant", me, granted.stdout.decode().strip())

    def invoke(self, *args, timeout=180):
        return subprocess.run([str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=timeout, check=False)

    def ok(self, *args):
        result = self.invoke(*args)
        self.assertEqual(result.returncode, 0,
                         (args, result.stderr.decode("utf-8", "replace")))
        return result

    def start(self, name):
        proc = subprocess.Popen([str(IMAGE), "--fn", "operator",
                                 str(self.nodes[name]["config"]), "run"],
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.owners.append(proc)
        wait_for_announcement(proc, b"LISTENING ")
        self.nodes[name]["proc"] = proc
        return proc

    def stop(self, name):
        proc = self.nodes[name].pop("proc")
        self.owners.remove(proc)
        diagnostic = stop_and_diagnostics(proc, timeout=60)
        self.assertEqual(proc.returncode, 0, diagnostic)
        return diagnostic

    def stop_all(self):
        for proc in reversed(self.owners):
            stop_and_diagnostics(proc, timeout=60)
        self.owners = []

    def source(self, stem, extra=b"", newsgroups=b"fn.test", body=b"body\r\n"):
        path = self.root / (stem + ".eml")
        path.write_bytes(
            b"From: someone@example.invalid\r\n"
            b"Date: Fri, 25 Sep 2026 08:00:00 +0000\r\n"
            b"Newsgroups: " + newsgroups + b"\r\nSubject: " + stem.encode() + b"\r\n"
            b"Message-ID: <" + stem.encode() + b"@example.invalid>\r\n" + extra +
            b"\r\n" + body)
        return path

    def author(self, node, who, stem, **kw):
        principal = self.p if who == "p" else self.q
        generation = 1 if who == "p" else 2
        private, public = self.ml[who]
        article = self.source(stem, **kw)
        signed = self.ok("hybrid-sign", principal, self.ed_public, self.ed_secret,
                         public, private, article)
        parts = dict(line.split() for line in signed.stdout.decode().splitlines())
        ed_path, ml_path = self.root / (stem + ".ed"), self.root / (stem + ".ml")
        ed_path.write_bytes(bytes.fromhex(parts["ed25519"]))
        ml_path.write_bytes(bytes.fromhex(parts["ml-dsa-65"]))
        result = self.invoke("hybrid-author", self.nodes[node]["control"], generation,
                             article, ed_path, ml_path, public)
        lab("author", node, who, stem, "rc=%d" % result.returncode,
            result.stdout.decode().strip()[:120])
        return result

    def reader(self, node):
        return Reader(self.nodes[node]["port"])

    def stat(self, node, stem):
        r = self.reader(node)
        try:
            return r.cmd("STAT <%s@example.invalid>" % stem)[:3]
        finally:
            r.close()

    def control(self, node, stem):
        r = self.reader(node)
        try:
            status = r.cmd("HDR :fn-control <%s@example.invalid>" % stem)
            if not status.startswith("225"):
                return status
            lines = r.block()
            return lines[0].split(" ", 1)[1] if lines else ""
        finally:
            r.close()

    def group(self, node, name):
        r = self.reader(node)
        try:
            return r.cmd("GROUP " + name)[:3]
        finally:
            r.close()

    def listgroup(self, node, name):
        r = self.reader(node)
        try:
            status = r.cmd("LISTGROUP " + name)
            return r.block() if status.startswith("211") else []
        finally:
            r.close()

    def until(self, what, probe, want, seconds=60):
        deadline = time.monotonic() + seconds
        seen = None
        while time.monotonic() < deadline:
            seen = probe()
            if seen == want or (callable(want) and want(seen)):
                lab(what, repr(seen))
                return seen
            time.sleep(0.25)
        lab(what, "TIMEOUT", repr(seen))
        self.fail("%s: wanted %r, last saw %r" % (what, want, seen))

    def test_two_node_control_lab(self):
        self.start("a")
        self.start("b")
        for node in ("a", "b"):
            for gen, principal, who in ((1, self.p, "p"), (2, self.q, "q")):
                self.ok("hybrid-enroll", self.nodes[node]["control"], gen, principal,
                        self.ed_public, self.ml[who][1])
        # Targets: Q's signed article, and an unsigned post.
        self.assertEqual(self.author("a", "q", "t-signed").returncode, 0)
        r = self.reader("a")
        lab("post unsigned", r.post(self.source("t-unsigned").read_bytes()))
        r.close()
        for node in ("a", "b"):
            for stem in ("t-signed", "t-unsigned"):
                self.until("present %s %s" % (node, stem),
                           lambda: self.stat(node, stem), "223")

        # Unauthorized: an unsigned cancel, and Q cancelling what Q did not write.
        r = self.reader("a")
        lab("post unsigned-cancel", r.post(self.source(
            "c-unsigned", extra=b"Control: cancel <t-signed@example.invalid>\r\n")
            .read_bytes()))
        r.close()
        self.assertEqual(self.author(
            "a", "q", "c-stranger",
            extra=b"Control: cancel <t-unsigned@example.invalid>\r\n").returncode, 0)
        for node in ("a", "b"):
            self.until("decision %s c-unsigned" % node,
                       lambda: self.control(node, "c-unsigned"), "declined unsigned")
            self.until("decision %s c-stranger" % node,
                       lambda: self.control(node, "c-stranger"), "declined no-grant")
            for stem in ("t-signed", "t-unsigned"):
                self.assertEqual(self.stat(node, stem), "223")
                lab("still served", node, stem)

        # P's authority cancel of the unsigned article; Q's author cancel.
        self.assertEqual(self.author(
            "a", "p", "c-authority",
            extra=b"Control: cancel <t-unsigned@example.invalid>\r\n").returncode, 0)
        self.assertEqual(self.author(
            "a", "q", "c-author",
            extra=b"Control: cancel <t-signed@example.invalid>\r\n").returncode, 0)
        for node in ("a", "b"):
            self.until("withdrawn %s t-unsigned" % node,
                       lambda: self.stat(node, "t-unsigned"), "430")
            self.until("withdrawn %s t-signed" % node,
                       lambda: self.stat(node, "t-signed"), "430")
            self.assertEqual(self.control(node, "c-authority"),
                             "executed withdrawal <t-unsigned@example.invalid> authority")
            self.assertEqual(self.control(node, "c-author"),
                             "executed withdrawal <t-signed@example.invalid> author")
            lab("listgroup fn.test", node, self.listgroup(node, "fn.test"))
            self.assertEqual(self.listgroup(node, "fn.test"), [])

        # newgroup / rmgroup by P, ordered by the signed serial.
        approved = b"Approved: p@example.invalid\r\n"
        self.assertEqual(self.author(
            "a", "p", "g-new-1", newsgroups=b"fn.created,fn.test",
            extra=b"Control: newgroup fn.created\r\n" + approved +
            b"FN-Control-Serial: 1\r\n").returncode, 0)
        for node in ("a", "b"):
            self.until("newgroup %s" % node, lambda: self.group(node, "fn.created"), "211")
            lab("decision", node, self.control(node, "g-new-1"))
        self.assertEqual(self.author(
            "a", "q", "g-stranger", newsgroups=b"fn.bad,fn.test",
            extra=b"Control: newgroup fn.bad\r\n" + approved +
            b"FN-Control-Serial: 1\r\n").returncode, 0)
        self.assertEqual(self.author(
            "a", "p", "g-rm-2", newsgroups=b"fn.created,fn.test",
            extra=b"Control: rmgroup fn.created\r\n" + approved +
            b"FN-Control-Serial: 2\r\n").returncode, 0)
        self.assertEqual(self.author(
            "a", "p", "g-new-1-replay", newsgroups=b"fn.created,fn.test",
            extra=b"Control: newgroup fn.created\r\n" + approved +
            b"FN-Control-Serial: 1\r\n").returncode, 0)
        for node in ("a", "b"):
            self.until("decision %s g-stranger" % node,
                       lambda: self.control(node, "g-stranger"), "declined no-grant")
            self.assertEqual(self.group(node, "fn.bad"), "411")
            self.until("rmgroup %s" % node, lambda: self.group(node, "fn.created"), "411")
            self.until("decision %s g-new-1-replay" % node,
                       lambda: self.control(node, "g-new-1-replay"),
                       "declined stale-serial")

        # checkgroups: a report on both, applied by one operator.
        self.assertEqual(self.author(
            "a", "p", "g-check", extra=b"Control: checkgroups fn #7\r\n" + approved,
            body=b"fn.test\tThe test group\r\nfn.extra\tAn extra group\r\n"
            ).returncode, 0)
        for node in ("a", "b"):
            self.until("report %s" % node, lambda: self.control(node, "g-check"),
                       lambda seen: isinstance(seen, str) and seen.startswith("report 7 fn"))
        self.assertEqual(self.group("a", "fn.extra"), "411")
        applied = self.invoke("operator", self.nodes["a"]["config"], "control",
                              "apply-checkgroups", "<g-check@example.invalid>")
        lab("apply-checkgroups", "rc=%d" % applied.returncode,
            applied.stdout.decode().strip(), applied.stderr.decode().strip()[:200])
        self.until("applied a", lambda: self.group("a", "fn.extra"), "211")
        self.assertEqual(self.group("b", "fn.extra"), "411")
        lab("not applied b", "fn.extra 411")

        # Restart B: the withdrawal is durable and still hides the target.
        self.stop("b")
        self.start("b")
        self.until("after restart b t-unsigned",
                   lambda: self.stat("b", "t-unsigned"), "430")
        self.assertEqual(self.control("b", "c-authority"),
                         "executed withdrawal <t-unsigned@example.invalid> authority")
        lab("done")


if __name__ == "__main__":
    unittest.main()
