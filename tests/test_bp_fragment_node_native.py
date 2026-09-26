"""Two TCPCL contacts with a receiver restart between fragment arrivals.

ACL2 authors the request ADU, fragment boundaries, BP blocks, and exact wire.
Python only writes those bytes and drives real native processes.
"""

import os
from pathlib import Path
import shutil
import socket
import subprocess
import tempfile
import unittest

from tests.native_process import stop_and_diagnostics, wait_for_announcement
from tools import run_bp_ingress, run_store


ROOT = Path(os.environ.get(
    "FN_NATIVE_SOURCE_ROOT", Path(__file__).resolve().parent.parent))
IMAGE = Path(os.environ.get(
    "FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))


class NativeBpFragmentNodeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not os.access(IMAGE, os.X_OK):
            raise unittest.SkipTest(f"native developer image missing: {IMAGE}")

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-bp-fragment-node-"))
        self.addCleanup(shutil.rmtree, self.tmp)
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.store = self.tmp / "store"
        self.journal = self.tmp / "fnbs"
        self.receipts = self.tmp / "fnrj"
        self.workflow = self.tmp / "fnwf"
        initialized = self.invoke("store", self.store, "init", "fn.test")
        self.assertEqual(initialized.returncode, 0, initialized.stderr)
        with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as reservation:
            reservation.bind(("127.0.0.1", 0))
            self.port = reservation.getsockname()[1]
        self.config = self.tmp / "receiver-fn.toml"
        self.config.write_text(f'[store]\npath = "{self.store}"\n',
                               encoding="ascii")
        policy = self.invoke("operator", self.config, "policy", "set",
                             "path-identity", "receiver.bp.gate.invalid")
        self.assertEqual(policy.returncode, 0, policy.stderr)
        trusted = self.invoke(
            "operator", self.config, "bp-boundary", "add", "sender-boundary",
            "sender.bp.gate.invalid", "dtn://sender/", self.port,
            "fn.test", 32768, 16)
        self.assertEqual(trusted.returncode, 0, trusted.stderr)
        self.fragments = self.author_fragments()

    def invoke(self, *args, timeout=120):
        return subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT,
            env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=timeout, check=False,
        )

    def author_fragments(self, count=2):
        msgid = b"<bp-fragment-node@example.invalid>"
        article = (
            b"From: sender@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: fragmented request\r\n"
            b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
            b"Message-ID: " + msgid + b"\r\n\r\nfragmented body\r\n"
        )
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            bridge.call('(include-book "books/bp-adu")')
            bridge.call('(include-book "books/bp-fragment")')
            bridge.call('(include-book "books/bp-bundle")')
            _archive, subject, _provenance = run_store.metadata(msgid, article)

            def text(value):
                return "(fn-store-octets->string '" + bridge.literal(value) + ")"

            fields = [
                b"work-bp-fragment", subject, b"dtn://sender/",
                b"dtn://receiver/", b"native-policy", b"origin-native",
                b"wire-auth", b"terms-native",
            ]
            adu_form = (
                "(fn-bpa-encode (fn-bpa-make-request "
                + " ".join(text(value) for value in fields)
                + " '" + bridge.literal(article) + "))"
            )
            adu = run_store.acl2_octets(bridge.call(adu_form))
            # COUNT - 1 interior cut points, strictly increasing.  The cut
            # is fn-bpf-cut (no fragment-count ceiling), not fn-bpf-fragment
            # (at most 64 pieces).
            self.assertLess(count, len(adu))
            cuts = [len(adu) * k // count for k in range(1, count)]
            self.assertEqual(len(set(cuts)), count - 1)
            self.assertGreater(cuts[0], 0)
            self.assertLess(cuts[-1], len(adu))
            cut_form = ("(fn-bpf-cut '" + bridge.literal(adu) + " 0 '("
                        + " ".join(map(str, cuts)) + ") "
                        + str(len(adu)) + ")")
            primary = (
                "(fn-bpp-make-block 0 1 "
                "(cons :dtn '(47 47 114 101 99 101 105 118 101 114 47)) "
                "(cons :dtn '(47 47 115 101 110 100 101 114 47)) "
                "(cons :dtn '(47 47 115 101 110 100 101 114 47)) "
                "1000 2 3600000 nil nil)"
            )
            paths = []
            for index in range(count):
                form = (
                    "(let* ((parent " + primary + ") "
                    "(parts " + cut_form + ") "
                    "(part (nth " + str(index) + " parts))) "
                    "(fn-bpb-encode (fn-bpb-make-bundle "
                    "(fn-bpf-fragment-block parent (fn-bpf-offset part) "
                    "(fn-bpf-total part)) nil "
                    "(fn-bpb-payload-block 1 (fn-bpf-bytes part)))))"
                )
                wire = run_store.acl2_octets(bridge.call(form))
                path = self.tmp / f"fragment-{index}.bp"
                path.write_bytes(wire)
                paths.append(path)
            return paths
        finally:
            bridge.close()

    def start_receiver(self, once=True):
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "bp-node", "serve", str(self.port),
             str(self.journal), str(self.store), str(self.receipts),
             str(self.workflow), "dtn://receiver/", "dtn://sender/",
             "dtn://receiver/", "native-policy", "dtn://receiver/",
             "127.0.0.1", "9", "1" if once else "0", "3600000", "2", "32",
             "1048576", "1000", "0"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0,
        )
        self.addCleanup(self.stop_process, process)
        line = wait_for_announcement(process, b"BP NODE LISTENING ", timeout=45)
        if not line.startswith(b"BP NODE LISTENING "):
            self.fail(f"receiver failed: {line!r} {stop_and_diagnostics(process)}")
        actual_port = int(line.rsplit(b" ", 1)[1])
        self.assertEqual(actual_port, self.port)
        return process, actual_port

    @staticmethod
    def stop_process(process):
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=5)
        process.stdout.close()
        process.stderr.close()

    def send_fragment(self, port, path, number):
        return self.invoke(
            "tcpcl", "send", "127.0.0.1", port, path,
            self.tmp / f"sender-spool-{number}",
            "dtn://sender/", "dtn://receiver/", 0, 65536, 1048576, 0,
        )

    def article_count(self):
        store, bridge, _records = run_bp_ingress.open_live_bp_store(
            self.store, False)
        try:
            return bridge.article_count()
        finally:
            bridge.close()
            store.close()

    def test_nonzero_fragment_then_restart_offset_zero_dispatches_once(self):
        first, port = self.start_receiver()
        sent = self.send_fragment(port, self.fragments[1], 1)
        out, err = first.communicate(timeout=120)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(first.returncode, 0, (out, err))
        self.assertNotIn(b"BP application handoff durable", out)
        self.assertEqual(self.article_count(), 0)

        second, port = self.start_receiver()
        sent = self.send_fragment(port, self.fragments[0], 0)
        out, err = second.communicate(timeout=120)
        self.assertEqual(sent.returncode, 0, sent.stderr)
        self.assertEqual(second.returncode, 0, (out, err))
        self.assertIn(b"BP fragment family durable", out)
        self.assertIn(b"BP application handoff durable", out)
        self.assertEqual(self.article_count(), 1)

        restarted = self.invoke(
            "bp-node", "dispatch", self.journal, self.store,
            self.receipts, self.workflow, "dtn://receiver/", "dtn://sender/",
            "dtn://receiver/", "native-policy", "dtn://receiver/",
            "127.0.0.1", 9, 1, 3600000, 2, 32, 1048576, 1000, 0,
        )
        self.assertEqual(restarted.returncode, 0, restarted.stderr)
        self.assertEqual(self.article_count(), 1)

    def test_seventy_fragments_across_a_kill_reassemble_once(self):
        # PRF-121: a family of 70 fragments, beyond the old 64-fragment
        # reassembly ceiling, sent highest offset first, with the receiver
        # killed (SIGKILL) after 35 of them.  The restarted receiver recovers
        # the 35 held fragments from its journal, takes the other 35 and
        # reassembles the family once: one handoff, one article.
        fragments = self.author_fragments(70)
        order = list(reversed(range(70)))
        first, port = self.start_receiver(once=False)
        for number in order[:35]:
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0, sent.stderr)
        first.kill()
        out, err = first.communicate(timeout=60)
        self.assertNotIn(b"BP fragment family durable", out)
        self.assertEqual(self.article_count(), 0)

        second, port = self.start_receiver(once=False)
        for number in order[35:]:
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0, sent.stderr)
        second.terminate()
        out, err = second.communicate(timeout=120)
        self.assertEqual(out.count(b"BP fragment family durable"), 1, (out, err))
        self.assertEqual(out.count(b"BP application handoff durable"), 1,
                         (out, err))
        self.assertEqual(self.article_count(), 1)


if __name__ == "__main__":
    unittest.main()
