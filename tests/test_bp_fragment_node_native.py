"""Two TCPCL contacts with a receiver restart between fragment arrivals.

ACL2 authors the request ADU, fragment boundaries, BP blocks, and exact wire.
Python only writes those bytes and drives real native processes.
"""

import os
from pathlib import Path
import select
import shutil
import socket
import subprocess
import tempfile
import time
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

    def send_fragment(self, port, path, number, timeout=120):
        return self.invoke(
            "tcpcl", "send", "127.0.0.1", port, path,
            self.tmp / f"sender-spool-{number}",
            "dtn://sender/", "dtn://receiver/", 0, 65536, 1048576, 0,
            timeout=timeout,
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

    def kill_across_family(self, count, before_kill):
        # A family of COUNT fragments, sent highest offset first, with the
        # receiver killed (SIGKILL) after BEFORE_KILL of them.  The restarted
        # receiver recovers the held fragments from its journal, takes the
        # rest and reassembles the family once: one handoff, one article.
        # Nothing completes before the last fragment (offset zero).
        fragments = self.author_fragments(count)
        order = list(reversed(range(count)))
        first, port = self.start_receiver(once=False)
        for number in order[:before_kill]:
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0,
                             (number, sent.stdout, sent.stderr))
        first.kill()
        out, err = first.communicate(timeout=60)
        self.assertNotIn(b"BP fragment family durable", out)
        self.assertEqual(self.article_count(), 0)

        second, port = self.start_receiver(once=False)
        for number in order[before_kill:-1]:
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0,
                             (number, sent.stdout, sent.stderr))
        second.terminate()
        out, err = second.communicate(timeout=120)
        self.assertNotIn(b"BP fragment family durable", out)
        # The last fragment goes to a one-session receiver, which exits only
        # after its post-session work (the family, then the Store handoff).
        third, port = self.start_receiver()
        number = order[-1]
        sent = self.send_fragment(port, fragments[number], number)
        self.assertEqual(sent.returncode, 0, (number, sent.stdout, sent.stderr))
        out, err = third.communicate(timeout=300)
        self.assertEqual(third.returncode, 0, (out, err))
        self.assertEqual(out.count(b"BP fragment family durable"), 1, (out, err))
        self.assertEqual(out.count(b"BP application handoff durable"), 1,
                         (out, err))
        self.assertEqual(self.article_count(), 1)

    def test_sixty_four_fragments_across_a_kill_reassemble_once(self):
        # PRF-121 on the served path: the uncapped sweep reassembler and the
        # once-per-family selector, with the family filling the node's held
        # capacity (*fn-bpn-machine-max-jobs*, 64 rows) across a kill.
        self.kill_across_family(64, 32)

    def test_seventy_fragments_across_a_kill_reassemble_once(self):
        # SCN-067: 70 fragments, beyond the old 64-fragment reassembly
        # ceiling and the default profile's 64 held rows, with the receiver
        # killed after 35.  The operator raises the node's profile to 128
        # held rows first (PRF-131 part 2, books/bp-node-profile.lisp);
        # ACL2 refuses to lower it again.
        raised = self.invoke("bp-node", "profile", self.journal,
                             "dtn://receiver/", 128, 16777216)
        self.assertEqual(raised.returncode, 0, raised.stderr)
        self.assertIn(b"BP node profile max-held-rows=128", raised.stdout)
        lowered = self.invoke("bp-node", "profile", self.journal,
                              "dtn://receiver/", 64, 16777216)
        self.assertEqual(lowered.returncode, 1, lowered.stderr)
        self.kill_across_family(70, 35)

    # -- SCN-077 (PRF-134): a 10 MiB article through 4 KiB fragments -------

    def author_large_fragments(self, body_octets, piece):
        """ACL2 authors one request ADU carrying an article of about
        BODY_OCTETS octets and cuts it (fn-bpf-cut-fast, the linear twin of
        fn-bpf-cut, fn-bpf-cut-fast-is-cut) into extents of PIECE octets;
        each fragment's bundle is ACL2's.  Returns the fragment paths in
        offset order and the ADU's length."""
        msgid = b"<bp-scn-077@example.invalid>"
        line = b"x" * 76 + b"\r\n"
        body = line * (body_octets // len(line))
        article = (
            b"From: sender@example.invalid\r\n"
            b"Newsgroups: fn.test\r\n"
            b"Subject: ten mebibytes through four KiB fragments\r\n"
            b"Date: Mon, 21 Sep 2026 08:00:00 +0000\r\n"
            b"Message-ID: " + msgid + b"\r\n\r\n" + body
        )
        bridge = run_bp_ingress.Acl2BpIngress()
        try:
            for book in ("bp-adu", "bp-fragment", "bp-fragment-fast",
                         "bp-bundle"):
                bridge.call('(include-book "books/' + book + '")')
            _archive, subject, _provenance = run_store.metadata(msgid, article)

            def text(value):
                return "(fn-store-octets->string '" + bridge.literal(value) + ")"

            fields = [
                b"work-bp-scn-077", subject, b"dtn://sender/",
                b"dtn://receiver/", b"native-policy", b"origin-native",
                b"wire-auth", b"terms-native",
            ]
            bridge.call("(defconst *bpl4-article* '" + bridge.literal(article)
                        + ")", timeout=3600)
            bridge.call(
                "(defconst *bpl4-adu* (fn-bpa-encode (fn-bpa-make-request "
                + " ".join(text(value) for value in fields)
                + " *bpl4-article*)))", timeout=3600)
            total = int(run_store.acl2_result(
                bridge.call("(len *bpl4-adu*)")))
            self.assertGreater(total, len(article))
            cuts = list(range(piece, total, piece))
            bridge.call("(defconst *bpl4-parts* (fn-bpf-cut-fast *bpl4-adu* 0 '("
                        + " ".join(map(str, cuts)) + ") " + str(total) + "))",
                        timeout=3600)
            primary = (
                "(fn-bpp-make-block 0 1 "
                "(cons :dtn '(47 47 114 101 99 101 105 118 101 114 47)) "
                "(cons :dtn '(47 47 115 101 110 100 101 114 47)) "
                "(cons :dtn '(47 47 115 101 110 100 101 114 47)) "
                "1000 3 3600000 nil nil)"
            )
            paths = []
            for index in range(len(cuts) + 1):
                form = (
                    "(let* ((parent " + primary + ") "
                    "(part (nth " + str(index) + " *bpl4-parts*))) "
                    "(fn-bpb-encode (fn-bpb-make-bundle "
                    "(fn-bpf-fragment-block parent (fn-bpf-offset part) "
                    "(fn-bpf-total part)) nil "
                    "(fn-bpb-payload-block 1 (fn-bpf-bytes part)))))"
                )
                wire = run_store.acl2_octets(bridge.call(form))
                self.assertLessEqual(len(wire), 4096, index)
                path = self.tmp / f"large-{index}.bp"
                path.write_bytes(wire)
                paths.append(path)
            return paths, total
        finally:
            bridge.close()

    def send_many(self, port, numbers, paths, workers=4):
        """Send each fragment in its own TCPCL session, WORKERS at a time;
        every send must be accepted."""
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=workers) as pool:
            results = list(pool.map(
                lambda n: (n, self.send_fragment(port, paths[n], n, 900)),
                numbers))
        for number, sent in results:
            self.assertEqual(sent.returncode, 0,
                             (number, sent.stdout, sent.stderr))

    def test_ten_mebibyte_article_through_four_kib_fragments(self):
        # SCN-077: under a profile that admits it (4,096 held rows, 16 MiB
        # held, an 11 MiB ADU), a 10 MiB article's ADU is cut into fragments
        # whose bundles are at most 4 KiB; the receiver is killed with
        # SIGKILL halfway through the family, the journal rotates while the
        # family is in flight, and the rest arrive at a restarted receiver.
        started = time.monotonic()
        paths, total = self.author_large_fragments(10 * 1024 * 1024, 4000)
        authored = time.monotonic()
        count = len(paths)
        print(f"SCN-077 adu-octets={total} fragments={count} "
              f"author-seconds={authored - started:.1f}", flush=True)
        self.assertGreater(count, 2560)
        raised = self.invoke("bp-node", "profile", self.journal,
                             "dtn://receiver/", 4096, 16777216,
                             11 * 1024 * 1024, 1048576)
        self.assertEqual(raised.returncode, 0, raised.stderr)
        self.assertIn(b"max-adu-octets=11534336", raised.stdout)
        order = list(reversed(range(count)))
        half = count // 2
        first, port = self.start_receiver(once=False)
        self.send_many(port, order[:half], paths)
        first.kill()
        out, err = first.communicate(timeout=120)
        self.assertNotIn(b"BP fragment family durable", out)
        killed = time.monotonic()
        print(f"SCN-077 first-half-seconds={killed - authored:.1f}", flush=True)
        # The journal rotates with the family's first half held.
        rotated = self.rotate()
        self.assertIn(b"BP journal generation retired", rotated)
        self.assertEqual(self.recovered_held(), half)
        second, port = self.start_receiver(once=False)
        self.send_many(port, order[half:-1], paths)
        second.terminate()
        out, err = second.communicate(timeout=300)
        self.assertNotIn(b"BP fragment family durable", out)
        before_last = time.monotonic()
        print(f"SCN-077 second-half-seconds={before_last - killed:.1f}",
              flush=True)
        third, port = self.start_receiver()
        number = order[-1]
        sent = self.send_fragment(port, paths[number], number)
        self.assertEqual(sent.returncode, 0, (sent.stdout, sent.stderr))
        out, err = third.communicate(timeout=3600)
        done = time.monotonic()
        print(f"SCN-077 reassembly-and-handoff-seconds={done - before_last:.1f}",
              flush=True)
        self.assertEqual(third.returncode, 0, (out[-4000:], err[-4000:]))
        self.assertEqual(out.count(b"BP fragment family durable"), 1, (out, err))
        self.assertEqual(out.count(b"BP application handoff durable"), 1,
                         (out, err))
        self.assertEqual(self.article_count(), 1)

    def test_adu_past_the_profile_is_refused_before_custody(self):
        # PRF-134: under the default profile (ADU 65,538 octets) a fragment
        # of a 70,000-octet ADU is refused by name and nothing is held.
        paths, total = self.author_large_fragments(69000, 4000)
        self.assertGreater(total, 65538)
        receiver, port = self.start_receiver()
        sent = self.send_fragment(port, paths[-1], 0)
        out, err = receiver.communicate(timeout=120)
        self.assertIn(b"ADU-BEYOND-PROFILE", (out + err).upper(), (out, err))
        self.assertEqual(self.recovered_held(), 0)

    def test_journal_past_its_profile_is_refused_at_open(self):
        # PRF-131/PRF-134 natively: 70 fragments held under a 128-row profile;
        # the profile file removed (the default, 64 rows), the journal's open
        # is refused with the named verdict and the held rows are not lost.
        raised = self.invoke("bp-node", "profile", self.journal,
                             "dtn://receiver/", 128, 16777216)
        self.assertEqual(raised.returncode, 0, raised.stderr)
        fragments = self.author_fragments(71)
        first, port = self.start_receiver(once=False)
        for number in range(70, 0, -1):
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0,
                             (number, sent.stdout, sent.stderr))
        first.terminate()
        first.communicate(timeout=120)
        self.assertEqual(self.recovered_held(), 70)
        profile = self.journal / "bp-node-profile"
        saved = profile.read_bytes()
        profile.unlink()
        reopened = self.invoke(
            "bp-node", "dispatch", self.journal, self.store,
            self.receipts, self.workflow, "dtn://receiver/", "dtn://sender/",
            "dtn://receiver/", "native-policy", "dtn://receiver/",
            "127.0.0.1", 9, 1, 3600000, 2, 32, 1048576, 1000, 0,
        )
        self.assertEqual(reopened.returncode, 3, (reopened.stdout, reopened.stderr))
        self.assertIn(b"HELD-BEYOND-PROFILE",
                      (reopened.stdout + reopened.stderr).upper(),
                      (reopened.stdout, reopened.stderr))
        # `bp-node profile' opens the journal too, so it cannot raise a
        # profile the journal is already past (PKT-294); the operator puts
        # the profile file back, and every row is there.
        refused = self.invoke("bp-node", "profile", self.journal,
                              "dtn://receiver/", 128, 16777216)
        self.assertNotEqual(refused.returncode, 0, refused.stdout)
        profile.write_bytes(saved)
        self.assertEqual(self.recovered_held(), 70)

    def rotate(self, stop=None):
        """`bp-node checkpoint` on the stopped receiver; with STOP, the
        developer cut stops it there and the test kills it with SIGKILL."""
        env = dict(self.env)
        if stop:
            env["FN_BP_ROTATION_TEST_STOP"] = stop
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "bp-node", "checkpoint",
             str(self.journal), "dtn://receiver/"],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0)
        if not stop:
            out, err = process.communicate(timeout=120)
            self.assertEqual(process.returncode, 0, (out, err))
            return out
        marker = b"BP journal rotation stopped at=" + stop.encode()
        seen = b""
        deadline = time.monotonic() + 120
        while marker not in seen and time.monotonic() < deadline:
            ready, _, _ = select.select([process.stdout], [], [], 1)
            if ready:
                chunk = os.read(process.stdout.fileno(), 65536)
                if not chunk:
                    break
                seen += chunk
        self.assertIn(marker, seen, seen)
        process.kill()
        process.wait(timeout=15)
        process.stdout.close()
        process.stderr.close()
        return seen

    def recovered_held(self):
        reopened = self.invoke(
            "bp-node", "dispatch", self.journal, self.store,
            self.receipts, self.workflow, "dtn://receiver/", "dtn://sender/",
            "dtn://receiver/", "native-policy", "dtn://receiver/",
            "127.0.0.1", 9, 1, 3600000, 2, 32, 1048576, 1000, 0,
        )
        self.assertEqual(reopened.returncode, 0, reopened.stderr)
        for line in reopened.stdout.splitlines():
            if line.startswith(b"BP FNBS recovered held="):
                return int(line.split(b"=", 1)[1])
        self.fail(reopened.stdout)

    def test_rotation_with_a_family_in_flight_loses_no_fragment(self):
        # N16 under load (item 5): seven of eight fragments are held when
        # the journal rotates, killed after the rename, killed inside the
        # retirement program, then clean.  Every reopen recovers the seven;
        # the offset-zero fragment then completes the family once.
        fragments = self.author_fragments(8)
        first, port = self.start_receiver(once=False)
        for number in range(7, 0, -1):
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0,
                             (number, sent.stdout, sent.stderr))
        first.terminate()
        out, err = first.communicate(timeout=120)
        self.assertNotIn(b"BP fragment family durable", out)
        self.assertEqual(self.recovered_held(), 7)
        for stop in ("replace", "retire-2"):
            self.rotate(stop)
            self.assertEqual(self.recovered_held(), 7, stop)
        out = self.rotate()
        self.assertIn(b"BP journal generation retired name=lifecycle", out)
        self.assertEqual(self.recovered_held(), 7)
        self.assertFalse((self.journal / "lifecycle").exists())
        last, port = self.start_receiver()
        sent = self.send_fragment(port, fragments[0], 0)
        self.assertEqual(sent.returncode, 0, (sent.stdout, sent.stderr))
        out, err = last.communicate(timeout=300)
        self.assertEqual(last.returncode, 0, (out, err))
        self.assertEqual(out.count(b"BP fragment family durable"), 1, (out, err))
        self.assertEqual(out.count(b"BP application handoff durable"), 1,
                         (out, err))
        self.assertEqual(self.article_count(), 1)

if __name__ == "__main__":
    unittest.main()
