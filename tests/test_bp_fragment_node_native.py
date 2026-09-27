"""Two TCPCL contacts with a receiver restart between fragment arrivals.

ACL2 authors the request ADU, fragment boundaries, BP blocks, and exact wire.
Python only writes those bytes and drives real native processes.
"""

import os
from pathlib import Path
import re
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
    STORE_PROFILES = {
        "test_ten_mebibyte_article_through_four_kib_fragments": [
            "--max-article-octets", "11534336",
            "--max-record-octets", "33554432",
            "--max-history-octets", "268435456"],
    }
    BOUNDARY_MAX_OCTETS = {
        "test_ten_mebibyte_article_through_four_kib_fragments": 11534336,
    }

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
        # SCN-077 step 1's Store half: the development base admits 32,768-
        # octet articles, and the neighbour's inbound bound (bp-boundary
        # MAX-OCTETS, the peer record's inbound max) was 32,768 too, so the
        # 10 MiB case raises both to 11 MiB (and the Store's record and
        # history bounds that admit one).  Without them the article is
        # refused :oversize and the handoff is reported refused (PRF-224,
        # PKT-630 (7)).
        profile = self.STORE_PROFILES.get(self._testMethodName, [])
        initialized = self.invoke("store", self.store, "init", *profile,
                                  "fn.test")
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
            "fn.test", self.BOUNDARY_MAX_OCTETS.get(self._testMethodName, 32768),
            16)
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
        # The node's own read-only open (`store PATH status`,
        # books/native-live-status.lisp fn-nls-report's `articles=' word):
        # it replays and verifies every durable record the way the served
        # path does, at any admitted record size.  The Python text bridge
        # (tools/frame_bridge.py) prints each record as a decimal list, and
        # its ACL2 exhausts its control stack decoding a 10 MiB record
        # (SCN-077), so it is not the readback here.
        status = self.invoke("store", self.store, "status", timeout=900)
        self.assertEqual(status.returncode, 0, (status.stdout, status.stderr))
        counts = re.findall(rb"^transactions=[0-9]+ articles=([0-9]+) ",
                            status.stdout, re.MULTILINE)
        self.assertEqual(len(counts), 1, status.stdout)
        return int(counts[0])

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
        self.large_msgid, self.large_article = msgid, article
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

    @staticmethod
    def drain(process):
        """Read PROCESS's stdout in a thread so a receiver that prints a line
        per session never blocks on a full pipe; returns a function that
        joins the thread and answers what was read."""
        import threading
        chunks = []
        errors = []

        def pump(stream, into):
            while True:
                chunk = os.read(stream.fileno(), 65536)
                if not chunk:
                    return
                into.append(chunk)

        threads = [threading.Thread(target=pump, args=(process.stdout, chunks),
                                    daemon=True),
                   threading.Thread(target=pump, args=(process.stderr, errors),
                                    daemon=True)]
        for thread in threads:
            thread.start()

        def finish(timeout):
            process.wait(timeout=timeout)
            for thread in threads:
                thread.join(timeout=60)
            finish.stderr = b"".join(errors)
            return b"".join(chunks)
        return finish

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
        # held, an 11 MiB ADU) and rotates every 1,000 records, a 10 MiB
        # article's ADU is cut into fragments whose bundles are at most 4 KiB;
        # the receiver is killed with SIGKILL halfway through the family, the
        # journal rotates by itself twice while the family is in flight (at
        # the opens that find a half's records in the generation; books/
        # bp-node-rotation-due), and the rest arrive at a restarted receiver.
        started = time.monotonic()
        paths, total = self.author_large_fragments(10 * 1024 * 1024, 4000)
        authored = time.monotonic()
        count = len(paths)
        print(f"SCN-077 adu-octets={total} fragments={count} "
              f"author-seconds={authored - started:.1f}", flush=True)
        self.assertGreater(count, 2560)
        raised = self.invoke("bp-node", "profile", self.journal,
                             "dtn://receiver/", 4096, 16777216,
                             11 * 1024 * 1024, 1048576, 1000)
        self.assertEqual(raised.returncode, 0, raised.stderr)
        self.assertIn(b"max-adu-octets=11534336", raised.stdout)
        self.assertIn(b"rotate-records=1000", raised.stdout)
        order = list(reversed(range(count)))
        half = count // 2
        first, port = self.start_receiver(once=False)
        first_out = self.drain(first)
        self.send_many(port, order[:half], paths)
        first.kill()
        out = first_out(120)
        self.assertNotIn(b"BP fragment family durable", out)
        killed = time.monotonic()
        print(f"SCN-077 first-half-seconds={killed - authored:.1f}", flush=True)
        # The serve itself rotated when its generation reached 1,000 records,
        # between sessions, with the family's first fragments held (lane
        # bp-retention-leftovers, fn-bpnrd-serve-rotation-due-p): the new
        # selection durable and "lifecycle" retired while it kept serving.
        self.assertGreaterEqual(out.count(b"BP journal rotation in serve"), 1,
                                out[-4000:])
        self.assertIn(b"BP journal generation selected generation=1", out)
        self.assertIn(b"BP journal generation retired name=lifecycle", out)
        # The next open recovers every held fragment of the first half.
        held, rotated = self.recovered_held(output=True)
        self.assertEqual(held, half)
        generations = [self.generation_number(path)
                       for path in self.generation_directories()]
        self.assertEqual(len(generations), 1, generations)
        self.assertGreaterEqual(generations[0], 1)
        second, port = self.start_receiver(once=False)
        second_out = self.drain(second)
        self.send_many(port, order[half:-1], paths)
        second.terminate()
        out = second_out(300)
        self.assertNotIn(b"BP fragment family durable", out)
        # The second half crossed the threshold again inside this serve.
        self.assertGreaterEqual(out.count(b"BP journal rotation in serve"), 1,
                                out[-4000:])
        before_last = time.monotonic()
        print(f"SCN-077 second-half-seconds={before_last - killed:.1f}",
              flush=True)
        third, port = self.start_receiver()
        third_out = self.drain(third)
        number = order[-1]
        sent = self.send_fragment(port, paths[number], number, 3600)
        self.assertEqual(sent.returncode, 0, (sent.stdout, sent.stderr))
        out = third_out(3600)
        err = third_out.stderr
        done = time.monotonic()
        print(f"SCN-077 reassembly-and-handoff-seconds={done - before_last:.1f}",
              flush=True)
        self.assertEqual(third.returncode, 0, (out[-4000:], err[-4000:]))
        # The journal rotated at least twice with the family in flight (in
        # the two serves, and at an open that found a generation past the
        # threshold); one generation directory is left, every earlier one
        # retired.
        generations = [self.generation_number(path)
                       for path in self.generation_directories()]
        self.assertEqual(len(generations), 1, generations)
        self.assertGreaterEqual(generations[0], 2)
        self.assertEqual(out.count(b"BP fragment family durable"), 1, (out, err))
        self.assertEqual(out.count(b"BP application handoff durable"), 1,
                         (out, err))
        self.assertIn(b"BP application handoff durable "
                      b"disposition=request-accepted", out)
        self.assertEqual(self.article_count(), 1,
                         [line for line in out.splitlines()
                          if b"delivery" in line or b"refused" in line
                          or b"application" in line])
        # The Store holds exactly the article the ADU carried: the node's
        # own lookup (`store PATH inspect MSGID`) writes them to stdout.
        inspected = self.invoke("store", self.store, "inspect",
                                self.large_msgid.decode("ascii"), timeout=900)
        self.assertEqual(inspected.returncode, 0, inspected.stderr[-4000:])
        self.assertEqual(len(inspected.stdout), len(self.large_article))
        self.assertTrue(inspected.stdout == self.large_article,
                        "the stored article differs from the one the ADU carried")

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

    def kill_at_rotation(self):
        """Start `bp-node serve'; as soon as its open announces a rotation,
        kill it with SIGKILL.  No developer cut: the kill lands wherever
        the publication or retirement program is, and every such point is
        a crash point of the model (fn-bpnr-rotation-crash-recovers-old-
        or-new, fn-bpnr-retirement-cut-keeps-open-view).  Returns what the
        process printed."""
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "bp-node", "serve", str(self.port),
             str(self.journal), str(self.store), str(self.receipts),
             str(self.workflow), "dtn://receiver/", "dtn://sender/",
             "dtn://receiver/", "native-policy", "dtn://receiver/",
             "127.0.0.1", "9", "1", "3600000", "2", "32",
             "1048576", "1000", "0"],
            cwd=ROOT, env=self.env, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, bufsize=0)
        marker = b"BP journal rotation generation="
        seen = b""
        deadline = time.monotonic() + 120
        while marker not in seen and time.monotonic() < deadline:
            ready, _, _ = select.select([process.stdout], [], [], 1)
            if ready:
                chunk = os.read(process.stdout.fileno(), 65536)
                if not chunk:
                    break
                seen += chunk
        process.kill()
        process.wait(timeout=15)
        process.stdout.close()
        process.stderr.close()
        self.assertIn(marker, seen, seen)
        return seen

    @staticmethod
    def generation_number(path):
        """The generation a directory name carries: `lifecycle' is 0, and
        `lifecycle-gNNNN' (books/bp-node-rotation-codec.lisp
        fn-bpnr-generation-directory) is NNNN."""
        name = path.name
        return 0 if name == "lifecycle" else int(name[len("lifecycle-g"):])

    def generation_directories(self):
        return sorted(path for path in self.journal.iterdir()
                      if path.is_dir() and path.name.startswith("lifecycle"))

    def recovered_held(self, output=False):
        """The held count the node's open recovers (`bp-node dispatch');
        after a rotation the open reopens, and the last reading counts."""
        reopened = self.invoke(
            "bp-node", "dispatch", self.journal, self.store,
            self.receipts, self.workflow, "dtn://receiver/", "dtn://sender/",
            "dtn://receiver/", "native-policy", "dtn://receiver/",
            "127.0.0.1", 9, 1, 3600000, 2, 32, 1048576, 1000, 0,
        )
        self.assertEqual(reopened.returncode, 0, reopened.stderr)
        held = None
        for line in reopened.stdout.splitlines():
            if line.startswith(b"BP FNBS recovered held="):
                held = int(line.split(b"=", 1)[1])
        if held is None:
            self.fail(reopened.stdout)
        return (held, reopened.stdout) if output else held

    def test_rotation_with_a_family_in_flight_loses_no_fragment(self):
        # N16 under load, on every image (F7): no developer cut.  Under a
        # profile whose rotation threshold is one record, every open of a
        # node verb that finds a record in its generation rotates (books/
        # bp-node-rotation-due), with a family of eight in flight: killed
        # inside that rotation, then a retirement step that fails (the
        # state a death after the selection leaves), then clean.  Every
        # reopen recovers the held fragments; the offset-zero fragment then
        # completes the family once.
        self.assertNotEqual(os.geteuid(), 0,
                            "the failed retirement step needs a non-root run")
        # A serve rotates between sessions as well (lane bp-retention-
        # leftovers): the four sessions run under a threshold of 100 so their
        # records are in the generation at the next open, then the operator
        # lowers it to one record.
        raised = self.invoke("bp-node", "profile", self.journal,
                             "dtn://receiver/", 64, 16777216, 65538, 1048576, 100)
        self.assertEqual(raised.returncode, 0, raised.stderr)
        self.assertIn(b"rotate-records=100", raised.stdout)
        fragments = self.author_fragments(8)
        first, port = self.start_receiver(once=False)
        for number in range(7, 3, -1):
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0,
                             (number, sent.stdout, sent.stderr))
        first.terminate()
        out, err = first.communicate(timeout=120)
        self.assertNotIn(b"BP fragment family durable", out)
        self.assertNotIn(b"BP journal rotation in serve", out)
        lowered = self.invoke("bp-node", "profile", self.journal,
                              "dtn://receiver/", 64, 16777216, 65538, 1048576, 1)
        self.assertEqual(lowered.returncode, 0, lowered.stderr)
        self.assertIn(b"rotate-records=1", lowered.stdout)
        # The next open rotates (four records): killed there.
        killed = self.kill_at_rotation()
        self.assertIn(b"BP journal rotation generation=1 records=", killed)
        held, recovered = self.recovered_held(output=True)
        self.assertEqual(held, 4, (killed, recovered))
        print("rotation kill: killed output ends "
              + repr(killed[-300:]) + "; recovery printed "
              + repr([line for line in recovered.splitlines()
                      if b"journal" in line]), flush=True)
        # A kill after the selection became durable leaves "lifecycle" for
        # the next rotation to remove; before it, the reopen rotated.
        print("rotation kill: generation directories "
              + repr([path.name for path in self.generation_directories()]),
              flush=True)
        # A serve now rotates between sessions too (fn-bpnrd-serve-rotation-
        # due-p): with the threshold at one record every session would.  The
        # threshold is raised for these three sessions, so their records are
        # still in the generation at the next open, and lowered again after.
        raised = self.invoke("bp-node", "profile", self.journal,
                             "dtn://receiver/", 64, 16777216, 65538, 1048576, 100)
        self.assertEqual(raised.returncode, 0, raised.stderr)
        second, port = self.start_receiver(once=False)
        for number in range(3, 0, -1):
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0,
                             (number, sent.stdout, sent.stderr))
        second.terminate()
        out, err = second.communicate(timeout=120)
        self.assertNotIn(b"BP fragment family durable", out)
        self.assertNotIn(b"BP journal rotation in serve", out)
        lowered = self.invoke("bp-node", "profile", self.journal,
                              "dtn://receiver/", 64, 16777216, 65538, 1048576, 1)
        self.assertEqual(lowered.returncode, 0, lowered.stderr)
        # The selected generation's directory cannot be emptied: the next
        # open rotates, the new selection is durable, and retirement fails
        # at the selected directory.  Recovery reads the new generation;
        # the old one stays until the next rotation finishes the removal.
        old = max(self.generation_directories(), key=self.generation_number)
        os.chmod(old, 0o555)
        try:
            held, blocked = self.recovered_held(output=True)
            self.assertEqual(held, 7, blocked)
            self.assertIn(b"BP journal generation selected", blocked)
            self.assertIn(b"BP journal generation retirement incomplete step=",
                          blocked)
            self.assertTrue(old.exists())
            self.assertEqual(self.recovered_held(), 7)
        finally:
            os.chmod(old, 0o755)
        # An open that does not rotate leaves the journal as it found it.
        held, reopened = self.recovered_held(output=True)
        self.assertEqual(held, 7)
        self.assertNotIn(b"BP journal generation retired", reopened)
        self.assertTrue(old.exists())
        last, port = self.start_receiver()
        sent = self.send_fragment(port, fragments[0], 0)
        self.assertEqual(sent.returncode, 0, (sent.stdout, sent.stderr))
        out, err = last.communicate(timeout=300)
        self.assertEqual(last.returncode, 0, (out, err))
        self.assertEqual(out.count(b"BP fragment family durable"), 1, (out, err))
        self.assertEqual(out.count(b"BP application handoff durable"), 1,
                         (out, err))
        self.assertEqual(self.article_count(), 1)
        # The last fragment's record makes the serve rotate between its
        # session and its deliveries (or, for records written after that,
        # the next open); the rotation first finishes the removal the failed
        # step left.
        _held, finished = self.recovered_held(output=True)
        self.assertIn(b"BP journal generation retired name=" + old.name.encode(),
                      out + finished)
        self.assertFalse(old.exists())
        self.assertEqual(len(self.generation_directories()), 1)

    def test_serve_crosses_the_threshold_twice_with_a_family_in_flight(self):
        # Lane bp-retention-leftovers: one `bp-node serve' process, a profile
        # rotating every two records, a family of eight fragments of which
        # seven arrive (highest offset first) in seven sessions.  The serve
        # rotates between sessions each time its generation reaches the
        # threshold (fn-bpnrd-serve-rotation-due-p), at least twice, without
        # stopping and without the developer cut; every rotation keeps every
        # held fragment (fn-bpnrd-rotation-keeps-every-held-family), the old
        # generations are retired, and the offset-zero fragment then
        # completes the family once.
        raised = self.invoke("bp-node", "profile", self.journal,
                             "dtn://receiver/", 64, 16777216, 65538, 1048576, 2)
        self.assertEqual(raised.returncode, 0, raised.stderr)
        self.assertIn(b"rotate-records=2", raised.stdout)
        fragments = self.author_fragments(8)
        serve, port = self.start_receiver(once=False)
        for number in range(7, 0, -1):
            sent = self.send_fragment(port, fragments[number], number)
            self.assertEqual(sent.returncode, 0,
                             (number, sent.stdout, sent.stderr))
        serve.terminate()
        out, err = serve.communicate(timeout=120)
        rotations = out.count(b"BP journal rotation in serve")
        print(f"serve rotations={rotations} generations="
              f"{[path.name for path in self.generation_directories()]}",
              flush=True)
        self.assertGreaterEqual(rotations, 2, out[-4000:])
        self.assertGreaterEqual(
            len(re.findall(rb"BP journal generation selected generation=", out)),
            2, out[-4000:])
        self.assertNotIn(b"BP journal rotation uncertain", out)
        self.assertNotIn(b"BP fragment family durable", out)
        generations = self.generation_directories()
        self.assertEqual(len(generations), 1, [p.name for p in generations])
        self.assertGreaterEqual(self.generation_number(generations[0]), 2)
        self.assertEqual(self.recovered_held(), 7)
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
