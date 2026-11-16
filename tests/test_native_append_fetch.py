"""Exact-byte acceptance controls for the native APPEND/FETCH restart fixture."""
import importlib.util
from pathlib import Path
import unittest
import os
import selectors
import subprocess
import tempfile
import time
from unittest import mock

spec = importlib.util.spec_from_file_location("native_append_fetch", Path(__file__).with_name("native-append-fetch-restart.py"))
campaign = importlib.util.module_from_spec(spec)
spec.loader.exec_module(campaign)


class ExactFetch(unittest.TestCase):
    def test_status_binds_committed_occurrences_and_survives_restart(self):
        articles = [dict(domain=712, position=41), dict(domain=712, position=42)]
        reply = dict(outcome="accepted", domain=712, position=0, frontier=42, gap=0)
        before = campaign.checked_status(reply, articles, 0)
        self.assertEqual(campaign.checked_status(dict(reply), articles, 0, before), before)
        for field, value in (("outcome", "refused"), ("domain", 713),
                             ("position", 1), ("frontier", 41), ("gap", 1)):
            with self.subTest(field=field), self.assertRaises(AssertionError):
                campaign.checked_status(dict(reply, **{field: value}), articles, 0, before)

    def test_init_timeout_stops_owned_child_and_grandchild(self):
        real_popen = subprocess.Popen
        children = []
        def capture(*args, **kwargs):
            kwargs["stdout"] = subprocess.PIPE
            process = real_popen(*args, **kwargs)
            children.append(process)
            return process
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            launcher = root / "fn"
            launcher.write_text("#!/usr/bin/env python3\n"
                                "import subprocess,sys,time\n"
                                "subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(60)'])\n"
                                "print('GRANDCHILD-STARTED', flush=True)\n"
                                "time.sleep(60)\n")
            launcher.chmod(0o755)
            try:
                with mock.patch.object(campaign, "ROOT", root), \
                     mock.patch.object(campaign.subprocess, "Popen", side_effect=capture):
                    with self.assertRaises(subprocess.TimeoutExpired):
                        campaign.initialize(root, root / "image", seconds=1)
                process = children[0]
                self.assertIsNotNone(process.poll())
                self.assertEqual(int((root / "init.launcher.pid").read_text()), process.pid)
                # Both processes inherit this pipe. EOF proves the grandchild
                # did not survive the direct launcher's timeout cleanup.
                os.set_blocking(process.stdout.fileno(), False)
                data = b""
                eof = False
                deadline = time.monotonic() + 2
                with selectors.DefaultSelector() as selector:
                    selector.register(process.stdout, selectors.EVENT_READ)
                    while time.monotonic() < deadline and not eof:
                        if selector.select(0.1):
                            chunk = os.read(process.stdout.fileno(), 65536)
                            eof = not chunk
                            data += chunk
                self.assertIn(b"GRANDCHILD-STARTED", data)
                self.assertTrue(eof, "grandchild still holds inherited stdout")
            finally:
                for process in children:
                    # Test owns these exact sessions, including on assertion failure.
                    try:
                        os.killpg(process.pid, 9)
                    except ProcessLookupError:
                        pass
                    process.wait(timeout=5)
                    process.stdout.close()

    def test_isolated_origin_overrides_ambient_deployment_names(self):
        expected = dict(FN2_ORIGIN_LINEAGE="711", FN2_ORIGIN_DOMAIN="712",
                        FN2_ORIGIN_INCARNATION="1", FN2_HISTORY_ID="713",
                        FN2_HISTORY_INCARNATION="1")
        ambient = {name: "wrong-deployment" for name in expected}
        ambient.update(FN2_KILL_AT="1", FN2_STORAGE_FAULT_MODEL="broad",
                       FN_ACL2="/qualified/launcher")
        with mock.patch.dict(campaign.os.environ, ambient):
            actual = campaign.environment()
        self.assertEqual({name: actual[name] for name in expected}, expected)
        self.assertEqual(actual["FN2_STORAGE_FAULT_MODEL"], "crash-only")
        self.assertNotIn("FN2_KILL_AT", actual)
        self.assertEqual(actual["FN_ACL2"], "/qualified/launcher")

    def test_crossing_articles_reject_a_previous_article_reply(self):
        first = campaign.crossing_article("<native-append-fetch-0@example.invalid>")
        second = campaign.crossing_article("<native-append-fetch-1@example.invalid>", body_variant=1)
        self.assertEqual(len(first), 6144)
        self.assertEqual(len(second), 6144)
        self.assertNotEqual(first, second)
        self.assertNotEqual(first[4096:], second[4096:])
        # Preserve the correct identity/header but substitute the other
        # article's later extent: this must not pass the restart oracle.
        wrong_tail = second[:4096] + first[4096:]
        with self.assertRaises(AssertionError):
            campaign.exact_fetch(dict(outcome="accepted", article_hex=wrong_tail.hex(),
                                      octets=len(wrong_tail)), second)
        for article in (first, second):
            self.assertIn(b"\r\n.", article)
            self.assertTrue(article.endswith(b"\r\n"))
        stale = dict(outcome="accepted", article_hex=first.hex(), octets=len(first))
        with self.assertRaises(AssertionError):
            campaign.exact_fetch(stale, second)

    def test_full_binary_article_and_changed_reply_controls(self):
        article = b"Header: exact\r\n\r\n\x00\xff.dot\r\n"
        good = dict(outcome="accepted", article_hex=article.hex(), octets=len(article))
        self.assertEqual(campaign.exact_fetch(good, article), article)
        for changed in (
            dict(good, article_hex=article[:-1].hex()),
            dict(good, article_hex=(article[:-1] + b"x").hex()),
            dict(good, octets=len(article) + 1),
            dict(outcome="refused"),
        ):
            with self.assertRaises(AssertionError):
                campaign.exact_fetch(changed, article)


if __name__ == "__main__":
    unittest.main()
