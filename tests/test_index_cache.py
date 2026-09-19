"""Generation-bound index cache over a real recovered store (C1-09).

Every answer checked here comes from `fn-index-host-query`, which calls
`fn-nntp-index-cache-query` and nothing else.  The oracle is
`fn-index-host-fold`, the books/nntp.lisp enumeration run directly over the
same recovered archive.
"""
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)
from tools.run_store import Acl2Store, Store  # noqa: E402

PROMPT = b"ACL2 !>"
ALL_HIGH = 2147483647


def result_text(output):
    trimmed = output.strip()
    if not trimmed.endswith(PROMPT):
        raise RuntimeError("unexpected ACL2 result: {!r}".format(output))
    return trimmed[:-len(PROMPT)].strip().decode("ascii", "replace")


def parse_status(text):
    upper = text.upper()
    if upper not in (":OK", ":STALE", ":UNKNOWN"):
        raise RuntimeError("unexpected index-cache status: {}".format(text))
    return upper[1:].lower()


def parse_value(text):
    if text.upper() == "NIL":
        return []
    if text.isdigit():
        return int(text)
    if text.startswith("(") and text.endswith(")"):
        return [int(token) for token in text[1:-1].split()]
    raise RuntimeError("unexpected index-cache value: {}".format(text))


class IndexReader:
    """One ACL2 process holding a recovered snapshot plus the index cache."""

    def __init__(self, store_path):
        self.store = Store(store_path, writable=False)
        self.bridge = None
        try:
            self.store.acquire()
            self.bridge = Acl2Store()
            self.records = self.store.recover(self.bridge)
            self.bridge.call('(include-book "books/node")')
            self.bridge.call('(include-book "books/nntp")')
            self.bridge.call('(ld "host/reader-host.lisp" :ld-error-action :return'
                             ' :ld-error-triples t)')
            self.bridge.call('(ld "host/index-host.lisp" :ld-error-action :return'
                             ' :ld-error-triples t)', timeout=600)
            self.select()
        except BaseException:
            self.close()
            raise

    def select(self):
        """Selection/recovery: read the archive once, observe its digest once."""
        self.bridge.call("(fn-reader-use-store state)")
        self.bridge.call("(fn-index-host-observe state)")
        self.generation = len(self.records)

    def open_index(self, generation=None):
        generation = self.generation if generation is None else generation
        return result_text(
            self.bridge.call("(fn-index-host-open {} state)".format(generation),
                             timeout=600))

    def _read_answer(self):
        status = parse_status(result_text(self.bridge.call("(@ fn-index-status)")))
        value = parse_value(result_text(self.bridge.call("(@ fn-index-value)")))
        return status, value

    def query(self, kind, group, generation=None, low=1, high=ALL_HIGH, current="nil"):
        generation = self.generation if generation is None else generation
        self.bridge.call(
            '(fn-index-host-query {} :{} "{}" {} {} {} state)'.format(
                generation, kind, group, low, high, current), timeout=600)
        return self._read_answer()

    def fold(self, kind, group, low=1, high=ALL_HIGH, current="nil"):
        self.bridge.call(
            '(fn-index-host-fold :{} "{}" {} {} {} state)'.format(
                kind, group, low, high, current), timeout=600)
        return self._read_answer()

    def close(self):
        if self.bridge is not None:
            self.bridge.close()
            self.bridge = None
        self.store.close()


class IndexCacheTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="fn-index-cache-")
        cls.root = Path(cls.temporary.name)
        cls.store = cls.root / "store"
        cls.payload = cls.root / "payload"
        subprocess.run([sys.executable, "tools/run_store.py", "--store", str(cls.store),
                        "init"], cwd=ROOT, check=True, capture_output=True)
        cls.post("<one@example.invalid>",
                 b"Message-ID: <one@example.invalid>\r\n\r\none\r\n",
                 ("fn.letters", "fn.test"))
        cls.post("<two@example.invalid>",
                 b"Message-ID: <two@example.invalid>\r\n\r\ntwo\r\n",
                 ("fn.letters",))

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @classmethod
    def post(cls, msgid, payload, groups):
        cls.payload.write_bytes(payload)
        args = ["--message-id", msgid, "--payload", str(cls.payload)]
        for group in groups:
            args.extend(["--group", group])
        result = subprocess.run(
            [sys.executable, "tools/run_store.py", "--store", str(cls.store), "post",
             *args], cwd=ROOT, capture_output=True)
        if result.returncode != 0:
            raise AssertionError("post failed: {}".format(result.stderr))

    def test_index_answers_equal_the_fold_command_by_command(self):
        reader = IndexReader(self.store)
        try:
            self.assertEqual(reader.open_index(), ":READY")
            self.assertEqual(reader.generation, 2)
            for kind, group, extra in (("count", "fn.letters", {}),
                                       ("low", "fn.letters", {}),
                                       ("high", "fn.letters", {}),
                                       ("count", "fn.test", {}),
                                       ("low", "fn.test", {}),
                                       ("high", "fn.test", {}),
                                       ("range", "fn.letters", {}),
                                       ("range", "fn.test", {}),
                                       ("range", "fn.letters", {"low": 2, "high": 9}),
                                       ("next", "fn.letters", {"current": 1}),
                                       ("last", "fn.letters", {"current": 2}),
                                       ("count", "fn.absent", {})):
                status, value = reader.query(kind, group, **extra)
                self.assertEqual(status, "ok", (kind, group, extra))
                self.assertEqual((status, value), reader.fold(kind, group, **extra),
                                 (kind, group, extra))
            # Non-degenerate: fn.letters holds both articles, fn.test one.
            self.assertEqual(reader.query("count", "fn.letters")[1], 2)
            self.assertEqual(reader.query("count", "fn.test")[1], 1)
            self.assertEqual(reader.query("range", "fn.letters")[1], [1, 2])
            self.assertEqual(reader.query("range", "fn.test")[1], [1])
            self.assertEqual(reader.query("capabilities", "fn.letters")[0], "unknown")
        finally:
            reader.close()

    def test_forged_generation_is_refused_not_answered(self):
        reader = IndexReader(self.store)
        try:
            reader.open_index()
            truth = reader.query("count", "fn.letters")
            self.assertEqual(truth, ("ok", 2))
            for forged in (reader.generation + 1, reader.generation - 1, 0, 99):
                status, value = reader.query("count", "fn.letters", generation=forged)
                self.assertEqual(status, "stale", forged)
                self.assertEqual(value, [])
            # Refusal does not damage the cache: the true generation still answers.
            self.assertEqual(reader.query("count", "fn.letters"), truth)
        finally:
            reader.close()

    def test_post_between_two_reader_commands_gives_post_generation_truth(self):
        reader = IndexReader(self.store)
        try:
            reader.open_index()
            self.assertEqual(reader.query("count", "fn.letters"), ("ok", 2))
            self.assertEqual(reader.query("high", "fn.letters"), ("ok", 2))
        finally:
            reader.close()

        self.post("<three@example.invalid>",
                  b"Message-ID: <three@example.invalid>\r\n\r\nthree\r\n",
                  ("fn.letters",))

        reader = IndexReader(self.store)
        try:
            self.assertEqual(reader.generation, 3)
            # A cache opened at the pre-post generation is refused, never served.
            reader.open_index(generation=2)
            self.assertEqual(reader.query("count", "fn.letters")[0], "stale")
            # Re-opened at the observed generation it carries the new truth.
            reader.open_index()
            self.assertEqual(reader.query("count", "fn.letters"), ("ok", 3))
            self.assertEqual(reader.query("high", "fn.letters"), ("ok", 3))
            self.assertEqual(reader.query("range", "fn.letters"), ("ok", [1, 2, 3]))
            self.assertEqual(reader.query("count", "fn.letters"),
                             reader.fold("count", "fn.letters"))
            self.assertEqual(reader.query("range", "fn.letters"),
                             reader.fold("range", "fn.letters"))
        finally:
            reader.close()

    def test_configuration_digest_change_is_refused(self):
        """An index opened before a re-selection is refused by the digest test."""
        reader = IndexReader(self.store)
        try:
            reader.open_index()
            self.assertEqual(reader.query("count", "fn.letters")[0], "ok")
            # Forge the observed configuration digest: the cache no longer
            # matches what the host last observed, so it refuses.
            reader.bridge.call("(f-put-global 'fn-index-digest :forged state)")
            self.assertEqual(reader.query("count", "fn.letters")[0], "stale")
            # Re-observing the real archive restores the match.
            reader.bridge.call("(fn-index-host-observe state)")
            self.assertEqual(reader.query("count", "fn.letters")[0], "ok")
            # A cache that was never opened refuses rather than answering.
            reader.bridge.call("(f-put-global 'fn-index-cache nil state)")
            self.assertEqual(reader.query("count", "fn.letters")[0], "stale")
        finally:
            reader.close()


if __name__ == "__main__":
    unittest.main()
