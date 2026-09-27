"""The header limits are the store profile's (PRF-230, STO-030, SCN-156).

A store initialised with max-header-fields 1000 accepts a 900-field POST
(and serves it back) and a 1,000-field one, and refuses a 1,001-field one
with the 441 line naming the profile field; the default profile admits 64
fields and refuses the 65th, and 900, by the same name, and a header of 258
physical lines by the lines limit's name.  The ACL2 side is
books/article-header-limits.lisp (fn-article-census-refusal-is-the-parse)
and books/injection.lisp (fn-inj-decide); this is the measurement that the
image wires the opened profile's limits into the served POST.
"""
import os
from pathlib import Path
import select
import socket
import subprocess
import tempfile
import time
import unittest


ROOT = Path(__file__).resolve().parent.parent


def image():
    """The image under test: FN_NATIVE_HOST, else the developer image."""
    named = os.environ.get("FN_NATIVE_HOST")
    if named:
        return Path(named)
    return Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST",
                               ROOT / "build" / "fn-host-developer"))


IMAGE = image()
SKIP_REASON = ("no native image at {}: build one with tools/build_native_host.sh "
               "(FN_NATIVE_PROFILE=developer) or name one with FN_NATIVE_HOST or "
               "FN_NATIVE_DEVELOPER_HOST".format(IMAGE))


def environment():
    env = dict(os.environ)
    env["ACL2_CUSTOMIZATION"] = "NONE"
    env.pop("ACL2_SYSTEM_BOOKS", None)
    for name in ("FN_HOST", "FN_NATIVE_CONTROL_TEST_STOP",
                 "FN_NATIVE_CONTROL_FAULT", "FN_NATIVE_POST_FAULT",
                 "FN_NATIVE_OWNER_TEST_SIGTERM",
                 "FN_NATIVE_OWNER_TEST_PAUSE_CLEANUP",
                 "FN_NATIVE_OWNER_TEST_PAUSE_BEFORE_LISTEN",
                 "FN_NATIVE_FEED_TEST_STOP_AFTER_SENT"):
        env.pop(name, None)
    return env


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0))
        return probe.getsockname()[1]



FIELDS_LINE = (b"441 posting failed; the header has more fields than the "
               b"profile's max-header-fields")


def article(total_fields, message_id):
    """An article of exactly TOTAL_FIELDS header fields (the four mandatory
    ones and TOTAL_FIELDS - 4 distinct X- fields)."""
    lines = [b"From: author@example.invalid", b"Newsgroups: fn.test",
             b"Subject: header limits",
             b"Message-ID: " + message_id.encode("ascii")]
    lines += [b"X-Field-%04d: value %d" % (i, i) for i in range(total_fields - 4)]
    return b"\r\n".join(lines) + b"\r\n\r\nbody\r\n"


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK), SKIP_REASON)
class NativeHeaderLimitsTests(unittest.TestCase):
    """PRF-230, STO-030, SCN-156: the header limits are the profile's."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-header-limits-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.store = self.root / "store"
        self.port = free_port()

    def image(self, *words, timeout=180):
        return subprocess.run([str(IMAGE), "--fn"] + list(words), cwd=ROOT,
                              env=environment(), stdout=subprocess.PIPE,
                              stderr=subprocess.PIPE, timeout=timeout, check=False)

    def init(self, *flags):
        result = self.image("store", str(self.store), "init", *flags, "fn.test")
        self.assertEqual(result.returncode, 0, result.stderr.decode())

    def start(self):
        config = self.root / "fn.toml"
        config.write_text(
            "[store]\npath = \"{}\"\n"
            "[listener]\nhost = \"127.0.0.1\"\nport = {}\n"
            "[control]\npath = \"{}\"\n".format(
                self.store, self.port, self.root / "control.sock"),
            encoding="ascii")
        process = subprocess.Popen(
            [str(IMAGE), "--fn", "operator", str(config), "run"], cwd=ROOT,
            env=environment(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            bufsize=0)
        self.addCleanup(self.stop, process)
        lines = []
        for _ in range(6):
            ready = select.select([process.stdout], [], [], 180)[0]
            self.assertTrue(ready, "the owner did not become ready: {}".format(lines))
            line = process.stdout.readline()
            lines.append(line)
            if line.startswith(b"LISTENING "):
                return process
            if process.poll() is not None:
                self.fail("owner exited: {} {}".format(
                    lines, process.stderr.read().decode("utf-8", "replace")))
        self.fail("no LISTENING line: {!r}".format(lines))

    @staticmethod
    def stop(process):
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=120)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()

    def post(self, octets, message_id):
        """POST OCTETS; return the reply and, on 240, the ARTICLE text."""
        with socket.create_connection(("127.0.0.1", self.port), timeout=120) as conn:
            stream = conn.makefile("rwb")
            self.assertTrue(stream.readline().startswith(b"200"))
            stream.write(b"POST\r\n")
            stream.flush()
            self.assertTrue(stream.readline().startswith(b"340"))
            stream.write(octets + b".\r\n")
            stream.flush()
            reply = stream.readline().rstrip(b"\r\n")
            served = b""
            if reply.startswith(b"240"):
                stream.write(b"ARTICLE " + message_id.encode("ascii") + b"\r\n")
                stream.flush()
                head = stream.readline()
                self.assertTrue(head.startswith(b"220"), head)
                while True:
                    line = stream.readline()
                    if line in (b".\r\n", b""):
                        break
                    served += line
            stream.write(b"QUIT\r\n")
            stream.flush()
            return reply, served

    def test_a_raised_profile_accepts_900_fields_and_refuses_1001_by_name(self):
        self.init("--max-header-fields", "1000", "--max-header-lines", "2000",
                  "--max-header-octets", "1048576")
        self.start()
        reply, served = self.post(article(900, "<f900@example.invalid>"),
                                  "<f900@example.invalid>")
        self.assertTrue(reply.startswith(b"240"), reply)
        header = served.split(b"\r\n\r\n", 1)[0]
        self.assertEqual(sum(1 for line in header.split(b"\r\n")
                             if line.startswith(b"X-Field-")), 896)
        reply, _ = self.post(article(1000, "<f1000@example.invalid>"),
                             "<f1000@example.invalid>")
        self.assertTrue(reply.startswith(b"240"), reply)
        reply, _ = self.post(article(1001, "<f1001@example.invalid>"),
                             "<f1001@example.invalid>")
        self.assertEqual(reply, FIELDS_LINE)

    def test_the_default_profile_is_unchanged(self):
        self.init()
        self.start()
        reply, _ = self.post(article(64, "<f64@example.invalid>"),
                             "<f64@example.invalid>")
        self.assertTrue(reply.startswith(b"240"), reply)
        for total in (65, 900):
            reply, _ = self.post(article(total, "<f%d@example.invalid>" % total),
                                 "<f%d@example.invalid>" % total)
            self.assertEqual(reply, FIELDS_LINE, total)
        # 257 physical lines (one field folded 256 times): the line limit.
        folded = (b"From: author@example.invalid\r\nNewsgroups: fn.test\r\n"
                  b"Subject: folded\r\nMessage-ID: <folded@example.invalid>\r\n"
                  b"X-Folded: x\r\n" + b"\tx\r\n" * 253 + b"\r\nbody\r\n")
        reply, _ = self.post(folded, "<folded@example.invalid>")
        self.assertEqual(reply, b"441 posting failed; the header has more lines "
                                b"than the profile's max-header-lines")


if __name__ == "__main__":
    unittest.main()
