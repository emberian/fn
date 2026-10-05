"""A fresh node started exactly as an installed node starts (smoke tier).

The decided-launch ruling (2026-10-04): every installed node is started
by packaging/fn.  In its installed layout the launcher runs the image's
heap probe (`heap -- operator CONFIG run`: books/heap-figure.lisp
fn-heap-decide over the store profile and this machine) and starts the
owner at that heap and control stack.  On dev at d5b0b9100 every such
start was refused ("cold startup refused: invalid runtime capture";
lane cold-start's fix, lane/cold-start@ae4e1cc95).  No native caught it,
because every native started the image at its saved 32000 MB.

Here a store made by a plain `init` is started through the installed
launcher (tests/native_harness.py installed_launcher, Node.launch).  The
owner must announce LISTENING, run at the probe's figure (read back from
its command line), answer GROUP 211 and a POST 240, serve the article,
and stop cleanly.  It runs on the production image (FN_NATIVE_HOST) and on
the developer image (FN_NATIVE_DEVELOPER_HOST).
"""
import os
from pathlib import Path
import re
import unittest

from tests.native_harness import (EXIT, Node, article, installed_launcher, native_image,
                                  run, environment)

IMAGES = [("production", native_image("FN_NATIVE_HOST")),
          ("developer", native_image("FN_NATIVE_DEVELOPER_HOST"))]
GROUP = "fn.test"


def executable(path):
    return path.is_file() and os.access(path, os.X_OK)


class InstalledStartTests(unittest.TestCase):
    def test_a_fresh_store_starts_as_installed_and_serves(self):
        ran = 0
        for label, image in IMAGES:
            if not executable(image):
                continue
            ran += 1
            with self.subTest(image=label):
                self.check(image)
        if not ran:
            self.skipTest("needs an image: FN_NATIVE_HOST or FN_NATIVE_DEVELOPER_HOST")

    def check(self, image):
        node = Node(self, image, name="installed-" + image.name)
        node.init(GROUP)
        launcher = installed_launcher(image)
        probe = run([launcher, "heap", "--", "operator", node.config, "run"],
                    env=environment({"FN_NATIVE_HOST": None}), text=True)
        figure = re.match(r"heap=(\d+) MB .*stack=(\d+) KB", probe.stdout.strip())
        self.assertIsNotNone(figure, (probe.returncode, probe.stdout, probe.stderr))
        owner = node.start()
        self.assertIsNone(owner.poll(), "the installed start exited")
        cmdline = Path("/proc/{}/cmdline".format(owner.pid))
        if cmdline.exists():
            words = cmdline.read_bytes().split(b"\0")
            sizes = [words[i + 1] for i, w in enumerate(words[:-1])
                     if w == b"--dynamic-space-size"]
            self.assertEqual(sizes[-1:], [figure.group(1).encode()],
                             "the owner does not run at the launcher's decided heap")
        message_id = "<installed-{}@example.invalid>".format(image.name)
        with node.session() as client:
            self.assertTrue(client.command(b"GROUP " + GROUP.encode()).startswith(b"211 "))
            first, final = client.post(article(message_id, groups=GROUP))
            self.assertTrue(first.startswith(b"340"), first)
            self.assertTrue(final is not None and final.startswith(b"240"), final)
            self.assertIsNotNone(client.article(message_id))
        node.stop(EXIT.OK)


if __name__ == "__main__":
    unittest.main()
