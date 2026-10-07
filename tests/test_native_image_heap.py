"""The 128 MB bar, measured on the production image (ruling 7).

128 MB counts everything resident (VmRSS) for the whole node process.  This
module drives the production image through the reference workload "nmem3-clean"
and asserts the bar:

* a fresh store (the small preset's limits, the flags N's nmem3 driver and
  E3's m3.py init with: --profile development --max-transactions 16384
  --max-history-octets 8388608 --max-record-octets 196608
  --max-groups-per-article 16 --max-open-suffix 128, groups fn.letters and
  fn.test);
* 1,000 POSTs of 2,048 octets;
* 32 idle connections opened (8, then 24 more) and closed;
* about 20 s idle after the close;
* VmRSS of the owner process then is at most 128 MiB.

The launch shape is the shipped one: the saved launcher's own SBCL options
(tools/build_native_host.sh: --tls-limit 16384, the control stack
books/heap-reservation.lisp decides) with SBCL_USER_ARGS "--dynamic-space-size
1068MB --tls-limit 16384" after them, as the workload's drivers run it.  The
image is FN_NATIVE_HOST, the one that ships.

A measurement gate that tracks the bar, not a test to make green: it is red on
an image that rests above 128 MiB, and the bar is never loosened to pass.  It
prints one FN_IMAGE_HEAP line of json (MB; the image, the launch args, the
posts).  Linux /proc only; FN_RUN_IMAGE_HEAP=1 runs it.
"""
import json
import os
import re
import time
import unittest
from pathlib import Path

from tests.native_harness import Client, Node, EXIT, executable, native_image

IMAGE = native_image("FN_NATIVE_HOST")
BAR_MIB = 128
POSTS = 1000
ARTICLE_OCTETS = 2048
IDLE_CONNECTIONS = (8, 24)
IDLE_SECONDS = 20
SBCL_USER_ARGS = "--dynamic-space-size 1068MB --tls-limit 16384"
INIT_FLAGS = ("--profile", "development", "--max-transactions", "16384",
              "--max-history-octets", "8388608", "--max-record-octets", "196608",
              "--max-groups-per-article", "16", "--max-open-suffix", "128")
LINE = b"0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789abcdef\r\n"


def article(i, octets=ARTICLE_OCTETS):
    """An article of OCTETS octets: the fixed header, then 78-character body lines."""
    head = ("From: heap@example.invalid\r\nNewsgroups: fn.test\r\nSubject: heap %d\r\n"
            "Date: Thu, 24 Sep 2026 12:00:00 +0000\r\n"
            "Message-ID: <heap-%06d@example.invalid>\r\n\r\n" % (i, i)).encode("ascii")
    need = octets - len(head)
    body = LINE * (need // len(LINE))
    rest = need - len(body)
    if rest >= 2:
        body += LINE[:rest - 2] + b"\r\n"
    return head + body


def status_kib(pid):
    text = Path("/proc/%d/status" % pid).read_text()
    return {key: int(re.search(key + r":\s+(\d+) kB", text).group(1))
            for key in ("VmRSS", "VmHWM", "RssAnon", "RssFile")}


def mb(kib):
    return round(kib / 1024, 1)


@unittest.skipUnless(os.environ.get("FN_RUN_IMAGE_HEAP") == "1",
                     "FN_RUN_IMAGE_HEAP=1 runs the 128 MB bar's measurement")
@unittest.skipUnless(os.path.isdir("/proc/self"), "needs Linux /proc")
class ImageHeapBarTests(unittest.TestCase):
    def test_nmem3_clean_resident_set_is_within_the_bar(self):
        if not executable(IMAGE):
            self.skipTest("needs the production image %s" % IMAGE)
        env = {"SBCL_USER_ARGS": SBCL_USER_ARGS}
        node = Node(self, IMAGE, env=env)
        node.operator("init", *INIT_FLAGS, "fn.letters", "fn.test", env=env, timeout=600,
                      expect=EXIT.OK)
        owner = node.start(env=env, timeout=900)
        time.sleep(3)
        pid = owner.pid
        try:
            with Client(node.port, timeout=120) as c:
                for i in range(POSTS):
                    first, final = c.post(article(i))
                    self.assertTrue(first.startswith(b"340") and final.startswith(b"240"),
                                    (i, first, final))
            held = []
            for count in IDLE_CONNECTIONS:
                held.extend(Client(node.port, timeout=120, greeting=None) for _ in range(count))
                time.sleep(2)
            # The shipped node refuses connections past its limit with a 400
            # greeting; the workload still opens them, as m3.py and nmem3.py do.
            admitted = sum(1 for c in held if c.greeting[:3] == b"200")
            for c in held:
                c.close()
            time.sleep(IDLE_SECONDS)
            sample = status_kib(pid)
        finally:
            node.stop(expect=None, grace=120)
        line = {"vmrss": mb(sample["VmRSS"]), "rssanon": mb(sample["RssAnon"]),
                "rssfile": mb(sample["RssFile"]), "vmhwm": mb(sample["VmHWM"]),
                "posts": POSTS, "connections": len(held), "admitted": admitted, "image": str(IMAGE),
                "launch": "{} --fn operator {} run".format(IMAGE, node.config),
                "sbcl_user_args": SBCL_USER_ARGS, "bar_mb": BAR_MIB * 1.0,
                "workload": "nmem3-clean"}
        print("FN_IMAGE_HEAP " + json.dumps(line), flush=True)
        self.assertLessEqual(sample["VmRSS"], BAR_MIB * 1024,
                             "VmRSS %.1f MB after %d POSTs, 32 idle connections closed and "
                             "%d s idle exceeds the %d MiB bar (ruling 7)"
                             % (mb(sample["VmRSS"]), POSTS, IDLE_SECONDS, BAR_MIB))


if __name__ == "__main__":
    unittest.main()
