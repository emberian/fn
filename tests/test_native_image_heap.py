"""The small-preset memory guardrails, measured on the production image.

The 128 MB target is retired by ember's 2026-10-14 ruling.  This
module drives the production image through the reference workload "nmem3-clean"
and asserts the guardrails:

* a fresh store (the small preset's limits, the flags N's nmem3 driver and
  E3's m3.py init with: --profile development --max-transactions 16384
  --max-history-octets 8388608 --max-record-octets 196608
  --max-groups-per-article 16 --max-open-suffix 128, groups fn.letters and
  fn.test);
* 1,000 POSTs of 2,048 octets;
* 32 idle connections opened (8, then 24 more) and closed;
* about 20 s idle after the close;
* whole-process VmHWM over the workload is at most 249 MB, and the sampled
  RssAnon + RssShmem is at most 115 MB; the at-rest VmRSS is printed beside
  them and not judged.

The launch shape is the shipped one: the saved launcher's own SBCL options
(tools/build_native_host.sh: --tls-limit 16384, the control stack
books/heap-reservation.lisp decides) with SBCL_USER_ARGS "--dynamic-space-size
1068MB --tls-limit 16384" after them, as the workload's drivers run it.  The
image is FN_NATIVE_HOST, the one that ships.

A measurement gate against 50% growth from the baseline.  It prints one
FN_IMAGE_HEAP line of json (MB; the image, the launch args, the
posts).  Linux /proc only; FN_RUN_IMAGE_HEAP=1 runs it.
"""
import json
import os
import re
import time
import unittest
from pathlib import Path

from tests.native_harness import Client, Node, EXIT, executable, native_image
from tools.load.workloads import nmem3_clean

IMAGE = native_image("FN_NATIVE_HOST")
# ember, 2026-10-14: "stop grinding towards the memory bar ... set guardrails
# to avoid bloating more than 50% from our baseline ... say ok for where we're at".
# Baselines: whole-process VmHWM 166.3 MB; RssAnon + RssShmem 77,096 KiB.
GUARDRAIL_VMHWM_MB = 249
GUARDRAIL_ANON_SHMEM_KIB = 115 * 1024
# One definition of the reference workload: tools/load/workloads.json, "rss-small-filled".
_WORKLOAD = nmem3_clean()
POSTS = _WORKLOAD["posts"]
ARTICLE_OCTETS = _WORKLOAD["octets"]
IDLE_CONNECTIONS = _WORKLOAD["idle_connections"]
IDLE_SECONDS = _WORKLOAD["idle_seconds"]
SBCL_USER_ARGS = _WORKLOAD["sbcl_user_args"]
INIT_FLAGS = _WORKLOAD["init_flags"]
GROUPS = _WORKLOAD["groups"]
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
            for key in ("VmRSS", "VmHWM", "RssAnon", "RssFile", "RssShmem")}


def mb(kib):
    return round(kib / 1024, 1)


@unittest.skipUnless(os.environ.get("FN_RUN_IMAGE_HEAP") == "1",
                     "FN_RUN_IMAGE_HEAP=1 runs the memory guardrail measurement")
@unittest.skipUnless(os.path.isdir("/proc/self"), "needs Linux /proc")
class ImageHeapBarTests(unittest.TestCase):
    def test_nmem3_clean_resident_set_is_within_the_bar(self):
        if not executable(IMAGE):
            self.skipTest("needs the production image %s" % IMAGE)
        env = {"SBCL_USER_ARGS": SBCL_USER_ARGS}
        node = Node(self, IMAGE, env=env)
        node.operator("init", *INIT_FLAGS, *GROUPS, env=env, timeout=600,
                      expect=EXIT.OK)
        owner = node.start(env=env, timeout=900)
        time.sleep(_WORKLOAD["settle_s"])
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
                time.sleep(_WORKLOAD["step_settle_s"])
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
                "rssshmem": mb(sample["RssShmem"]),
                "rssanon_shmem": mb(sample["RssAnon"] + sample["RssShmem"]),
                "posts": POSTS, "connections": len(held), "admitted": admitted, "image": str(IMAGE),
                "launch": "{} --fn operator {} run".format(IMAGE, node.config),
                "sbcl_user_args": SBCL_USER_ARGS,
                "guardrail_vmhwm_mb": GUARDRAIL_VMHWM_MB,
                "guardrail_anon_shmem_kib": GUARDRAIL_ANON_SHMEM_KIB,
                "workload": "nmem3-clean", "judged": ["vmhwm", "rssanon_shmem"]}
        print("FN_IMAGE_HEAP " + json.dumps(line), flush=True)
        # Judge the unrounded /proc figures; VmRSS remains a printed measurement.
        self.assertLessEqual(sample["VmHWM"], GUARDRAIL_VMHWM_MB * 1024,
                             "VmHWM %.1f MB over the workload (%d POSTs, 32 idle connections, %d s idle; "
                             "at-rest VmRSS %.1f MB) exceeds the %d MB guardrail"
                             % (mb(sample["VmHWM"]), POSTS, IDLE_SECONDS, mb(sample["VmRSS"]),
                                GUARDRAIL_VMHWM_MB))
        self.assertLessEqual(sample["RssAnon"] + sample["RssShmem"], GUARDRAIL_ANON_SHMEM_KIB,
                             "RssAnon + RssShmem exceeds the guardrail: %r" % sample)


if __name__ == "__main__":
    unittest.main()
