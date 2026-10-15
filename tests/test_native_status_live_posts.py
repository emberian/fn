"""Live `operator status' after live POSTs (PKT-878, PRF-361, lane health-truth-status).

The fitness soak (planning/evidence/fitness-2026-09-28.md, f1) saw the live
`status' take 10.1 s and exit 3 (uncertain: the control reply deadline passed)
in 7 of 8 samples on a 100k store under 16 clients, while `health' on the
same owner answered at once.  The cause is the reclaim line's classes:
books/store-reclaim-holders.lisp asked `fn-rcl-verdict-heldp' of the Store's
whole verdict list once per article, and that list gains one :absent entry
per acceptance since the open, so the render was O(articles x live
acceptances): 0.03 s at V = 0, 10.8 s at V = 5,000 and 50.6 s at V = 20,000
over 101,274 articles (hbox, planning/evidence/health-truth-status-2026-09-28.md).
The counts now ask it of the held verdicts only (`fn-rcl-held-verdicts').

The case (FN_NATIVE_DEVELOPER_HOST or build/fn-host-developer is the image;
no fixture: format changes do not strand it):

* `store init' a fresh store; the owner opens it; `status' answers, exit 0,
  twice (T0 the faster);
* FN_STATUS_POSTS (default 60,000) articles are POSTed over 8 connections,
  every article eventually 240 (bounded retry of the command-stage memory 440) -- each a live acceptance, so N = V, where the old render was
  N x V verdict steps (9.3 s more at 20,000 on hbox);
* `status' answers again, exit 0, twice (T1 the faster), its articles=N grown
  by the POSTs, and T1 - T0 stays under FN_STATUS_SLACK seconds (default 2.0).

Before this lane, on the images after the thread-stacks change, the same
20,000 articles also exhausted the owner's 1 MiB control-thread stack in the
per-article count (fn-rcl-summary-in, a frame per article): `status' exited 3
in 0.15 s and the owner stopped (`control request fault; owner stopped').
At 60,000 `health' did the same in books/native-health.lisp
fn-nh-forward-count (one frame per retention pin).  The counts are loops
now; the case asks `health' afterwards (never uncertain) and `status' once
more (exit 0: the owner is still there).

A difference of two timings on one owner, so the box's load largely cancels;
it prints one JSON line per observation.
"""

import json
import os
import re
import shutil
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

from tests.native_harness import ROOT, Node, native_image, requires

sys.path.insert(0, str(ROOT / "tools"))

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
POSTS = int(os.environ.get("FN_STATUS_POSTS", "60000"))
FLAGS = ["--profile", "default", "--max-transactions", "131072", "--max-history-octets", "128000000"]
SLACK = float(os.environ.get("FN_STATUS_SLACK", "2.0"))
CONNECTIONS = 8


def article(i):
    return ("From: status@example.invalid\r\nNewsgroups: fn.test\r\n"
            "Subject: status %d\r\nDate: Mon, 28 Sep 2026 06:00:00 +0000\r\n"
            "Message-ID: <hts-%06d@status.example.invalid>\r\n\r\n"
            % (i, i)).encode("ascii") + b"status line body\r\n" * 8


MEMORY_440 = b"440 posting not permitted now; the articles in flight fill the memory, try again later\r\n"
POST_RETRY_SECONDS = 60


def post_eventually(client, payload):
    "Retry only a command-stage transient refusal; never resend a submitted body."
    deadline = time.monotonic() + POST_RETRY_SECONDS
    retries = 0
    while True:
        first, final = client.post(payload)
        if final is not None or first != MEMORY_440:
            return (final or first).decode(errors="replace").strip(), retries
        if time.monotonic() >= deadline:
            raise TimeoutError("article never admitted after memory 440 within 60 seconds")
        retries += 1
        time.sleep(0.05)


class PostRetrySourceTests(unittest.TestCase):
    def test_memory_refusal_retries_the_same_article_until_accepted(self):
        client = mock.Mock()
        client.post.side_effect = [(MEMORY_440, None), (b"340 send article\r\n", b"240 article received OK\r\n")]
        with mock.patch(__name__ + ".time.sleep"):
            reply, count = post_eventually(client, b"same article")
        self.assertEqual(reply, "240 article received OK")
        self.assertEqual(count, 1)
        self.assertEqual(client.post.call_args_list, [mock.call(b"same article")] * 2)

    def test_permanent_refusal_and_post_body_outcome_are_never_retried(self):
        for first, final in [(b"440 posting disabled\r\n", None),
                             (b"340 send article\r\n", b"441 posting failed\r\n")]:
            client = mock.Mock()
            client.post.return_value = first, final
            post_eventually(client, b"article")
            client.post.assert_called_once()

    def test_continuous_memory_refusal_fails_the_eventual_acceptance_claim(self):
        client = mock.Mock()
        client.post.return_value = MEMORY_440, None
        with mock.patch(__name__ + ".time.monotonic", side_effect=[0, POST_RETRY_SECONDS]):
            with self.assertRaisesRegex(TimeoutError, "never admitted"):
                post_eventually(client, b"article")
        client.post.assert_called_once()


@requires(IMAGE)
class NativeStatusLivePostsTests(unittest.TestCase):

    def setUp(self):
        self.temp = Path(tempfile.mkdtemp(prefix="fn-status-live-"))
        self.node = Node(self, IMAGE, root=self.temp / "node")

    def tearDown(self):
        owner = self.node.process
        if owner is not None:
            self.node.stop(expect=None, grace=600)
            log = os.environ.get("FN_STATUS_OWNER_LOG")
            if log:
                with open(log, "ab") as handle:
                    handle.write(owner.stderr.since(0))
        if not os.environ.get("FN_STATUS_KEEP"):
            shutil.rmtree(self.temp, ignore_errors=True)

    def out(self, **rec):
        print(json.dumps(rec), flush=True)

    def status(self):
        started = time.monotonic()
        r = self.node.operator("status", timeout=300)
        seconds = time.monotonic() - started
        text = r.stdout.decode(errors="replace") + r.stderr.decode(errors="replace")
        found = re.search(r"\barticles=(\d+)", text)
        return r.returncode, seconds, int(found.group(1)) if found else None, text

    def poster(self, indices, replies, retried, errors):
        try:
            with self.node.session(timeout=60, greeting=None) as client:
                for i in indices:
                    reply, retries = post_eventually(client, article(i))
                    replies.append(reply)
                    if retries:
                        retried.append(retries)
        except Exception as error:
            errors.append(repr(error))

    def test_status_after_live_posts_stays_within_the_slack(self):
        init = self.node.store("init", *FLAGS, "fn.test", timeout=900)
        self.assertEqual(init.returncode, 0, init.stderr.decode(errors="replace")[-400:])
        started = time.monotonic()
        owner = self.node.start(timeout=1200)
        self.out(step="open", seconds=round(time.monotonic() - started, 2))

        before = [self.status() for _ in range(2)]
        for rc, s, n, text in before:
            self.out(step="status-before", exit=rc, seconds=round(s, 3), articles=n)
            self.assertEqual(rc, 0, text[-600:])
        t0 = min(s for _, s, _, _ in before)
        n0 = before[-1][2]

        replies, retried, errors = [], [], []
        threads = [threading.Thread(target=self.poster,
                                    args=(range(k, POSTS, CONNECTIONS), replies, retried, errors))
                   for k in range(CONNECTIONS)]
        started = time.monotonic()
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        accepted = sum(1 for r in replies if r.startswith("240"))
        self.out(step="posts", posted=len(replies), accepted=accepted,
                 retries=sum(retried), errors=errors,
                 seconds=round(time.monotonic() - started, 1),
                 other=sorted(set(r for r in replies if not r.startswith("240")))[:5])
        self.assertEqual(errors, [])
        self.assertEqual(len(replies), POSTS)
        self.assertEqual(accepted, POSTS)

        after = [self.status() for _ in range(2)]
        for rc, s, n, text in after:
            self.out(step="status-after", exit=rc, seconds=round(s, 3), articles=n)
            self.assertEqual(rc, 0, text[-600:])
        t1 = min(s for _, s, _, _ in after)
        health = self.node.operator("health", timeout=300)
        self.out(step="health-after", exit=health.returncode,
                 head=health.stdout.decode(errors="replace").splitlines()[:1],
                 err=health.stderr.decode(errors="replace")[-300:])
        self.assertNotEqual(health.returncode, 3,
                            (health.stdout + health.stderr).decode(errors="replace")[-600:])
        again = self.status()
        self.out(step="status-after-health", exit=again[0], seconds=round(again[1], 3))
        self.assertEqual(again[0], 0, again[3][-600:])
        self.assertIsNone(owner.poll(), "the owner stopped")
        self.assertEqual(after[-1][2], n0 + POSTS)
        self.out(step="verdict", t0=round(t0, 3), t1=round(t1, 3),
                 growth=round(t1 - t0, 3), slack=SLACK)
        self.assertLess(t1 - t0, SLACK,
                        "status grew %.2f s after %d live POSTs" % (t1 - t0, POSTS))


if __name__ == "__main__":
    unittest.main()
