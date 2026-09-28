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

The case, against a copy of a large store (opt-in: FN_STATUS_FIXTURE names a
store directory to copy, e.g. /tank/fn/scratch/fixtures/syn100k-2k/store on
hbox; FN_NATIVE_DEVELOPER_HOST or build/fn-host-developer is the image):

* the owner opens the copy; `status' answers, exit 0, twice (T0 the faster);
* FN_STATUS_POSTS (default 3,000) articles are POSTed over 8 connections,
  every one 240;
* `status' answers again, exit 0, twice (T1 the faster), its articles=N grown
  by the POSTs, and T1 - T0 stays under FN_STATUS_SLACK seconds (default 2.0;
  before the fix the same step added ~6 s at N = 100k).

A difference of two timings on one owner, so the box's load largely cancels;
it prints one JSON line per observation.
"""

import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "tools"))
from tests.native_process import wait_for_announcement  # noqa: E402
from tools import msgid_measure as m  # noqa: E402
import native_env  # noqa: E402

FIXTURE = os.environ.get("FN_STATUS_FIXTURE")
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
POSTS = int(os.environ.get("FN_STATUS_POSTS", "3000"))
SLACK = float(os.environ.get("FN_STATUS_SLACK", "2.0"))
CONNECTIONS = 8


def article(i):
    return ("From: status@example.invalid\r\nNewsgroups: fn.test\r\n"
            "Subject: status %d\r\nDate: Mon, 28 Sep 2026 06:00:00 +0000\r\n"
            "Message-ID: <hts-%06d@status.example.invalid>\r\n\r\n"
            % (i, i)).encode("ascii") + b"status line body\r\n" * 8


@unittest.skipUnless(FIXTURE and Path(FIXTURE).is_dir() and os.access(IMAGE, os.X_OK),
                     "FN_STATUS_FIXTURE (a store to copy) and the developer image")
class NativeStatusLivePostsTests(unittest.TestCase):

    def setUp(self):
        self.temp = Path(tempfile.mkdtemp(prefix="fn-status-live-"))
        self.env = native_env.harness_store_env(dict(os.environ, ACL2_CUSTOMIZATION="NONE"))
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_HOST", None)
        self.owner = None

    def tearDown(self):
        if self.owner and self.owner.poll() is None:
            self.owner.send_signal(signal.SIGTERM)
            try:
                self.owner.wait(timeout=600)
            except subprocess.TimeoutExpired:
                self.owner.kill()
                self.owner.wait(timeout=60)
        if self.owner:
            self.owner.stdout.close()
        shutil.rmtree(self.temp, ignore_errors=True)

    def out(self, **rec):
        print(json.dumps(rec), flush=True)

    def invoke(self, *words, timeout=900):
        return subprocess.run([str(IMAGE), "--fn", *map(str, words)], cwd=str(ROOT),
                              env=self.env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              timeout=timeout, check=False)

    def status(self, cfg):
        started = time.monotonic()
        r = self.invoke("operator", cfg, "status", timeout=300)
        seconds = time.monotonic() - started
        text = r.stdout.decode(errors="replace")
        found = re.search(r"\barticles=(\d+)", text)
        return r.returncode, seconds, int(found.group(1)) if found else None, text

    def poster(self, port, indices, replies):
        c = m.Conn(port)
        try:
            for i in indices:
                r = c.line("POST")
                if not r.startswith(b"340"):
                    replies.append(r.decode(errors="replace").strip())
                    continue
                c.stream.write(article(i) + b".\r\n")
                replies.append(c.readline().decode(errors="replace").strip())
        finally:
            c.close()

    def test_status_after_live_posts_stays_within_the_slack(self):
        store = self.temp / "store"
        subprocess.run(["cp", "-a", "--reflink=auto", FIXTURE, str(store)], check=True)
        lock = store / "writer.lock"
        lock.touch()
        lock.chmod(0o600)
        rebind = self.invoke("store", store, "rebind-filesystem")
        self.assertEqual(rebind.returncode, 0, rebind.stderr.decode(errors="replace")[-400:])
        port = m.free_port()
        cfg = self.temp / "fn.toml"
        cfg.write_text('[store]\npath = "%s"\n[listener]\nhost = "127.0.0.1"\nport = %d\n'
                       '[control]\npath = "%s"\n' % (store, port, self.temp / "c.sock"))
        started = time.monotonic()
        self.owner = subprocess.Popen([str(IMAGE), "--fn", "operator", str(cfg), "run"],
                                      cwd=str(ROOT), env=self.env, stdout=subprocess.PIPE,
                                      stderr=subprocess.DEVNULL)
        wait_for_announcement(self.owner, b"LISTENING ", timeout=1200)
        self.out(step="open", seconds=round(time.monotonic() - started, 2))

        before = [self.status(cfg) for _ in range(2)]
        for rc, s, n, text in before:
            self.out(step="status-before", exit=rc, seconds=round(s, 3), articles=n)
            self.assertEqual(rc, 0, text[-600:])
        t0 = min(s for _, s, _, _ in before)
        n0 = before[-1][2]

        replies = []
        threads = [threading.Thread(target=self.poster,
                                    args=(port, range(k, POSTS, CONNECTIONS), replies))
                   for k in range(CONNECTIONS)]
        started = time.monotonic()
        for t in threads:
            t.start()
        for t in threads:
            t.join()
        accepted = sum(1 for r in replies if r.startswith("240"))
        self.out(step="posts", posted=len(replies), accepted=accepted,
                 seconds=round(time.monotonic() - started, 1),
                 other=sorted(set(r for r in replies if not r.startswith("240")))[:5])
        self.assertEqual(accepted, POSTS)

        after = [self.status(cfg) for _ in range(2)]
        for rc, s, n, text in after:
            self.out(step="status-after", exit=rc, seconds=round(s, 3), articles=n)
            self.assertEqual(rc, 0, text[-600:])
        t1 = min(s for _, s, _, _ in after)
        self.assertEqual(after[-1][2], n0 + POSTS)
        self.out(step="verdict", t0=round(t0, 3), t1=round(t1, 3),
                 growth=round(t1 - t0, 3), slack=SLACK)
        self.assertLess(t1 - t0, SLACK,
                        "status grew %.2f s after %d live POSTs" % (t1 - t0, POSTS))


if __name__ == "__main__":
    unittest.main()
