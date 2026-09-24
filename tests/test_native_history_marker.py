"""The committed-history boundary (books/store-history-marker), natively.

`committed-history.json` holds the committed-record count.  The host writes
it after each record's transaction-directory barrier and before completion
(`fnn-mark-committed`), and every open compares it with the length of the
record list replay is handed (`fnn-check-history-marker`, in `fnn-recover`).

The witnesses (developer image, `store ROOT ...`):

* two posts, the newest transaction file deleted: the open refuses, naming
  `history-short-of-marker` with the marker and the record count;
* a post whose reservation is burned (a known abort before publication, and
  a process killed after its reservation): the open admits the store and the
  next post commits;
* a store without a marker (every store written before it) opens, and the
  next commit writes one;
* an allocation-frontier frame in the marker's place is `marker-damaged`;
* SIGKILL and EIO at every marker cut (ACL2's `fn-hm-marker-cut-names`):
  the store recovers, the next post commits, and a lost newest file is
  refused afterwards.
"""

import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

from tests.campaign import native_cuts

ROOT = Path(__file__).resolve().parent.parent
IMAGE = Path(os.environ.get("FN_NATIVE_DEVELOPER_HOST", ROOT / "build" / "fn-host-developer"))
EXIT_OK, EXIT_REFUSED, EXIT_UNCERTAIN, EXIT_FAULT = 0, 1, 3, 4
MARKER_CUTS = ("marker-created", "marker-written", "marker-staged-durable",
               "marker-replaced", "marker-durable")


class HistoryMarkerSourceTests(unittest.TestCase):
    def test_the_host_calls_acl2s_decisions_at_every_publish_site(self):
        model = (ROOT / "books" / "store-history-marker.lisp").read_text(encoding="ascii")
        io = (ROOT / "host" / "native" / "io.lisp").read_text(encoding="ascii")
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="ascii")
        table = native_cuts.host_function(model, "fn-hm-marker-cut-names")
        mark = native_cuts.host_function(io, "fnn-mark-committed")
        for cut in MARKER_CUTS:
            self.assertIn('"{}"'.format(cut), table)
            self.assertIn(":" + cut, mark)
        self.assertIn("(fnn-core 'fn-hm-after-commit sequence)", mark)
        check = native_cuts.host_function(io, "fnn-check-history-marker")
        self.assertIn("'fn-hm-open-verdict", check)
        recover = native_cuts.host_function(io, "fnn-recover")
        self.assertIn("(fnn-check-history-marker store (length records))", recover)
        # Every caller of fnn-finish marks the commit first.
        for text, name in ((io, "fnn-command-post"), (io, "fnn-command-probe"),
                           (owner, "fnn-owner-publish-prepared")):
            body = native_cuts.host_function(text, name)
            self.assertLess(body.index("(fnn-mark-committed store"), body.index("(fnn-finish store)"),
                            name)
        self.assertEqual(len(re.findall(r"\(fnn-finish store\)", io + owner)), 3)


@unittest.skipUnless(IMAGE.is_file() and os.access(IMAGE, os.X_OK),
                     "build/fn-host-developer is required")
class NativeHistoryMarkerTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fn-native-marker-")
        self.base = Path(self.temporary.name)
        self.payload = self.base / "payload"
        self.payload.write_bytes(b"committed history marker\r\n")
        self.env = dict(os.environ)
        self.env["ACL2_CUSTOMIZATION"] = "NONE"
        self.env.pop("ACL2_SYSTEM_BOOKS", None)
        self.env.pop("FN_NATIVE_POST_FAULT", None)
        self.env.pop("FN_NATIVE_RECOVERY_FAULT", None)
        self.posts = 0

    def tearDown(self):
        self.temporary.cleanup()

    def native(self, *args, expected=EXIT_OK, env=None):
        result = subprocess.run(
            [str(IMAGE), "--fn", *map(str, args)], cwd=ROOT, env=env or self.env,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60, check=False, text=True)
        if expected is not None:
            self.assertEqual(result.returncode, expected,
                             "native {} returned {}\nstdout={}\nstderr={}".format(
                                 args, result.returncode, result.stdout, result.stderr))
        return result

    def post(self, store, expected=EXIT_OK, inject="-", env=None):
        self.posts += 1
        return self.native("store", store, "post",
                           "<marker-{}@example.invalid>".format(self.posts),
                           self.payload, "-", inject, "fn.letters",
                           expected=expected, env=env)

    def store(self, name="store", posts=2):
        store = self.base / name
        self.native("store", store, "init", "fn.letters")
        for _ in range(posts):
            self.post(store)
        return store

    def newest(self, store):
        return sorted((store / "transactions").iterdir())[-1]

    def assert_lost_newest_refused(self, store):
        count = len(list((store / "transactions").iterdir()))
        self.newest(store).unlink()
        refused = self.native("store", store, "recover", expected=EXIT_FAULT)
        self.assertIn("history-short-of-marker", refused.stderr)
        self.assertIn("marker={} records={}".format(count, count - 1), refused.stderr)

    def test_a_lost_newest_transaction_file_is_refused_with_the_reason(self):
        store = self.store()
        self.assertTrue((store / "committed-history.json").is_file())
        self.native("store", store, "recover")
        self.assert_lost_newest_refused(store)
        # The refusal writes nothing: it is refused again.
        again = self.native("store", store, "recover", expected=EXIT_FAULT)
        self.assertIn("history-short-of-marker", again.stderr)

    def test_a_burned_reservation_is_not_a_lost_record(self):
        store = self.store()
        marker = (store / "committed-history.json").read_bytes()
        frontier = (store / "allocation-frontier.json").read_bytes()
        # A known abort before publication burns the reservation.
        self.post(store, expected=EXIT_REFUSED, inject="prepublish")
        # A process killed after its reservation burns another.
        env = dict(self.env, FN_NATIVE_POST_FAULT="record-staged-durable:kill")
        self.post(store, expected=None, env=env)
        self.assertNotEqual((store / "allocation-frontier.json").read_bytes(), frontier)
        self.assertEqual((store / "committed-history.json").read_bytes(), marker)
        self.assertEqual(len(list((store / "transactions").iterdir())), 2)
        self.native("store", store, "recover")
        committed = self.post(store)
        self.assertIn("committed sequence=2", committed.stdout)
        self.assert_lost_newest_refused(store)

    def test_a_store_without_a_marker_opens_and_the_next_commit_marks_it(self):
        store = self.store()
        (store / "committed-history.json").unlink()
        self.native("store", store, "recover")
        self.post(store)
        self.assertTrue((store / "committed-history.json").is_file())
        self.assert_lost_newest_refused(store)

    def test_a_frontier_frame_is_not_a_marker(self):
        store = self.store()
        shutil.copyfile(store / "allocation-frontier.json", store / "committed-history.json")
        refused = self.native("store", store, "recover", expected=EXIT_FAULT)
        self.assertIn("marker-damaged", refused.stderr)

    def test_every_marker_cut_recovers_and_keeps_detecting(self):
        for cut in MARKER_CUTS:
            for action, expected in (("kill", None), ("eio", EXIT_UNCERTAIN)):
                with self.subTest(cut=cut, action=action):
                    store = self.store("{}-{}".format(cut, action), posts=1)
                    env = dict(self.env, FN_NATIVE_POST_FAULT="{}:{}".format(cut, action))
                    faulted = self.post(store, expected=expected, env=env)
                    if action == "kill":
                        self.assertLess(faulted.returncode, 0, faulted.stderr)
                    # The record is durable at every marker cut.
                    self.assertEqual(len(list((store / "transactions").iterdir())), 2)
                    self.native("store", store, "recover")
                    self.post(store)
                    self.assert_lost_newest_refused(store)


if __name__ == "__main__":
    unittest.main()
