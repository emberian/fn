"""Opt-in native case: a store of another format is refused at open by name (D34).

A store is synthesized by tests/foreign_format_store.py: a fresh store made
by the image under test whose config.json is replaced by a profile frame
naming another format word (literal octets pinned to ACL2 by
tests/acl2/store-profile-open-tests.lisp).  Every open refuses it by ACL2's
line, "not an fn store of this release: redeploy fresh", exit 1 (specs/
host.md "CLI exit codes": a refusal), never the generic fault ("ACL2
rejected durable configuration frame", exit 4): `store ROOT recover`,
`store ROOT status`, `store ROOT inspect`, `store ROOT checkpoint`,
`operator CONFIG status`, `operator CONFIG health` and `operator CONFIG run`
(the owner's start).  The open is books/store-profile-open.lisp
fn-spo-config-open, which host/native/io.lisp fnn-metadata-config-decode
calls through host/store-host.lisp fn-store-metadata-config-open from
fnn-load-config; the line is fn-spo-refusal-text.  Theorem:
fn-spo-config-open-store-format-is-exactly-a-foreign-frame.  The refused
store's files are unchanged.  The control: the same store with its own
config.json opens.

Run: FN_NATIVE_HOST=<launcher> python3 -m unittest -v tests.test_native_foreign_format_open
"""

import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from tests import foreign_format_store as foreign

ROOT = Path(__file__).resolve().parent.parent
IMAGE_TEXT = os.environ.get("FN_NATIVE_HOST")
IMAGE = (Path(IMAGE_TEXT) if IMAGE_TEXT else
         next((p for p in (ROOT / "build" / "fn-host-developer", ROOT / "build" / "fn-host")
               if p.is_file()), None))
READY = bool(IMAGE is not None and IMAGE.is_file() and os.access(IMAGE, os.X_OK))
REFUSED = 1
GENERIC = "ACL2 rejected durable configuration frame"


def tree(root):
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(Path(root).rglob("*"))
            if p.is_file() and p.name != "writer.lock"}


@unittest.skipUnless(READY, "set FN_NATIVE_HOST to a saved native image")
class ForeignFormatOpenTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="fn-foreign-format-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        self.env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
        self.env.pop("ACL2_SYSTEM_BOOKS", None)

    def fn(self, *args):
        r = subprocess.run([str(IMAGE), "--fn", *map(str, args)], cwd=ROOT, env=self.env,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=300)
        out = (r.stdout + r.stderr).decode("utf-8", "replace")
        print("$ fn", *args, "->", r.returncode, "\n" + out.strip())
        return r.returncode, out

    def test_a_store_of_another_format_is_refused_by_name(self):
        store, config, _ = foreign.make_store(IMAGE, self.tmp, self.env)
        before = tree(store)
        for args in (("store", store, "recover"),
                     ("store", store, "status"),
                     ("store", store, "inspect", "<another-format@example.invalid>"),
                     ("store", store, "checkpoint"),
                     ("operator", config, "status"),
                     ("operator", config, "health"),
                     ("operator", config, "run")):
            with self.subTest(args=args[0:1] + args[2:]):
                rc, out = self.fn(*args)
                self.assertEqual(rc, REFUSED, out)
                self.assertIn(foreign.LINE, out)
                self.assertNotIn(GENERIC, out)
        self.assertEqual(tree(store), before)

    def test_the_same_store_with_its_own_profile_opens(self):
        # The control: the builder's store with the config.json this release
        # wrote put back opens.
        store, config, own = foreign.make_store(IMAGE, self.tmp, self.env)
        (store / "config.json").write_bytes(own)
        rc, out = self.fn("store", store, "recover")
        self.assertEqual(rc, 0, out)
        self.assertNotIn("open refused", out)
        rc, out = self.fn("operator", config, "status")
        self.assertEqual(rc, 0, out)


if __name__ == "__main__":
    unittest.main()
