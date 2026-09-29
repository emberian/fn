#!/usr/bin/env python3
"""Static fixtures (tools/fixtures.py): pinned SHA256SUMS and the `path` verb
consumers call before use; the glibc-floor runtime is one (PKT-727)."""
import contextlib
import hashlib
import io
import shutil
import tempfile
import unittest
import unittest.mock
from pathlib import Path

from tools import fixtures

ROOT = Path(__file__).resolve().parent.parent
FLOOR = "sbcl-floor-runtime-2.6.8"


def sha(octets):
    return hashlib.sha256(octets).hexdigest()


class StaticFixtureTests(unittest.TestCase):
    def setUp(self):
        self.root = Path(tempfile.mkdtemp(prefix="fn-fixtures-"))
        self.addCleanup(shutil.rmtree, self.root, True)
        where = self.root / FLOOR
        where.mkdir()
        (where / "sbcl").write_bytes(b"runtime")
        (where / "SHA256SUMS").write_text("{}  sbcl\n".format(sha(b"runtime")))
        self.pinned = sha((where / "SHA256SUMS").read_bytes())
        self.fixture = fixtures.Fixture(FLOOR, static=True, stores=(), sums_sha256=self.pinned)

    def path(self, name=FLOOR):
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            code = fixtures.main(["path", name, "--root", str(self.root)])
        return code, out.getvalue(), err.getvalue()

    def test_a_verified_fixture_prints_its_directory(self):
        self.assertEqual(fixtures.verify_fixture(self.fixture, self.root / FLOOR), [])
        registered = fixtures.BY_NAME[FLOOR]
        with unittest.mock.patch.dict(fixtures.BY_NAME, {FLOOR: self.fixture}):
            code, out, _ = self.path()
        self.assertEqual((code, out.strip()), (0, str(self.root / FLOOR)))
        self.assertTrue(registered.static)
        self.assertEqual(registered.stores, ())

    def test_rewritten_sums_matching_changed_files_fail_the_pin(self):
        where = self.root / FLOOR
        (where / "sbcl").write_bytes(b"another runtime")
        (where / "SHA256SUMS").write_text("{}  sbcl\n".format(sha(b"another runtime")))
        self.assertEqual(fixtures.verify_sums(where), [])
        bad = fixtures.verify_fixture(self.fixture, where)
        self.assertEqual(len(bad), 1)
        self.assertTrue(bad[0].startswith("SHA256SUMS (pinned"), bad)
        with unittest.mock.patch.dict(fixtures.BY_NAME, {FLOOR: self.fixture}):
            code, out, err = self.path()
        self.assertEqual((code, out), (1, ""))
        self.assertIn("pinned", err)

    def test_a_changed_file_and_an_absent_or_unknown_fixture_are_refused(self):
        (self.root / FLOOR / "sbcl").write_bytes(b"changed")
        self.assertEqual(fixtures.verify_fixture(self.fixture, self.root / FLOOR), ["sbcl"])
        with unittest.mock.patch.dict(fixtures.BY_NAME, {FLOOR: self.fixture}):
            self.assertEqual(self.path()[0], 1)
        self.assertEqual(self.path("no-such-fixture")[0], 2)
        with unittest.mock.patch.dict(fixtures.BY_NAME, {FLOOR: self.fixture}):
            shutil.rmtree(self.root / FLOOR)
            code, _, err = self.path()
        self.assertEqual(code, 1)
        self.assertIn("MISSING", err)

    def test_the_release_scripts_take_the_registered_runtime(self):
        for script in ("tests/friends_tarball.sh", "tools/cut_release.sh"):
            text = (ROOT / script).read_text(encoding="utf-8")
            self.assertIn("fixtures.py path", text, script)
            self.assertIn(FLOOR, text, script)
            self.assertNotIn("glibc-floor/runtime-2.6.8", text, script)


if __name__ == "__main__":
    unittest.main()
