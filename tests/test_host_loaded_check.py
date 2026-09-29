"""tools/host_loaded_check.py: a host file no build loads is refused (Q7k)."""
import pathlib
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

import host_loaded_check  # noqa: E402


def tree(tmp: str) -> pathlib.Path:
    root = pathlib.Path(tmp)
    (root / "host" / "native").mkdir(parents=True)
    (root / "host/native/build.lisp").write_text('(ld "host/served-host.lisp")\n')
    (root / "host/native/build-store-test.lisp").write_text('(ld "host/test-image-host.lisp")\n')
    (root / "host/served-host.lisp").write_text("(defun s () 1)\n")
    (root / "host/test-image-host.lisp").write_text("(defun t1 () 1)\n")
    return root


class HostLoadedTests(unittest.TestCase):
    def test_every_loaded_file_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(host_loaded_check.findings(tree(tmp), {}), [])

    def test_an_unloaded_host_file_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = tree(tmp)
            (root / "host/native/proto-thing.lisp").write_text("(defun p () 1)\n")
            found = host_loaded_check.findings(root, {})
            self.assertEqual(len(found), 1)
            self.assertTrue(found[0].startswith("host/native/proto-thing.lisp: no build loads it"))
            self.assertEqual(host_loaded_check.findings(
                root, {"host/native/proto-thing.lisp": "why"}), [])

    def test_known_only_shrinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = tree(tmp)
            found = host_loaded_check.findings(
                root, {"host/served-host.lisp": "why", "host/gone.lisp": "why"})
            self.assertEqual(sorted(f.split(":")[0] for f in found),
                             ["host/gone.lisp", "host/served-host.lisp"])
            self.assertTrue(any("a build loads it now" in f for f in found))
            self.assertTrue(any("it is gone" in f for f in found))

    def test_the_tree_is_clean(self):
        self.assertEqual(host_loaded_check.findings(), [])


if __name__ == "__main__":
    unittest.main()
