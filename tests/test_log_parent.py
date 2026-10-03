"""fnn-log-parent names the directory that holds PATH, trailing slashes
trimmed (TCB-SHRINK review): the two defuns from host/native/io.lisp,
evaluated by SBCL as they are written, on paths with and without a
trailing slash.  Before the fix fnn-log-parent of "a/journal/" answered
"a/journal", so a fence meant for "a" fenced the renamed directory itself."""
import shutil
import subprocess
import unittest
from pathlib import Path

from tests.campaign.native_cuts import host_function

ROOT = Path(__file__).resolve().parent.parent
CASES = {"a/journal/": "a", "a/journal": "a", "/x/y//": "/x", "/x": "/", "x": ".",
         "x/": ".", "/": "/", "a/b/c.log": "a/b"}


@unittest.skipUnless(shutil.which("sbcl"), "sbcl is required")
class LogParentTests(unittest.TestCase):
    def test_trailing_slash_is_trimmed(self):
        source = (ROOT / "host/native/io.lisp").read_text()
        forms = host_function(source, "fnn-parent") + "\n" + host_function(source, "fnn-log-parent")
        calls = "".join('(format t "~a~%%" (fnn-log-parent "%s"))' % p for p in CASES)
        out = subprocess.run(["sbcl", "--noinform", "--non-interactive", "--no-userinit",
                              "--eval", "(progn %s %s)" % (forms, calls)],
                             capture_output=True, text=True, timeout=120)
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertEqual(out.stdout.splitlines()[-len(CASES):], list(CASES.values()))


if __name__ == "__main__":
    unittest.main()
