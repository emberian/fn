"""tools/system_books.py: the toolchain's system books are one read list, and a box without one is named."""
import os
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))

import system_books as sb                                       # noqa: E402


class SystemBooksTests(unittest.TestCase):
    def tree(self, d: Path) -> Path:
        (d / "books").mkdir()
        (d / "tests" / "acl2").mkdir(parents=True)
        (d / "books" / "a.lisp").write_text(
            '(local (include-book "arithmetic/top" :dir :system))\n'
            '; (include-book "std/commented/out" :dir :system)\n')
        (d / "tests" / "acl2" / "t.lisp").write_text('(include-book "std/testing/must-fail" :dir :system)\n')
        return d

    def acl2(self, d: Path, certified) -> Path:
        acl2 = d / "acl2"
        for book in certified:
            (acl2 / "books" / Path(book).parent).mkdir(parents=True, exist_ok=True)
            (acl2 / "books" / f"{book}.cert").write_text("")
        (acl2 / "books").mkdir(parents=True, exist_ok=True)
        launcher = d / "acl2-literal"
        launcher.write_text("#!/bin/sh\nexport SBCL_HOME='/x/'\n"
                            f'exec "/x/sbcl" --tls-limit 65536 --core "{acl2}/saved_acl2.core"'
                            " --end-runtime-options --no-userinit \"$@\"\n")
        return launcher

    def test_the_list_is_the_trees_system_includes_and_the_extras(self):
        with tempfile.TemporaryDirectory() as d:
            got = sb.books(self.tree(Path(d)))
        self.assertEqual(got, sorted({"arithmetic/top", "std/testing/must-fail", *sb.TOOLCHAIN_EXTRA}))
        self.assertIn("std/lists/nthcdr", got)

    def test_a_missing_certificate_is_named_and_none_is_not_run(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            wanted = ["arithmetic/top", "std/lists/nthcdr"]
            launcher = self.acl2(d, ["arithmetic/top"])
            self.assertEqual(sb.books_dir(launcher), d / "acl2" / "books")
            status, line = sb.check(str(launcher), wanted)
            self.assertEqual(status, 1)
            self.assertIn("std/lists/nthcdr", line)
            (d / "acl2" / "books" / "std" / "lists").mkdir(parents=True)
            (d / "acl2" / "books" / "std" / "lists" / "nthcdr.cert").write_text("")
            self.assertEqual(sb.check(str(launcher), wanted)[0], 0)
        saved = os.environ.pop("FN_ACL2", None)
        try:
            status, line = sb.check(None, ["x"])
        finally:
            if saved is not None:
                os.environ["FN_ACL2"] = saved
        self.assertEqual(status, 2)
        self.assertIn("NOT RUN", line)

    def test_the_laptop_build_certifies_the_same_list(self):
        script = (ROOT / "tools" / "build_local_acl2.sh").read_text()
        self.assertIn("tools/system_books.py\" list", script)


if __name__ == "__main__":
    unittest.main()
