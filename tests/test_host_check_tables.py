"""Teeth for tools/host_check.py --tables (lane host-lints): the rule refuses
each shape of unsynchronised global table in tests/fixtures/host-tables/
refused.lisp by file:line and name, accepts the same file with only the
declarations added (so each refusal is for the named reason, never a parse
accident), ignores a table local to one call and text in comments and
strings, and passes host/.  Also the host's one global counter of off-mutex
arena readers: the publication is counted under the owner mutex before its
thread starts."""
from __future__ import annotations

from pathlib import Path
import re
import sys
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import host_check  # noqa: E402

FIXTURES = ROOT / "tests" / "fixtures" / "host-tables"


class HostTablesRuleTests(unittest.TestCase):
    def test_the_fixture_is_refused_site_by_site(self):
        refused, accepted = host_check.tables_check([FIXTURES / "refused.lisp"])
        self.assertEqual(accepted, [])
        where = [line.split(": ", 1)[0] for line in refused]
        self.assertEqual(where, [
            "tests/fixtures/host-tables/refused.lisp:7 *fx-shared*",
            "tests/fixtures/host-tables/refused.lisp:8 *fx-unsync*",
            "tests/fixtures/host-tables/refused.lisp:11 fx-runtime slot pending",
            "tests/fixtures/host-tables/refused.lisp:13 *fx-misnamed*",
            "tests/fixtures/host-tables/refused.lisp:15 *fx-late*",
        ])
        self.assertIn("no with-mutex/with-recursive-lock in this file takes it", refused[3])
        self.assertIn("neither :synchronized t nor declared", refused[0])

    def test_the_declared_twin_is_accepted(self):
        refused, accepted = host_check.tables_check([FIXTURES / "accepted.lisp"])
        self.assertEqual(refused, [])
        self.assertEqual([line.split(": ", 1)[1] for line in accepted], [
            "guarded-by *fx-lock*", ":synchronized t", "guarded-by fx-runtime-lock",
            "guarded-by *fx-lock*", "thread-confined"])

    def test_a_multi_pair_setf_names_each_place_and_inherits_its_declaration(self):
        """A pool install re-makes several declared tables in one setf under
        their lock (host/native/extent.lisp fnn-extent-pool-storage-start):
        each pair's table is its own place, and carries the declaration of
        the variable it assigns; a declaration in the comment lines right
        under a defvar counts.  Undeclared, each pair is refused by its own
        name (it used to be reported under the first pair's)."""
        import tempfile
        body = ('(in-package "ACL2")\n'
                '(defvar *fx-lock* (sb-thread:make-mutex :name "fixture"))\n'
                '(defvar *fx-a* (make-hash-table)){a}\n'
                '(defvar *fx-b* (make-hash-table))\n{b}'
                '(defun fx-reset ()\n'
                '  (sb-thread:with-mutex (*fx-lock*)\n'
                '    (setf *fx-a* (make-hash-table :size 4)\n'
                '          *fx-b* (make-hash-table :size 8))))\n')
        with tempfile.TemporaryDirectory() as directory:
            bare = Path(directory) / "bare.lisp"
            bare.write_text(body.format(a="", b=""))
            refused, _ = host_check.tables_check([bare])
            self.assertEqual([r.split(": ", 1)[0].split(" ", 1)[1] for r in refused],
                             ["*fx-a*", "*fx-b*", "*fx-a*", "*fx-b*"])
            declared = Path(directory) / "declared.lisp"
            declared.write_text(body.format(a=" ; guarded-by: *fx-lock*",
                                            b=";; guarded-by: *fx-lock*. Under the defvar.\n"))
            refused, accepted = host_check.tables_check([declared])
            self.assertEqual(refused, [])
            self.assertEqual(len(accepted), 4)

    def test_the_command_exits_one_on_the_fixture(self):
        self.assertEqual(host_check.main(["--tables", str(FIXTURES / "refused.lisp")]), 1)
        self.assertEqual(host_check.main(["--tables", str(FIXTURES / "accepted.lisp")]), 0)

    def test_host_passes(self):
        refused, accepted = host_check.tables_check(host_check.table_files())
        self.assertEqual(refused, [])
        # the two entry-guards-2 tables (6137e36c3) are among the checked
        self.assertTrue(any("*fnn-entry-guard-specs*" in a for a in accepted))
        self.assertTrue(any("*fnn-trailing-stobjs*" in a for a in accepted))


def host_function(text: str, name: str) -> str:
    start = text.index("(defun " + name + " ")
    end = text.find("\n(def", start + 1)
    return text[start:end if end >= 0 else len(text)]


class PublicationReaderCountTests(unittest.TestCase):
    def test_counted_under_the_mutex_before_the_thread_starts(self):
        owner = (ROOT / "host" / "native" / "owner.lisp").read_text(encoding="utf-8")
        maybe = host_function(owner, "fnn-owner-maybe-publish-quantum")
        publish = host_function(owner, "fnn-owner-publish-captured")
        incf = "(fnn-arena-pin)"
        decf = "(fnn-arena-unpin pin)"
        self.assertIn("(fnn-owner-gated (service :control)", maybe)
        self.assertLess(maybe.index(incf), maybe.index("(sb-thread:make-thread"))
        self.assertIn(decf, maybe)  # a thread never made returns its pin
        self.assertNotIn(incf, publish)
        self.assertEqual(len(re.findall(re.escape(decf), publish)), 1)


if __name__ == "__main__":
    unittest.main()
