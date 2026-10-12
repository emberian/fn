"""Production books must belong to a Makefile root's include closure."""
import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from tools import book_roots_check


class BookRootsCheckTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="book-roots-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        (self.root / "books/nested").mkdir(parents=True)
        (self.root / "tests/acl2").mkdir(parents=True)
        (self.root / "Makefile").write_text("ACL2_BOOKS = tests/acl2/root-tests\n")
        (self.root / "tests/acl2/root-tests.lisp").write_text(
            '(include-book "../../books/parent")\n')
        (self.root / "books/parent.lisp").write_text('(include-book "nested/child")\n')
        (self.root / "books/nested/child.lisp").write_text('(in-package "ACL2")\n')

    def check(self, excluded=None):
        output = io.StringIO()
        with mock.patch.object(book_roots_check.ledger, "ROOT", self.root), \
                contextlib.redirect_stdout(output):
            # A fixture tree is judged by its own exclusions, never the real tree's.
            rc = book_roots_check.main(self.root, excluded={} if excluded is None else excluded)
        return rc, output.getvalue()

    def test_an_orphan_book_fails_and_is_named(self):
        (self.root / "books/nested/orphan.lisp").write_text("")
        rc, output = self.check()
        self.assertEqual(rc, 1)
        self.assertIn("books/nested/orphan.lisp is outside", output)

    def test_an_excluded_orphan_passes_and_its_reason_is_printed(self):
        (self.root / "books/parked.lisp").write_text("")
        rc, output = self.check({"books/parked.lisp": "seat C: repair the missing root"})
        self.assertEqual(rc, 0, output)
        self.assertIn("EXCLUDED: books/parked.lisp: seat C: repair the missing root", output)

    def test_a_book_included_by_a_root_passes(self):
        rc, output = self.check()
        self.assertEqual(rc, 0, output)
        self.assertIn("2 of 2 books/**/*.lisp are covered", output)

    def test_exclusions_are_printed_even_when_another_orphan_fails(self):
        (self.root / "books/parked.lisp").write_text("")
        (self.root / "books/orphan.lisp").write_text("")
        rc, output = self.check({"books/parked.lisp": "seat C: repair"})
        self.assertEqual(rc, 1)
        self.assertIn("EXCLUDED: books/parked.lisp: seat C: repair", output)
        self.assertIn("books/orphan.lisp is outside", output)

    def test_an_exclusion_without_a_reason_fails(self):
        (self.root / "books/parked.lisp").write_text("")
        rc, output = self.check({"books/parked.lisp": ""})
        self.assertEqual(rc, 1)
        self.assertIn("has no exclusion reason", output)

    def test_a_stale_exclusion_fails(self):
        rc, output = self.check({"books/nested/child.lisp": "seat C: formerly orphaned"})
        self.assertEqual(rc, 1)
        self.assertIn("drop it from EXCLUDED", output)

    def test_a_system_include_does_not_cover_a_local_book(self):
        (self.root / "books/parent.lisp").write_text(
            '(include-book "nested/child" :dir :system)\n')
        rc, output = self.check()
        self.assertEqual(rc, 1)
        self.assertIn("books/nested/child.lisp is outside", output)

    def review_shape(self, include, excluded=None):
        """The reviewer's books/root -> books/target fixture shape."""
        root = self.root / "review-shape"
        (root / "books").mkdir(parents=True, exist_ok=True)
        (root / "books/root.lisp").write_text('(in-package "ACL2")\n' + include + '\n')
        (root / "books/target.lisp").write_text('(in-package "ACL2")\n')
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            rc = book_roots_check.main(root, roots=["books/root"],
                                      excluded={} if excluded is None else excluded)
        return rc, output.getvalue()

    def test_reader_conditionals_are_unanalyzable_and_never_cover_the_target(self):
        for marker in ("#+", "#-"):
            with self.subTest(marker=marker):
                rc, output = self.review_shape(
                    marker + 'fn-review-feature-not-present\n(include-book "target")')
                self.assertEqual(rc, 1, output)
                self.assertIn("UNANALYZABLE: books/root.lisp:2: reader conditional", output)
                self.assertIn("1 of 2 books/**/*.lisp are covered", output)

    def test_dir_nil_covers_the_ordinary_local_include(self):
        rc, output = self.review_shape('(include-book "target" :dir nil)')
        self.assertEqual(rc, 0, output)
        self.assertIn("2 of 2 books/**/*.lisp are covered", output)
        self.assertIn("0 unanalyzable", output)

    def test_make_event_include_is_unanalyzable_even_when_the_target_is_excluded(self):
        # With the orphan excused, only the uncertain include can fail this.
        rc, output = self.review_shape("(make-event '(include-book \"target\"))",
                                       {"books/target.lisp": "fixture: parked target"})
        self.assertEqual(rc, 1, output)
        self.assertIn("UNANALYZABLE: books/root.lisp:2: make-event", output)
        self.assertIn("1 of 2 books/**/*.lisp are covered", output)
        self.assertIn("0 unlisted orphan(s); 1 unanalyzable", output)

    def test_conditional_include_is_unanalyzable_even_when_the_target_is_excluded(self):
        rc, output = self.review_shape('#+fixture-feature\n(include-book "target")',
                                       {"books/target.lisp": "fixture: parked target"})
        self.assertEqual(rc, 1, output)
        self.assertIn("0 unlisted orphan(s); 1 unanalyzable", output)

    def test_comment_string_and_quoted_include_controls_are_not_unanalyzable(self):
        rc, output = self.review_shape(
            '; #+feature (include-book "target")\n'
            '#| (make-event \'(include-book "target")) |#\n'
            '(value-triple "#+feature (include-book target)")\n'
            '\'(make-event (include-book "target"))\n'
            '(include-book "target")')
        self.assertEqual(rc, 0, output)
        self.assertIn("0 unanalyzable", output)


if __name__ == "__main__":
    unittest.main()
