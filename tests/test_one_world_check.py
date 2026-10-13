import contextlib
import io
from pathlib import Path
import tempfile
import unittest

from tools.one_world_check import ROOT, check, main


class OneWorldTests(unittest.TestCase):
    def refuse(self, sources, name, reason):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for filename, source in sources.items():
                path = root / filename
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                status = main(['--root', str(root)])
            self.assertEqual(status, 1, output.getvalue())
            self.assertTrue(any(name in line and reason in line
                                for line in output.getvalue().splitlines()), output.getvalue())

    def test_attachment_outside_generic_book(self):
        self.refuse({'books/g.lisp': '(def-generic scratch-outside :model nil)',
                     'host/other.lisp': '(attach-stobj scratch-outside impl)'},
                    'scratch-outside', 'OUTSIDE-OWNER')

    def test_second_introduction(self):
        self.refuse({'books/g.lisp': '(attach-stobj scratch-twice impl) (defabsstobj scratch-twice :attachable t)',
                     'books/other.lisp': '(defstobj scratch-twice (x :initially nil))'},
                    'scratch-twice', 'SECOND-INTRODUCTION')

    def test_attachment_after_introduction(self):
        self.refuse({'books/g.lisp': '(defabsstobj scratch-late :attachable t) (attach-stobj scratch-late impl)'},
                    'scratch-late', 'MISSING-PRECEDING-ATTACH')

    def test_second_attachment_in_owner_book(self):
        self.refuse({'books/g.lisp': '(attach-stobj scratch-rebound impl) (attach-stobj scratch-rebound other) (def-generic scratch-rebound :model nil)'},
                    'scratch-rebound', 'SECOND-ATTACHMENT')

    def test_implementation_cannot_be_generic(self):
        for implementation in ('fn-arena-extent', 'fn-cat-paged', 'fn-hist-paged'):
            with self.subTest(implementation=implementation):
                self.refuse({'books/impl.lisp': f'(defabsstobj {implementation})',
                             'host/reattach.lisp': f'(attach-stobj {implementation} other)'},
                            implementation, 'IMPLEMENTATION-AS-GENERIC')

    def test_generated_implementation_attachment_is_refused(self):
        self.refuse({'books/impl.lisp': '(def-representation fn-cat-paged (value :u8) :generic t)'},
                    'fn-cat-paged', 'IMPLEMENTATION-AS-GENERIC')

    def test_generated_second_introduction_is_refused(self):
        self.refuse({'books/g.lisp': '(attach-stobj scratch-generated impl) (def-generic scratch-generated :model nil)',
                     'books/other.lisp': '(def-representation scratch-generated (value :u8))'},
                    'scratch-generated', 'SECOND-INTRODUCTION')

    def test_quoted_templates_are_not_introductions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'books').mkdir()
            (root / 'books/g.lisp').write_text('''
; (def-generic commented)
(defun generator (name) `(defabsstobj ,name :attachable t))
(defconst *template* '(attach-stobj quoted impl))
(progn (attach-stobj scratch-good impl)
       (defabsstobj scratch-good :attachable t))
''')
            self.assertEqual(check(root), ([], 1, 1))

    def test_clean_tree(self):
        findings, generics, sites = check(ROOT)
        self.assertEqual(findings, [])
        self.assertEqual((generics, sites), (3, 3))
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = main([])
        self.assertEqual(status, 0)
        self.assertIn('0 findings', output.getvalue())
