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

    def test_nested_attachments_cannot_hide_outside_owner(self):
        templates = {
            'macro': "(defmacro hidden () '(attach-stobj scratch-hidden other)) (hidden)",
            'make-event': "(make-event '(attach-stobj scratch-hidden other))",
            'quote': "'(attach-stobj scratch-hidden other)",
            'backquote': '`(attach-stobj scratch-hidden other)',
            'symbol': "(defconst *event* 'other-package::attach-stobj)",
            'event-tail': '(defstobj scratch-concrete (x :initially nil) :inline attach-stobj)',
        }
        for bypass, source in templates.items():
            with self.subTest(bypass=bypass):
                self.refuse({
                    'books/g.lisp': '(attach-stobj scratch-hidden impl) (def-generic scratch-hidden :model nil)',
                    'books/other.lisp': source,
                }, '<computed>' if bypass in {'symbol', 'event-tail'} else 'scratch-hidden', 'OUTSIDE-OWNER')

    def test_qualified_attachment_head_is_refused(self):
        for package in ('acl2::', 'acl2:', 'other-package::'):
            with self.subTest(package=package):
                self.refuse({
                    'books/g.lisp': '(attach-stobj scratch-qualified impl) (def-generic scratch-qualified :model nil)',
                    'host/other.lisp': f'({package}attach-stobj {package}scratch-qualified impl)',
                }, 'scratch-qualified', 'OUTSIDE-OWNER')

    def test_qualified_introduction_head_is_refused(self):
        for package in ('acl2::', 'acl2:', 'other-package::'):
            for introduction in ('defabsstobj', 'def-generic'):
                with self.subTest(package=package, introduction=introduction):
                    self.refuse({
                        'books/g.lisp': '(attach-stobj scratch-qualified impl) (def-generic scratch-qualified :model nil)',
                        'books/other.lisp': f'({package}{introduction} {package}scratch-qualified :attachable t)',
                    }, 'scratch-qualified', 'SECOND-INTRODUCTION')

    def test_nested_introductions_cannot_hide_outside_owner(self):
        for template in ("(defmacro hidden () '(defabsstobj scratch-hidden :attachable t)) (hidden)",
                         "(make-event '(acl2::defabsstobj scratch-hidden :attachable t))",
                         "(defmacro hidden () '(defstobj scratch-hidden (x :initially nil))) (hidden)",
                         "(make-event '(defabsstobj scratch-hidden))",
                         '`(other::def-generic scratch-hidden :attachable t)'):
            with self.subTest(template=template):
                self.refuse({
                    'books/g.lisp': '(attach-stobj scratch-hidden impl) (def-generic scratch-hidden :model nil)',
                    'books/other.lisp': template,
                }, 'scratch-hidden', 'SECOND-INTRODUCTION')

    def test_acl2_test_books_are_scanned(self):
        for event, reason in (('(attach-stobj scratch-test other)', 'OUTSIDE-OWNER'),
                              ('(defabsstobj scratch-test :attachable t)', 'SECOND-INTRODUCTION')):
            with self.subTest(reason=reason):
                self.refuse({
                    'books/g.lisp': '(attach-stobj scratch-test impl) (def-generic scratch-test :model nil)',
                    'tests/acl2/other-tests.lisp': event,
                }, 'scratch-test', reason)

    def test_test_exemption_does_not_cover_other_files(self):
        self.refuse({
            'books/g.lisp': '(attach-stobj scratch-exemption impl) (def-generic scratch-exemption :model nil)',
            'books/def-generic-tests.lisp': '(attach-stobj scratch-exemption other)',
        }, 'scratch-exemption', 'OUTSIDE-OWNER')

    def test_generator_sites_outside_libraries_are_refused(self):
        for template in ('`(attach-stobj ,name impl)',
                         '`(acl2::defabsstobj ,name :attachable t)',
                         '`(other::def-generic ,name :attachable t)'):
            for filename in ('books/other.lisp', 'books/g.lisp',
                             'tests/acl2/def-representation-other-tests.lisp'):
                with self.subTest(template=template, filename=filename):
                    sources = {'books/g.lisp': '(attach-stobj scratch-generator impl) (def-generic scratch-generator :model nil)'}
                    sources[filename] = sources.get(filename, '') + f'(defun generator (name) {template})'
                    self.refuse(sources, '<computed>', 'GENERATOR-OUTSIDE-LIBRARY')

    def test_literal_sites_in_generator_libraries_are_not_exempt(self):
        for filename in ('books/def-representation-generic.lisp', 'books/def-representation.lisp'):
            for template, reason in (("'(acl2::attach-stobj scratch-library impl)", 'OUTSIDE-OWNER'),
                                     ("'(defabsstobj scratch-library :attachable t)", 'SECOND-INTRODUCTION')):
                with self.subTest(filename=filename, reason=reason):
                    self.refuse({
                        'books/g.lisp': '(attach-stobj scratch-library impl) (def-generic scratch-library :model nil)',
                        filename: f'(defmacro hidden () {template}) (hidden)',
                    }, 'scratch-library', reason)

    def test_generator_sites_in_named_libraries_are_legal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'books').mkdir()
            for filename in ('def-representation-generic', 'def-representation'):
                (root / 'books' / f'{filename}.lisp').write_text('''
(defun generator (name)
  `((acl2::attach-stobj ,name impl)
    (acl2::defabsstobj ,name :attachable t)))
''')
            self.assertEqual(check(root), ([], 0, 0))

    def test_qualified_generator_call_is_checked_at_call_site(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'books').mkdir()
            (root / 'books/g.lisp').write_text(
                '(acl2::def-representation scratch-expanded (value :u8) :generic t)')
            self.assertEqual(check(root), ([], 1, 1))

    def test_qualified_owner_events_and_templates_are_legal(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'books').mkdir()
            (root / 'books/g.lisp').write_text('''
(acl2::progn (acl2::attach-stobj acl2::scratch-good impl)
             (acl2::defabsstobj acl2::scratch-good :attachable t))
(defmacro generator () `(other::attach-stobj scratch-good impl))
(make-event '(acl2::attach-stobj scratch-good impl))
(defconst *template* '(acl2::defabsstobj scratch-good :attachable t))
''')
            self.assertEqual(check(root), ([], 1, 1))

    def test_quoted_templates_are_not_introductions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'books').mkdir()
            (root / 'books/g.lisp').write_text('''
; (def-generic commented)
(defun generator (name) `(defabsstobj scratch-good :attachable t))
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
