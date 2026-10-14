import contextlib
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools import one_world_check as one_world
from tools.one_world_check import ROOT, check, main


class OneWorldTests(unittest.TestCase):
    def refuse(self, sources, name, reason, allowed=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for filename, source in sources.items():
                path = root / filename
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            output = io.StringIO()
            with (contextlib.redirect_stdout(output),
                  patch.object(one_world, "ALLOWED_SITES", allowed) if allowed is not None
                  else contextlib.nullcontext()):
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
                    self.refuse(sources, 'GENERATOR', 'GENERATOR-OUTSIDE-LIBRARY')

    def test_literal_sites_in_generator_libraries_are_not_exempt(self):
        for filename in ('books/def-representation-generic.lisp', 'books/def-representation.lisp'):
            for template, reason in (("'(acl2::attach-stobj scratch-library impl)", 'OUTSIDE-OWNER'),
                                     ("'(defabsstobj scratch-library :attachable t)", 'SECOND-INTRODUCTION')):
                with self.subTest(filename=filename, reason=reason):
                    self.refuse({
                        'books/g.lisp': '(attach-stobj scratch-library impl) (def-generic scratch-library :model nil)',
                        filename: f'(defmacro hidden () {template}) (hidden)',
                    }, 'scratch-library', reason)

    def accept(self, sources, allowed):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for filename, source in sources.items():
                path = root / filename
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(source)
            with patch.object(one_world, 'ALLOWED_SITES', allowed):
                count = sum(len(entries) for entries in allowed.values())
                self.assertEqual(check(root), ([], count, count))
                output = io.StringIO()
                with contextlib.redirect_stdout(output):
                    self.assertEqual(main(['--root', str(root)]), 0)
                self.assertIn('0 findings', output.getvalue())

    def owner(self, book='books/g.lisp', name='scratch-closed'):
        sources = {book: f'(attach-stobj {name} impl) (defabsstobj {name} :attachable t)'}
        allowed = {book: (('attachment', name), ('introduction', name))}
        self.accept(sources, allowed)
        return sources, allowed

    def test_unlisted_site(self):
        sources, allowed = self.owner()
        sources['books/other.lisp'] = "'(attach-stobj scratch-unlisted impl)"
        self.refuse(sources, 'scratch-unlisted', 'UNLISTED-SITE', allowed)

    def test_missing_site(self):
        sources, allowed = self.owner()
        sources['books/g.lisp'] = '(attach-stobj scratch-closed impl)'
        self.refuse(sources, 'scratch-closed', 'MISSING-SITE', allowed)

    def test_site_count(self):
        sources, allowed = self.owner()
        sources['books/g.lisp'] += ' (attach-stobj scratch-closed other)'
        self.refuse(sources, 'scratch-closed', 'SITE-COUNT', allowed)

    def test_missing_file_still_requires_its_sites(self):
        sources, allowed = self.owner()
        allowed['books/missing.lisp'] = (('introduction', 'scratch-missing'),)
        self.refuse(sources, 'scratch-missing', 'MISSING-SITE', allowed)

    def test_order_requires_admitted_owner_events(self):
        sources, allowed = self.owner()
        sources['books/g.lisp'] = "(attach-stobj scratch-closed impl) (unknown-wrapper '(defabsstobj scratch-closed :attachable t))"
        self.refuse(sources, 'scratch-closed', 'MISSING-PRECEDING-ATTACH', allowed)

    def test_rr_a1_attachment_inside_each_named_fixture_book(self):
        for book, entries in one_world.ALLOWED_SITES.items():
            if not book.startswith('tests/acl2/'):
                continue
            with self.subTest(book=book):
                sources, allowed = self.owner(name='fn-cat')
                kind, name = entries[0]
                if kind == 'representation-call':
                    fixture = f'(def-representation {name} (value :u8) :generic t)'
                else:
                    fixture = f'(defabsstobj {name} :attachable t)'
                sources[book] = fixture
                allowed[book] = ((kind, name),)
                self.accept(sources, allowed)
                sources[book] += ' (attach-stobj fn-cat fn-cat-paged)'
                self.refuse(sources, 'fn-cat', 'UNLISTED-SITE', allowed)

    def test_rr_a2_hidden_concrete_generator_and_call(self):
        sources, allowed = self.owner(name='fn-cat')
        sources['books/other.lisp'] = '(defmacro hidden (name) `(defabsstobj ,name)) (hidden fn-cat)'
        self.refuse(sources, 'GENERATOR', 'UNLISTED-SITE', allowed)
        self.refuse(sources, 'GENERATOR', 'GENERATOR-OUTSIDE-LIBRARY', allowed)

    def test_rr_a2_library_macro_calls_outside_owner_are_sites(self):
        for event in ('(def-generic fn-cat :model nil)',
                      '(acl2::def-representation fn-cat (value :u8) :generic t)',
                      '(def-representation fn-cat (value :u8))'):
            with self.subTest(event=event):
                sources, allowed = self.owner(name='fn-cat')
                sources['books/other.lisp'] = f'(unknown-wrapper (make-event \'{event}))'
                self.refuse(sources, 'fn-cat', 'UNLISTED-SITE', allowed)

    def test_computed_macro_calls_are_refused_even_if_counted(self):
        for macro in one_world.GENERATOR_MACROS:
            for name in (',name', '(intern-in-package-of-symbol "FN-CAT" \'fn-cat)'):
                with self.subTest(macro=macro, name=name):
                    sources, allowed = self.owner()
                    kind = 'introduction' if macro == 'def-generic' else 'representation-call'
                    marker = 'GENERATOR' if name.startswith(',') else '<computed>'
                    sources['books/other.lisp'] = f'(defmacro hidden (name) `({macro} {name}))'
                    # Even an erroneous manifest grant cannot legalize a
                    # computed generic outside a named generator library.
                    allowed['books/other.lisp'] = ((kind, marker),)
                    self.refuse(sources, marker, 'GENERATOR-OUTSIDE-LIBRARY', allowed)

    def test_unresolved_representation_option_is_a_site(self):
        sources, allowed = self.owner()
        sources['books/other.lisp'] = '(def-representation scratch-option (value :u8) :generic (intern "T" "ACL2"))'
        self.refuse(sources, 'scratch-option', 'UNLISTED-SITE', allowed)

    def test_rr_a3_make_event_second_attachment_and_introduction(self):
        for event in ('(attach-stobj fn-cat other)',
                      '(defabsstobj fn-cat :attachable t)',
                      '(def-generic fn-cat :model nil)'):
            with self.subTest(event=event):
                sources, allowed = self.owner(name='fn-cat')
                sources['books/g.lisp'] += f' (make-event \'{event})'
                self.refuse(sources, 'fn-cat', 'SITE-COUNT', allowed)

    def test_unlisted_owner_templates_are_refused(self):
        for template in ("'(attach-stobj scratch-closed impl)",
                         '`(defabsstobj scratch-closed :attachable t)',
                         '(defmacro hidden () \'(attach-stobj scratch-closed impl))'):
            with self.subTest(template=template):
                sources, allowed = self.owner()
                sources['books/g.lisp'] += ' ' + template
                self.refuse(sources, 'scratch-closed', 'SITE-COUNT', allowed)

    def test_generator_sites_in_named_libraries_are_legal(self):
        generic = 'books/def-representation-generic.lisp'
        representation = 'books/def-representation.lisp'
        sources = {
            generic: '(include-book \"def-representation\") (defun template (name) `(acl2::defabsstobj ,name :attachable t))',
            representation: '(defun template (name) `((acl2::attach-stobj ,name impl) (acl2::defabsstobj ,name :attachable t)))',
        }
        self.accept(sources, {book: one_world.ALLOWED_SITES[book] for book in sources})

    def test_qualified_generator_call_is_checked_at_call_site(self):
        self.accept({'books/g.lisp': '(acl2::def-representation scratch-expanded (value :u8) :generic t)'},
                    {'books/g.lisp': (('representation-call', 'scratch-expanded'),)})

    def test_wrapped_generator_keeps_its_call_site_ordering_location(self):
        self.accept({'books/g.lisp': '(acl2::progn\n (acl2::def-representation scratch-expanded (value :u8) :generic t))'},
                    {'books/g.lisp': (('representation-call', 'scratch-expanded'),)})

    def test_qualified_owner_events_are_legal(self):
        self.accept({'books/g.lisp': '(acl2::progn (acl2::attach-stobj acl2::scratch-good impl) (acl2::defabsstobj acl2::scratch-good :attachable t))'},
                    {'books/g.lisp': (('attachment', 'scratch-good'), ('introduction', 'scratch-good'))})

    def test_comments_and_strings_are_not_sites(self):
        sources, allowed = self.owner()
        sources['books/g.lisp'] += '\n; (attach-stobj commented impl)\n(defconst *text* "(defabsstobj text :attachable t)")'
        self.accept(sources, allowed)

    def test_omitted_owner_attachments_are_missing_sites(self):
        for conditional in ('#+(or)', '#-(and)'):
            with self.subTest(conditional=conditional):
                sources, allowed = self.owner()
                sources['books/g.lisp'] = f'{conditional} (attach-stobj scratch-closed impl) (defabsstobj scratch-closed :attachable t)'
                self.refuse(sources, 'scratch-closed', 'MISSING-SITE', allowed)

    def test_omitted_forms_create_no_objects_or_sites(self):
        sources, allowed = self.owner()
        sources['books/other.lisp'] = '#+(or) (attach-stobj scratch-closed other)\n#-(and) (make-event \'(defabsstobj scratch-closed :attachable t))\n#+(or) (list "ATTACH-STOBJ" `(def-generic ,name))\n(progn #+(or) (attach-stobj scratch-closed other))\n'
        self.accept(sources, allowed)

    def test_omitted_nested_conditionals_do_not_evaluate_features(self):
        sources, allowed = self.owner()
        sources['books/other.lisp'] = '#+(or) (progn #+:unmodeled (list "ATTACH-STOBJ"))'
        self.accept(sources, allowed)

    def test_midtoken_hash_is_not_a_block_comment(self):
        sources, allowed = self.owner()
        sources['books/g.lisp'] = '(attach-stobj#|suffix|# scratch-closed impl) (defabsstobj scratch-closed :attachable t)'
        self.refuse(sources, 'scratch-closed', 'MISSING-SITE', allowed)

    def test_feature_expressions_and_keywords(self):
        features = frozenset({'sbcl', 'gencgc', 'linux', 'x86-64'})
        reader = one_world.SourceReader('#+(:and :sbcl (:or :linux :openbsd) (:not :darwin)) kept\n#-:linux omitted\n#+(or) omitted\n#-(and) omitted\n#+(and) kept-too\n#-(or) kept-last\n', features=features)
        self.assertEqual([str(value) for value, _line in reader.top_level()],
                         ['kept', 'kept-too', 'kept-last'])

    def test_feature_expressions_are_validated_without_short_circuiting(self):
        for expression in ('(not :sbcl :linux)', '(and (or) :unmodeled)', '(or :sbcl :unmodeled)'):
            with self.subTest(expression=expression):
                sources, allowed = self.owner()
                sources['books/other.lisp'] = f'#+{expression} nil'
                self.refuse(sources, 'expected' if expression.startswith('(not') else 'unmodeled',
                            'READER-FEATURE', allowed)

    def test_included_conditional_site_preserves_ordering_location(self):
        sources, allowed = self.owner()
        sources['books/g.lisp'] = '#+(and) (attach-stobj scratch-closed impl)\n#+(not (or)) (defabsstobj scratch-closed :attachable t)\n'
        self.accept(sources, allowed)

    def test_read_eval_is_refused_in_every_source_root(self):
        for book in ('books/other.lisp', 'host/other.lisp', 'tests/acl2/other-tests.lisp'):
            for expression in ('(#.(intern "ATTACH-STOBJ" "ACL2") scratch-closed impl)',
                               '(defmacro hidden () \'(#.(intern "DEFABSSTOBJ" "ACL2") scratch-closed :attachable t))',
                               '#+(or) #.(intern "ATTACH-STOBJ" "ACL2")'):
                with self.subTest(book=book, expression=expression):
                    sources, allowed = self.owner()
                    sources[book] = expression
                    self.refuse(sources, 'read-eval', 'READER-EVAL', allowed)

    def test_reader_labels_and_references_are_refused(self):
        for expression in ('(#1=ATTACH-STOBJ scratch-closed impl)',
                           '(list #1=thing #1#)', '#1#', '#+(or) #12=thing'):
            with self.subTest(expression=expression):
                sources, allowed = self.owner()
                sources['books/other.lisp'] = expression
                self.refuse(sources, 'labels/references', 'READER-LABEL', allowed)

    def test_unknown_dispatch_is_refused(self):
        for expression in ('#zanything', '#:uninterned', '#2A((1 2))', '#S(thing)', '#;ignored', '#+(or) #zhidden'):
            with self.subTest(expression=expression):
                sources, allowed = self.owner()
                sources['books/other.lisp'] = expression
                self.refuse(sources, 'unsupported dispatch', 'READER-DISPATCH', allowed)

    def test_legitimate_dispatch_macros_are_read_as_data(self):
        reader = one_world.SourceReader("#| outer #| inner |# comment |#\n#'fn #\\) #(1 2) #o600 #xFF #c(1/2 2) #b101 #d12 #16rFF\n")
        values = [value for value, _line in reader.top_level()]
        self.assertEqual(len(values), 9)
        self.assertEqual(one_world.head(values[0]), 'function')
        self.assertIsInstance(values[1], one_world.LispChar)
        self.assertEqual(one_world.head(values[2]), 'vector')
        self.assertEqual(values[3:5], [384, 255])
        self.assertEqual(one_world.head(values[5]), 'complex')
        self.assertEqual(values[6:], [5, 12, 255])

    def test_dispatch_text_inside_comments_and_strings_is_not_dispatch(self):
        sources, allowed = self.owner()
        sources['books/other.lisp'] = '; #.(unsafe) #1=object #1# #zunknown\n#| #.(unsafe) #1=object #1# #zunknown |#\n(defconst *text* "#. #1= #1# #z")\n'
        self.accept(sources, allowed)

    def test_site_name_strings_at_every_depth(self):
        for name in sorted(one_world.SITE_SYMBOLS):
            for text in (name, name.upper(), 'ACL2::' + name.upper(), 'other:' + name):
                for wrapper in ('(defconst *name* "{text}")',
                                '(defmacro hidden () (list "{text}"))',
                                '(make-event (list (intern-in-package-of-symbol "{text}" \'fn-cat)))',
                                '`(unknown-wrapper #("{text}"))'):
                    with self.subTest(text=text, wrapper=wrapper):
                        sources, allowed = self.owner()
                        sources['books/other.lisp'] = wrapper.format(text=text)
                        self.refuse(sources, text, 'SITE-NAME-STRING', allowed)

    def test_escaped_site_name_string_is_decoded(self):
        sources, allowed = self.owner()
        escaped = 'AT' + chr(92) + 'TACH-STOBJ'
        sources['books/other.lisp'] = f'(defconst *name* "{escaped}")'
        self.refuse(sources, 'ATTACH-STOBJ', 'SITE-NAME-STRING', allowed)

    def test_import_string_allowance_is_exact_and_contextual(self):
        book = 'books/catalog-paged.lisp'
        allowed = {book: one_world.ALLOWED_SITES[book]}
        self.accept({book: '(include-book "def-representation")'}, allowed)
        for source in ('(defconst *name* "def-representation")',
                       '(include-book "DEF-REPRESENTATION")',
                       '(make-event (list (intern "def-representation" "ACL2")))'):
            with self.subTest(source=source):
                self.refuse({book: source}, 'REPRESENTATION' if 'DEF-REPRESENTATION' in source else 'def-representation',
                            'SITE-NAME-STRING', allowed)
        self.refuse({book: '(include-book "def-representation") (include-book "def-representation")'},
                    'def-representation', 'SITE-COUNT', allowed)

    def test_exact_allowed_site_name_string_is_counted(self):
        sources, allowed = self.owner()
        sources['books/g.lisp'] += ' (defconst *name* "ATTACH-STOBJ")'
        allowed['books/g.lisp'] += (('site-name-string', 'ATTACH-STOBJ'),)
        self.accept(sources, allowed)
        sources['books/other.lisp'] = '(defconst *name* "ATTACH-STOBJ")'
        self.refuse(sources, 'ATTACH-STOBJ', 'SITE-NAME-STRING', allowed)

    def test_clean_tree(self):
        findings, sites, expected = check(ROOT)
        self.assertEqual(findings, [])
        self.assertEqual((sites, expected), (29, 29))
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = main([])
        self.assertEqual(status, 0)
        self.assertIn('0 findings', output.getvalue())
