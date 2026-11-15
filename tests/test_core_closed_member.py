"""Packet-to-proof controls; fixtures are not current ACL2 exports."""
import importlib.util
from pathlib import Path
import tempfile
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location('core', Path(__file__).parents[1] / 'meta/emit/emit_core_certificate.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)


def obj(value):
    if isinstance(value, list):
        result = obj('COMMON-LISP::NIL')
        for item in reversed(value):
            result = f'(:CONS {obj(item)} {result})'
        return result
    package, name = value.split('::') if '::' in value else ('ACL2', value)
    return '(:SYMBOL (' + ' '.join(map(str, map(ord, package))) + ') (' + ' '.join(map(str, map(ord, name))) + '))'


def packet(mutate=False, duplicate=False):
    cl = lambda n: 'COMMON-LISP::' + n
    q = lambda n: [cl('QUOTE'), cl(n)]
    bodies = {
        'NOT': (['P'], [cl('IF'), 'P', q('NIL'), q('T')]),
        'ATOM': (['X'], [cl('NOT'), [cl('CONSP'), 'X']]),
        'ENDP': (['X'], [cl('ATOM'), 'X']),
        'EQ': (['X', 'Y'], [cl('EQUAL'), 'X', 'Y']),
        'MEMBER-EQ-EXEC': (['X', 'LST'], [cl('IF'), [cl('ENDP'), 'LST'], q('NIL'),
            [cl('IF'), [cl('EQ'), 'X', [cl('CAR'), 'LST']], 'LST',
             ['MEMBER-EQ-EXEC', 'X', [cl('CDR'), 'LST']]]]),
        'FN2-ACCEPT-ROUTE': (['X', 'LST'], ['MEMBER-EQ-EXEC', 'X', 'LST']),
    }
    if mutate:
        # Same ABI and reached closure; only the recursive tail is corrupted.
        bodies['MEMBER-EQ-EXEC'][1][3][3][2] = 'LST'
    rows = []
    for name, (formals, body) in bodies.items():
        rows.append(f'(:FUNCTION {obj(name)} :FORMALS {obj(formals)} :LOGICAL-BODY {obj(body)} '
                    f':GUARD {obj(cl("T"))} :ATTACHMENT {obj(cl("NIL"))})')
    if duplicate:
        rows.append(rows[0])
    return '(:PACKET :REFUSED () :FUNCTIONS (' + ' '.join(rows) + ') :KIND ' + obj('NIL') + ')'


class ClosedMember(unittest.TestCase):
    def proposal(self, **kw):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'fixture.sexp'
            source.write_text(packet(**kw))
            return c.closed_member_source(source, ['FN2-ACCEPT-ROUTE'])

    def test_exact_program_and_domain_premises(self):
        source = self.proposal()
        self.assertIn('"FN2-ACCEPT-ROUTE" => some', source)
        self.assertIn('program_extension_of_lookups', source)
        self.assertEqual(source.count('  · rfl'), 5)
        self.assertIn('MemberExecEvaluation.domain name values → domain name values', source)
        self.assertIn('MemberExecEvaluation.primitiveDomain name values → primitiveDomain name values', source)
        self.assertIn('public import Fn2.ACL2.MemberBodyCorrect', source)
        self.assertIn('CanonicalBodyCorrect program domain primitiveDomain LayerAWorld.fns', source)
        self.assertIn('MemberBodyCorrect.body_correct_in_program member_records calls primitives memberInputs', source)
        self.assertIn('domain "MEMBER-EQ-EXEC" values → MemberExecEvaluation.domain "MEMBER-EQ-EXEC" values', source)
        self.assertNotIn('axiom ', source)
        self.assertNotIn('sorry', source)

    def test_mutation_reaches_kernel_obligation(self):
        self.assertNotEqual(self.proposal(), self.proposal(mutate=True))
        self.assertIn('program_extension_of_lookups', self.proposal(mutate=True))

    def test_duplicate_subject_refused(self):
        with self.assertRaisesRegex(ValueError, 'duplicate decoded canonical function subject'):
            self.proposal(duplicate=True)

    def test_missing_member_closure_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'fixture.sexp'
            source.write_text(packet())
            with self.assertRaisesRegex(ValueError, 'member closure missing'):
                c.closed_member_source(source, ['NOT'])


class ScopedQualification(unittest.TestCase):
    def source(self, roots=None):
        roots = ['FN2-ACCEPT-ROUTE'] if roots is None else roots
        return packet().replace(':PACKET', ':FN2-CERTIFICATE :VERSION 1', 1).replace(
            ':REFUSED', ':ROOTS (' + ' '.join(obj(x) for x in roots) +
            ') :MANIFEST () :NATIVES () :REFUSED', 1)

    def book(self, text, roots=None):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / 'fixture.sexp'
            source.write_text(text)
            return c.closed_member_book(source, roots or ['FN2-ACCEPT-ROUTE'],
                                        Path(directory) / 'scoped.lisp')

    def test_all_records_qualified_with_correct_macro_abi(self):
        book = self.book(self.source())
        forms = c.read_all(book)
        checks = [f for f in forms if isinstance(f, c.List) and f and
                  str(f[0]).upper() == 'FN2-TV-CHECK-FUNCTION']
        self.assertEqual(len(checks), 6)
        # Macro ABI is (entry fn), not the natural-language (fn entry).
        self.assertEqual(str(checks[0][1][0]), 'QUOTE')
        self.assertEqual(str(checks[0][1][1][0]), ':FUNCTION')
        self.assertEqual(str(checks[0][2][1]), 'NOT')
        self.assertIn('fn2-tv-closed-functions names (append names natives)', book)
        self.assertIn('subsetp-eq *fn2-tv-native-boundary* natives', book)
        self.assertIn('fn2-tv-check-manifest', book)

    def test_extra_guard_record_is_not_dropped_with_body_selection(self):
        text = self.source()
        extra = '(:FUNCTION ' + obj('GUARD-ONLY') + ' :FORMALS ' + obj([]) + \
                ' :LOGICAL-BODY ' + obj('COMMON-LISP::T') + ' :GUARD ' + \
                obj('COMMON-LISP::T') + ' :ATTACHMENT ' + obj('COMMON-LISP::NIL') + ')'
        text = text.replace(':FUNCTIONS (', ':FUNCTIONS (' + extra + ' ', 1)
        self.assertIn("'GUARD-ONLY)", self.book(text))
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / 'fixture.sexp'
            src.write_text(text)
            lean = c.closed_member_source(src, ['FN2-ACCEPT-ROUTE'])
            self.assertEqual(lean.count('  | "GUARD-ONLY" => some'), 2)
            self.assertIn('def guards : CanonicalGuards', lean)

    def guarded_packet(self, *, missing=False, attached=False, false_guard=False):
        parsed = c.read_canonical(self.source())
        packet_fields = c.fields(parsed[1:])
        rows = packet_fields[':FUNCTIONS']
        root = rows[-1]
        root[root.index(c.Atom(':GUARD')) + 1] = c.read_canonical(
            obj(['GUARD-ONLY', 'X']) if not false_guard else obj(['COMMON-LISP::QUOTE', 'COMMON-LISP::NIL']))
        if not missing:
            helper = c.read_canonical('(:FUNCTION ' + obj('GUARD-ONLY') +
                ' :FORMALS ' + obj(['X']) + ' :LOGICAL-BODY ' + obj(['COMMON-LISP::INTEGERP', 'X']) +
                ' :GUARD ' + obj('COMMON-LISP::T') + ' :ATTACHMENT ' +
                obj('GUARD-IMPLEMENTATION' if attached else 'COMMON-LISP::NIL') + ')')
            rows.append(helper)
        return c.canonical_text(parsed)

    def guarded_lean(self, **kw):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / 'fixture.sexp'
            src.write_text(self.guarded_packet(**kw))
            return c.closed_member_source(src, ['FN2-ACCEPT-ROUTE'])

    def test_reached_guard_helper_has_body_and_exact_guard(self):
        source = self.guarded_lean()
        program, guards = source.split('def guards : CanonicalGuards')
        self.assertIn('  | "GUARD-ONLY" => some', program)
        self.assertIn('  | "GUARD-ONLY" => some', guards)
        expected = c.lean_object(c.read_canonical(obj(['GUARD-ONLY', 'X'])))
        self.assertIn('  | "FN2-ACCEPT-ROUTE" => some ⟨["X", "LST"], ' + expected, guards)
        # Changing ONLY the canonical root guard must change the Lean subject.
        changed = self.guarded_lean(false_guard=True)
        self.assertEqual(program, changed.split('def guards : CanonicalGuards')[0])
        self.assertNotEqual(source, changed)

    def test_missing_guard_dependency_refused(self):
        with self.assertRaisesRegex(ValueError, 'missing canonical body/guard callees.*GUARD-ONLY'):
            self.guarded_lean(missing=True)

    def test_attached_guard_helper_not_treated_as_logical_body(self):
        with self.assertRaisesRegex(ValueError, 'attached canonical body/guard callee GUARD-ONLY'):
            self.guarded_lean(attached=True)

    def test_wrong_or_duplicate_root_census_refused(self):
        for roots in (['NOT'], ['FN2-ACCEPT-ROUTE', 'NOT'],
                      ['FN2-ACCEPT-ROUTE', 'FN2-ACCEPT-ROUTE']):
            with self.assertRaisesRegex(ValueError, 'root census'):
                self.book(self.source(roots))

    def test_nonpacket_and_future_version_refused(self):
        for text in (packet(), self.source().replace(':VERSION 1', ':VERSION 2')):
            with self.assertRaises(ValueError):
                self.book(text)

    def test_packet_replaced_between_outputs_keeps_original_pair(self):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / 'fixture.sexp'
            lean = Path(directory) / 'Member.lean'
            book = Path(directory) / 'member.lisp'
            original = self.source()
            # A different root census must fail if either later stage rereads.
            replacement = self.source(['NOT'])
            src.write_text(original)
            expected_lean = c.closed_member_source(src, ['FN2-ACCEPT-ROUTE'])
            expected_book = c.closed_member_book(src, ['FN2-ACCEPT-ROUTE'], book)
            generate_lean = c.closed_member_source
            def replace_after_lean(*args, **kwargs):
                result = generate_lean(*args, **kwargs)
                src.write_text(replacement)
                return result
            with mock.patch.object(c, 'closed_member_source', side_effect=replace_after_lean):
                c.cli(['--root', 'FN2-ACCEPT-ROUTE', '--closed-member-output', str(lean),
                       '--closed-member-book', str(book), str(src)])
            self.assertEqual(src.read_text(), replacement)
            self.assertEqual(lean.read_text(), expected_lean)
            self.assertEqual(book.read_text(), expected_book)
            # The replacement remains independently inadmissible for that root.
            with self.assertRaisesRegex(ValueError, 'root census'):
                c.closed_member_book(src, ['FN2-ACCEPT-ROUTE'], book)

    def test_companion_replacement_before_inspection_keeps_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / 'fixture.sexp'
            book = Path(directory) / 'member.lisp'
            original = self.source()
            src.write_text(original)
            expected = c.closed_member_book(src, ['FN2-ACCEPT-ROUTE'], book)
            inspect = c.inspect_core_certificate
            def replace_before_inspection(*args, **kwargs):
                src.write_text('(:BROKEN)')
                return inspect(*args, **kwargs)
            with mock.patch.object(c, 'inspect_core_certificate', side_effect=replace_before_inspection):
                actual = c.closed_member_book(src, ['FN2-ACCEPT-ROUTE'], book)
            self.assertEqual(actual, expected)
            self.assertEqual(src.read_text(), '(:BROKEN)')

    def test_refusal_leaves_neither_proposal_written(self):
        with tempfile.TemporaryDirectory() as directory:
            src = Path(directory) / 'fixture.sexp'
            lean = Path(directory) / 'Member.lean'
            book = Path(directory) / 'member.lisp'
            src.write_text(self.source(['NOT']))
            with self.assertRaisesRegex(ValueError, 'root census'):
                c.cli(['--root', 'FN2-ACCEPT-ROUTE', '--closed-member-output', str(lean),
                       '--closed-member-book', str(book), str(src)])
            self.assertFalse(lean.exists())
            self.assertFalse(book.exists())


if __name__ == '__main__':
    unittest.main()
