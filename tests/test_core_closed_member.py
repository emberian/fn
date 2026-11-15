"""Packet-to-proof controls; fixtures are not current ACL2 exports."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

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


if __name__ == '__main__':
    unittest.main()
