"""Synthetic packet refusal controls; no claim of an admitted served export."""
import importlib.util
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).parents[1] / 'meta/emit'))
import emit_served_member_binding as s
spec = importlib.util.spec_from_file_location('fixtures', Path(__file__).with_name('test_core_closed_member.py'))
fixtures = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixtures)
obj = fixtures.obj


def packet(selector=s.RUN, broken_path=False, wrong_abi=False, package='ACL2'):
    rows = []
    definitions = {
        s.STUB: (['ID', 'BUDGET', 'CORE'], ['COMMON-LISP::QUOTE', 'COMMON-LISP::NIL']),
        s.RUN: (['ID', 'BUDGET', 'CORE'], [s.ITEM, 'ID', 'CORE']),
        s.ITEM: (['ID', 'CORE'], ['COMMON-LISP::QUOTE', 'COMMON-LISP::NIL'] if broken_path else
                 [s.ANSWER, 'ID', 'ID', 'ID', 'ID', 'ID', 'ID']),
        s.ANSWER: (['LIVE', 'OK0', 'RC', 'CODE', 'FITS', 'CC'],
                   ['MEMBER-EQUAL', 'RC', ['COMMON-LISP::QUOTE', ['KEYWORD::SIZE', 'KEYWORD::FULL']]]),
        'FN2-CNS-RUN-ALTERNATE': (['ID', 'BUDGET', 'CORE'], ['COMMON-LISP::QUOTE', 'COMMON-LISP::NIL']),
    }
    for name, (formals, body) in definitions.items():
        attachment = (f'(:CONS {obj(package + "::" + s.STUB)} {obj(selector)})'
                      if name == s.STUB else obj('COMMON-LISP::NIL'))
        if wrong_abi and name == s.RUN:
            formals = ['ID']
        rows.append(f'(:FUNCTION {obj(name)} :FORMALS {obj(formals)} '
                    f':LOGICAL-BODY {obj(body)} :GUARD {obj("COMMON-LISP::T")} '
                    f':STOBJS-IN {obj([])} :STOBJS-OUT {obj([])} :ATTACHMENT {attachment})')
    return ('(:FN2-CERTIFICATE :VERSION 1 :ROOTS (' + obj(s.STUB) + ') '
            ':REFUSED () :MANIFEST () :NATIVES () :FUNCTIONS (' + ' '.join(rows) + '))')


class ServedSelection(unittest.TestCase):
    def test_actual_named_path_and_live_attachment_replay(self):
        text = s.qualification_book(packet(), Path('/tmp/served-binding.lisp'))
        self.assertIn('FN2-CNS-RUN -> FN2-CNS-PUT-ITEM -> FN2-CNS-PUT-ANSWER', text)
        self.assertIn('(fn2-tv-attachment \'fn2-cns-run-stub (w state))', text)
        self.assertEqual(text.count('(fn2-tv-check-function '), 5)
        self.assertIn('fn2-tv-closed-functions', text)
        self.assertIn('(equal (fn2-tv-object *fn2-tv-native-boundary*)', text)
        self.assertIn('no guard, primitive, or served-behavior discharge', text)

    def test_context_uses_actual_body_and_unconditional_member_bridge(self):
        source = s.member_context_source(packet())
        self.assertIn('MemberBodyCorrect.emitted_eq_native', source)
        self.assertIn('«FN2-CNS-PUT-ANSWER»', source)
        self.assertIn('«MEMBER-EQ-EXEC» «RC»', source)
        self.assertIn('canonicalAnswer : Object', source)
        self.assertIn('reached_comparison_domains (rc : Val)', source)
        self.assertIn('symbolEqualDomain "EQUAL" [rc, (Val.sym ":SIZE")]', source)
        self.assertNotIn('sorry', source)
        self.assertNotIn('axiom ', source)

    def test_missing_member_site_does_not_generate_context(self):
        text = packet().replace(obj('MEMBER-EQUAL'), obj('EQUAL'))
        with self.assertRaisesRegex(ValueError, 'exactly one logical MEMBER'):
            s.member_context_source(text)

    def test_make_event_both_branches_return_error_triples(self):
        from emit_certificate import read_all
        text = s.qualification_book(packet(), Path('/tmp/served-binding.lisp'))
        event = next(f for f in read_all(text) if f[0] == 'make-event')
        branch = event[1]
        self.assertEqual(branch[0], 'if')
        self.assertEqual(branch[2][0], 'value')
        self.assertEqual(branch[3][:2], ['er', 'soft'])

    def test_actual_member_lambda_and_nonliteral_refusal(self):
        from emit_certificate import decode, read_canonical
        body = decode(read_canonical(obj([
            ['COMMON-LISP::LAMBDA', ['X', 'L'], ['MEMBER-EQUAL', 'X', 'L']],
            'RC', ['COMMON-LISP::QUOTE', ['KEYWORD::SIZE', 'KEYWORD::FULL']]])))
        self.assertEqual(list(map(str, s.member_literal_site(body))), [':SIZE', ':FULL'])
        body[2] = decode(read_canonical(obj('DYNAMIC-LIST')))
        with self.assertRaisesRegex(ValueError, 'not literal'):
            s.member_literal_site(body)

    def test_same_abi_wrong_selector_refused(self):
        with self.assertRaisesRegex(ValueError, 'selector differs'):
            s.inspect(packet(selector='FN2-CNS-RUN-ALTERNATE'))

    def test_same_spelling_wrong_package_refused(self):
        with self.assertRaisesRegex(ValueError, 'selector differs'):
            s.inspect(packet(package='COMMON-LISP'))

    def test_disconnected_real_helper_refused(self):
        with self.assertRaisesRegex(ValueError, 'logical call path'):
            s.inspect(packet(broken_path=True))

    def test_wrong_selected_abi_refused(self):
        with self.assertRaisesRegex(ValueError, 'ABI differs'):
            s.inspect(packet(wrong_abi=True))


if __name__ == '__main__':
    unittest.main()
