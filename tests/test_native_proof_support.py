"""Source/hook controls; no claim that an unexecuted hook is proof evidence."""
from pathlib import Path
from unittest import mock
import tempfile
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import ledger
import capture_native_proof_support as capture
import assurance_dependencies as dependencies
S = ledger.Sym

class NativeProofSupport(unittest.TestCase):
    def test_hook_uses_exact_current_formula_and_actual_metadata(self):
        ident, formula = capture.identity(ROOT)
        text = capture.hook(ROOT, Path('/tmp/native-support.lsp'))
        forms = ledger.read_forms(text)
        self.assertEqual(len(forms), 4)
        self.assertEqual(ledger.head(forms[-1]), 'mv-let')
        self.assertNotIn('open-output-channel', ledger.source_text(forms[2]))
        self.assertIn(ledger.source_text(formula), text)
        for actual in ('getpropc', 'all-vars', 'fn2-proof-support-node',
                       'fn2-proof-assumption-contexts', '(equal actual translated)',
                       'print-object$', ':object'):
            self.assertIn(actual, text)
        self.assertNotIn(':depends', text)
        self.assertNotIn('skip-proofs', text)
        self.assertEqual(ident[3], S(capture.SUBJECT.lower()))

    def test_snapshot_identity_and_support_redirects_refused(self):
        ident, _ = capture.identity(ROOT)
        report = [S(':kind'), S(':live-event-proof-support-projection'),
                  S(':roots'), [S(capture.SUBJECT)], S(':named-assumption-subjects'), [S(capture.ASSUMPTION)],
                  S(':complete'), S('nil'), S(':limitations'), [S(':absent-support-is-unknown')],
                  S(':nodes'), [[S(':name'), S(capture.SUBJECT), S(':support-state'), S(':recorded-event-support'),
                                 S(':supporters'), [S(capture.SUPPORT)]],
                                [S(':name'), S(capture.SUPPORT), S(':theorem'), [S('equal'), S('x'), S('x')], S(':constraint-contexts'),
                                 [[S(':subject'), S(capture.ASSUMPTION), S(':status'), S(':exact-live-constraint-theorem'),
                                   S(':constraints'), [[S('equal'), S('x'), S('x')]],
                                   S(':origins'), [[S('theorem'), S(capture.SUPPORT)]]]]]]]
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / 'snapshot'
            def write(identity, payload):
                path.write_text(ledger.source_text([S(':kind'), S(':source-admitted-proof-support'),
                                S(':identity'), identity, S(':report'), payload]))
            write(ident, report)
            self.assertEqual(dependencies.live_support_snapshot(path, source_root=ROOT)
                             ['actual_theorem_constraint_dependency_closure'], 'unresolved')
            with self.assertRaises(ValueError):
                dependencies.live_support_snapshot(path)
            for index in (1, 2, 3, 4, 5, 6, 7):
                wrong = ident.copy();wrong[index] = 'wrong'
                write(wrong, report)
                with self.assertRaises(ValueError):capture.validate_capture(ROOT, path)
            for old, new in ((capture.SUBJECT, 'OTHER'), (capture.SUPPORT, 'UNRELATED'),
                             (':recorded-event-support', ':absent-or-empty-unknown'),
                             (':exact-live-constraint-theorem', ':not-this-constraint-theorem')):
                write(ident, report)
                # Change nested payload only, leaving current identity intact.
                row = ledger.read_forms(path.read_text())[0]
                nested = ledger.source_text(row[5]).replace(old.lower(), new.lower())
                row[5] = ledger.read_forms(nested)[0]
                path.write_text(ledger.source_text(row))
                with self.assertRaises(ValueError):capture.validate_capture(ROOT, path)

if __name__ == '__main__':unittest.main()
