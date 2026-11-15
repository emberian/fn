"""Source structure controls; actual ACL2 behavior lives in the two unit books."""
from pathlib import Path
import sys
import unittest
import tempfile
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import ledger
import assurance_dependencies as dependencies

class ProofSupportSource(unittest.TestCase):
    def test_all_new_books_parse(self):
        for relative in ('books/assurance-proof-support.lisp',
                         'tests/assurance-proof-support-unit.lisp',
                         'tests/assurance-proof-support-import-unit.lisp'):
            self.assertTrue(ledger.read_forms((ROOT / relative).read_text()))

    def test_report_never_claims_completeness(self):
        forms = ledger.read_forms((ROOT / 'books/assurance-proof-support.lisp').read_text())
        report = next(f for f in forms if ledger.head(f) == 'defun' and
                      str(f[1]).lower() == 'fn2-proof-support-report')
        body = report[-1]
        self.assertEqual(str(body[body.index(ledger.Sym(':complete')) + 1]).lower(), 'nil')

    def test_snapshot_preserves_partial_scope_and_rejects_complete_bit(self):
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / 'support.lsp'
            prefix = '(:kind :live-event-proof-support-projection :roots (actual) :named-assumption-subjects (a) :limitations (:absent-support-is-unknown) :nodes nil :complete '
            path.write_text(prefix + 'nil)')
            report = dependencies.live_support_snapshot(path)
            self.assertEqual(report['actual_theorem_constraint_dependency_closure'], 'unresolved')
            for suffix in ('t)', 'nil :complete nil)', ')'):
                path.write_text(prefix + suffix)
                with self.assertRaises((ValueError, IndexError)):
                    dependencies.live_support_snapshot(path)

    def test_no_authored_dependency_or_callgraph_in_extractor(self):
        forms = ledger.read_forms((ROOT / 'books/assurance-proof-support.lisp').read_text())
        def atoms(x):
            if isinstance(x, list):
                return [a for v in x for a in atoms(v)]
            return [str(x).lower()] if isinstance(x, ledger.Sym) else []
        names = atoms(forms)
        for forbidden in (':depends', 'all-fnnames', 'skip-proofs', 'defaxiom', ':program'):
            self.assertNotIn(forbidden, names)
        self.assertIn('constraint-info', names)
        self.assertIn('proof-supporters-alist', names)

if __name__ == '__main__':
    unittest.main()
