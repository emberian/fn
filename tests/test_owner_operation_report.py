"""Execute literal diagnostic and CLI projection definitions, without a saved image."""
import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('diagnostics', ROOT / 'tests/test_operation_diagnostics_boundary.py')
diag = importlib.util.module_from_spec(spec)
spec.loader.exec_module(diag)

class OperationReport(unittest.TestCase):
    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required')
    def test_current_state_report_and_operator_route(self):
        selections = {
            'books/operation-diagnostics.lisp': ['fn-od-word', 'fn-od-nat-fits-p', 'fn-od-digits', 'fn-od-nat', 'fn-od-value', 'fn-od-fields'],
            'books/page-read-ledger.lisp': ['fn-prl-nth'],
            'books/admission-preallocation-resources.lisp': ['fn-apr-widthp', 'fn-apr-naturals', 'fn-apr-tokenp', 'fn-apr-livep', 'fn-apr-owner-current'],
            'books/owner-canonical-epoch.lisp': ['fn-owner-canonical-epoch'],
            'books/history-semantic-writer.lisp': ['fn-hsw-parentp', 'fn-hsw-gate'],
            'books/history-semantic-writer-state.lisp': ['fn-owner-history-writer-gate'],
            'host/native-live-status-host.lisp': ['fn-native-operation-host-report', 'fn-native-operation-host-offline', 'fn-native-live-status-host-answer'],
            'books/owner-operation-report.lisp': ['fn-oor-report', 'fn-owner-operation-report'],
            'books/native-live-status.lisp': ['fn-nls-kind-code', 'fn-nls-code-kind', 'fn-nls-buffer', 'fn-nls-page', 'fn-nls-cached-buffer', 'fn-nls-cache-put'],
            'books/native-operator.lisp': ['fn-nop-result', 'fn-native-operator-result-status', 'fn-native-operator-result-command', 'fn-native-operator-result-arguments', 'fn-native-operator-result-status-planp', 'fn-native-operator-result-status-kind', 'fn-nop-parse-command', 'fn-native-operator-result-native-action'],
        }
        source = '\n'.join(diag.selected(ROOT / file, names) for file, names in selections.items())
        fixture = (ROOT / 'tests/fixtures/owner_operation_report.lisp').read_text()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / 'source.lisp').write_text(source)
            (path / 'run.lisp').write_text(fixture.replace('__SOURCE_FILE__', str(path / 'source.lisp')))
            run = subprocess.run([shutil.which('sbcl'), '--noinform', '--disable-debugger', '--script', str(path / 'run.lisp')], capture_output=True, text=True, timeout=30)
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn('PASS actual operation report', run.stdout)

if __name__ == '__main__':
    unittest.main()
