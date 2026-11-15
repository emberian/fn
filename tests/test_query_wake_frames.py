"""Original runtime/guards/shape identity plus selective frame mutation controls."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
BASELINE = '0b84789e4f10349150c002e302bfc476db6b2817'

@unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for source controls')
class QueryWakeFrames(unittest.TestCase):
    def control(self, mutation=''):
        with tempfile.TemporaryDirectory(prefix='fn-query-wake-') as temp:
            env = {**os.environ, 'FN_BIND_MUTATION': mutation}
            for name, variable in [('machines-c-bind', 'FN_BIND_BASELINE'),
                                   ('machines-c-groups', 'FN_GROUPS_BASELINE')]:
                path = Path(temp) / (name + '.lisp')
                path.write_bytes(subprocess.check_output(['git', 'show', f'{BASELINE}:books/{name}.lisp'], cwd=ROOT))
                env[variable] = str(path)
            return subprocess.run(['sbcl', '--noinform', '--script', 'tests/query-wake-frame-controls.lsp'],
                cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT, timeout=20)

    def test_original_runtime_guards_shape_and_exact_frame_statements(self):
        result = self.control()
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn('QUERY WAKE FRAME CONTROLS PASS', result.stdout)

    def test_runtime_mutation_refused(self):
        self.assertNotEqual(self.control('runtime').returncode, 0)

    def test_original_shape_hypothesis_removal_refused(self):
        self.assertNotEqual(self.control('hyps').returncode, 0)

    def test_bind_guard_mutation_refused(self):
        self.assertNotEqual(self.control('guard').returncode, 0)

    def test_group_guard_mutation_refused(self):
        self.assertNotEqual(self.control('group-guard').returncode, 0)

    def test_wrong_frame_statement_refused(self):
        self.assertNotEqual(self.control('frame').returncode, 0)

if __name__ == '__main__':
    unittest.main()
