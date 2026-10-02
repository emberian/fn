"""Exact path values are reported; registry prose is never evaluated."""
import contextlib
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from tools import registry_paths_report as report


class RegistryPaths(unittest.TestCase):
    def test_resolvable_dangling_and_shrink_only_check(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            (root / 'books').mkdir()
            (root / 'books/exists.lisp').write_text('(in-package "ACL2")')
            subprocess.run(['git', '-C', str(root), 'add', 'books'], check=True)
            (root / 'planning').mkdir()
            registry = root / 'planning/requirements.json'
            registry.write_text(json.dumps({'requirements': [{'id': 'REQ-1', 'evidence': [
                'books/exists.lisp', 'books/missing.lisp'],
                'note': 'prose mentions books/not-a-target.lisp; never evaluate'}]}))
            (root / 'planning/proofs.json').write_text('{"proofs":[]}')
            findings = report.collect(root)
            self.assertEqual([row['path'] for row in findings], ['books/missing.lisp'])
            self.assertEqual(findings[0]['disposition'], 'RETIRE')
            self.assertIn('REQ-1', str(findings[0]['sites']))
            baseline = root / 'baseline.json'
            baseline.write_text('{"maximum_dangling":1}')
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(report.main(['--root', str(root), '--baseline', str(baseline), '--check']), 0)
                baseline.write_text('{"maximum_dangling":0}')
                self.assertEqual(report.main(['--root', str(root), '--baseline', str(baseline), '--check']), 1)

    def test_index_names_and_unique_basename_dispositions(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            (root / 'tests/new').mkdir(parents=True)
            (root / 'tests/new/moved.py').write_text('')
            subprocess.run(['git', '-C', str(root), 'add', 'tests'], check=True)
            (root / 'planning').mkdir()
            (root / 'planning/evidence-index.tsv').write_text('a' * 64 + ' 2 planning/evidence/kept.json\n')
            (root / 'planning/proofs.json').write_text(json.dumps({'proofs': [{'id': 'P1', 'evidence': [
                'tests/old/moved.py', 'planning/evidence/kept.json', 'planning/evidence/lost.json']}]}))
            (root / 'planning/requirements.json').write_text('{}')
            findings = {r['path']: r['disposition'] for r in report.collect(root)}
            self.assertEqual(findings, {'tests/old/moved.py': 'RENAMED-TO tests/new/moved.py',
                                       'planning/evidence/lost.json': 'UNINDEXED-EVIDENCE'})

    def test_git_rename_with_changed_basename_and_baseline_increase(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            (root / 'tests').mkdir()
            (root / 'tests/old.py').write_text('# distinctive tracked source\n' * 5)
            (root / 'planning').mkdir()
            (root / 'planning/requirements.json').write_text('{"evidence":["tests/old.py"]}')
            (root / 'planning/proofs.json').write_text('{}')
            (root / 'baseline.json').write_text('{"maximum_dangling":1}')
            def commit():
                subprocess.run(['git', '-C', str(root), 'add', '.'], check=True)
                subprocess.run(['git', '-C', str(root), '-c', 'user.name=test', '-c', 'user.email=test@example',
                                '-c', 'core.hooksPath=/dev/null', 'commit', '--no-gpg-sign', '-qm', 'fixture'], check=True)
            commit()
            (root / 'tests/old.py').rename(root / 'tests/new.py')
            commit()
            self.assertEqual(report.collect(root)[0]['disposition'], 'RENAMED-TO tests/new.py')
            (root / 'baseline.json').write_text('{"maximum_dangling":2}')
            with contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(report.main(['--root', str(root), '--baseline', str(root / 'baseline.json'), '--check']), 1)
            self.assertIn('RegistryPathsBaselineIncrease', output.getvalue())
