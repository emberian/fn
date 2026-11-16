"""Evidence oracle and loader controls; no ACL2 or native node execution."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, Path(__file__).with_name(filename))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


campaign = load('large_restart', 'native-large-article-restart.py')
launcher = load('rolling_launcher', 'native-rolling-launcher.py')


class ResetEvidence(unittest.TestCase):
    def check(self, rows):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'resets.jsonl'
            path.write_text(''.join(json.dumps(row) + '\n' for row in rows))
            return campaign.reset_evidence(path, (91, 92))

    def rows(self):
        return [dict(result='OK', before=[2, 9, 17, 3, op, op, n], after=[2, 9, 17, 3, op, op, n + 1])
                for op in (91, 92) for n in (0, 1)]

    def test_real_changes_required_under_each_identity(self):
        self.assertEqual(len(self.check(self.rows())), 2)
        noop = self.rows()
        for row in noop:
            row['after'] = list(row['before'])
        with self.assertRaises(AssertionError):
            self.check(noop)
        for field in (0, 1, 4, 5):
            changed = self.rows()
            changed[1]['before'][field] += 1
            changed[1]['after'][field] += 1
            with self.assertRaises(AssertionError):
                self.check(changed)
        changed = self.rows()
        changed[1]['after'][-1] += 1
        with self.assertRaises(AssertionError):
            self.check(changed)

    def test_launchers_must_be_executable_before_image_creation(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'tests').mkdir()
            real = root / 'qualified-acl2'
            observer = root / 'tests/native-rolling-launcher.py'
            for path in (real, observer):
                path.write_text('#!/bin/sh\nexit 0\n')
                path.chmod(0o700)
            with mock.patch.object(campaign, 'ROOT', root), \
                 mock.patch.dict(campaign.os.environ, {'FN_ACL2': str(real)}):
                self.assertEqual(campaign.selected_launchers(), (real.resolve(), observer.resolve()))
                for path in (observer, real):
                    path.chmod(0o600)
                    with self.assertRaises(PermissionError):
                        campaign.selected_launchers()
                    path.chmod(0o700)
                with mock.patch.dict(campaign.os.environ, {'FN_ACL2': str(observer)}):
                    with self.assertRaises(ValueError):
                        campaign.selected_launchers()

    def test_loader_inserts_only_observer_before_actual_entry(self):
        source = (campaign.ROOT / 'tools/image-node.lsp').read_bytes()
        observed = launcher.observed_script(source)
        insertion = b'(load "tests/native-upload-reset-capture.lsp")\n'
        self.assertEqual(observed.count(insertion), 1)
        self.assertEqual(observed.replace(insertion, b''), source)
        for wrong in (b'', source + source):
            with self.assertRaises(ValueError):
                launcher.observed_script(wrong)


if __name__ == '__main__':
    unittest.main()
