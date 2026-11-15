from pathlib import Path
import concurrent.futures
import hashlib
import subprocess
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import checked_queue as cq


class CheckedQueue(unittest.TestCase):
    def fixture(self, root):
        script = root / 'retry.py'
        candidate = root / 'candidate.lisp'
        script.write_text('import pathlib,sys\nprint(pathlib.Path(sys.argv[1]).read_text())\n')
        candidate.write_text('APPROVED')
        files = {name: {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                 for name, path in [('retry', script), ('candidate', candidate)]}
        return {'argv': [sys.executable, '{retry}', '{candidate}'], 'files': files}

    def test_missing_or_truncated_dependency_never_publishes(self):
        for failure in ['missing', 'truncated']:
            with self.subTest(failure=failure), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                manifest = self.fixture(root)
                candidate = root / 'candidate.lisp'
                if failure == 'missing':
                    candidate.unlink()
                else:
                    candidate.write_text('APP')
                with self.assertRaises((FileNotFoundError, ValueError)):
                    cq.publish(manifest, root / 'bundles', root / 'queue')
                self.assertFalse((root / 'queue').exists())

    def test_consumed_or_replaced_originals_do_not_change_execution(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = self.fixture(root)
            queue = root / 'queue'
            cq.publish(manifest, root / 'bundles', queue)
            # Same failure family as consuming retry.sh under a new queue name.
            (root / 'retry.py').rename(root / 'consumed-running.py')
            (root / 'candidate.lisp').write_text('REPLACED AFTER PUBLICATION')
            queue.rename(root / 'running.sh')
            result = subprocess.run(['sh', str(root / 'running.sh')], capture_output=True,
                                    text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), 'APPROVED')

    def test_complete_two_script_chain_uses_only_bundled_dependencies(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            stage = root / 'with-frame.sh'
            retry = root / 'retry.sh'
            candidate = root / 'candidate.lisp'
            executor = root / 'fake-executor.py'
            stage.write_text('set -eu\n"$1" "$2" proper-frame\nbash "$3" "$4" "$1" "$2"\n')
            retry.write_text('set -eu\n"$2" "$3" "checkpoint:$(cat "$1")"\n')
            candidate.write_text('APPROVED')
            executor.write_text('import sys\nprint(sys.argv[1])\n')
            files = {name: {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
                     for name, path in [('stage', stage), ('retry', retry),
                                        ('candidate', candidate), ('executor', executor)]}
            manifest = {'argv': ['bash', '{stage}', sys.executable, '{executor}', '{retry}', '{candidate}'],
                        'files': files}
            cq.publish(manifest, root / 'bundles', root / 'queue')
            stage.rename(root / 'stage-consumed.sh')
            retry.rename(root / 'retry-consumed.sh')
            candidate.unlink()
            executor.write_text('raise RuntimeError("original replaced")')
            result = subprocess.run(['sh', str(root / 'queue')], capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.splitlines(), ['proper-frame', 'checkpoint:APPROVED'])

    def test_parallel_publication_is_complete_and_never_clobbers(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = self.fixture(root)
            # Prepare once: this test isolates the actual no-clobber queue race.
            cq.prepare(manifest, root / 'bundles')
            def attempt():
                try:
                    cq.publish(manifest, root / 'bundles', root / 'queue')
                    return True
                except FileExistsError:
                    return False
            with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
                self.assertEqual(sorted(executor.map(lambda _: attempt(), range(2))), [False, True])
            result = subprocess.run(['sh', str(root / 'queue')], capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), 'APPROVED')

    def test_corrupted_bundle_is_refused_before_command_runs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = self.fixture(root)
            bundle = cq.publish(manifest, root / 'bundles', root / 'queue')
            path = bundle / 'candidate'
            path.chmod(0o644)
            path.write_text('CORRUPT')
            result = subprocess.run(['sh', str(root / 'queue')], capture_output=True, text=True, timeout=10)
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn('APPROVED', result.stdout)

    def test_incomplete_placeholder_inventory_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            manifest = self.fixture(root)
            manifest['argv'] = [sys.executable, '{retry}']
            with self.assertRaises(ValueError):
                cq.publish(manifest, root / 'bundles', root / 'queue')


if __name__ == '__main__':
    unittest.main()
