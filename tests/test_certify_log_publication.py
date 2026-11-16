"""Finalized evidence stays readable while a replacement is published."""
import ast
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import certify_books as cb


class LogPublication(unittest.TestCase):
    book = 'books/example'
    nonce = 'publication-test'

    def payload(self):
        return 'complete proof output\n' + cb.success_token(self.book, self.nonce) + '\n'

    def test_terminal_activity_never_exposes_truncated_replacement(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            log = root / 'books--example.certify.log'
            # Execute a Python output fixture, not ACL2. Include invalid UTF-8
            # to exercise the runner's unchanged replacement-decoding path.
            raw = b'\xff' + self.payload().encode()
            driver = 'import sys; sys.stdout.buffer.write(' + repr(raw) + ')'
            with patch.object(cb, 'ROOT', root), patch.object(cb.acl2_slots, 'acl2_environment', return_value=os.environ.copy()):
                result = cb.run_acl2(Path(sys.executable), driver, 5, log_path=log, book=self.book)
            activity = json.loads(log.with_name('books--example.active.json').read_text())
            self.assertEqual(activity['status'], 'exited')
            self.assertEqual(result.stdout, raw)
            normalized = result.stdout.decode('utf-8', errors='replace')
            before_replace, finish = threading.Event(), threading.Event()
            failures = []
            replace = Path.replace

            def paused_replace(source, target):
                if Path(target) == log:
                    # A finalizer has written and closed its temporary file.
                    self.assertEqual(source.read_text(), normalized)
                    before_replace.set()
                    if not finish.wait(5):
                        raise AssertionError('reader did not release publication')
                return replace(source, target)

            def publish():
                try:
                    cb.certs.write_text_atomic(log, normalized)
                except BaseException as error:
                    failures.append(error)

            with log.open('rb') as old_reader, patch.object(Path, 'replace', paused_replace):
                thread = threading.Thread(target=publish)
                thread.start()
                try:
                    self.assertTrue(before_replace.wait(5))
                    # Deterministic watcher ordering: terminal status was
                    # observed, replacement is in progress, marker must exist.
                    self.assertEqual(log.read_bytes(), raw)
                    self.assertEqual(cb.book_result(self.book, log.read_text(errors='replace'), 0, self.nonce, True)[0], 'passed')
                finally:
                    finish.set()
                    thread.join(5)
                self.assertFalse(thread.is_alive())
                self.assertEqual(old_reader.read(), raw)
            self.assertEqual(failures, [])
            self.assertEqual(log.read_bytes(), normalized.encode())
            self.assertEqual(list(root.glob('*.tmp')), [])

    def test_old_in_place_rewrite_has_the_reported_counterexample(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'book.certify.log'
            log.write_text(self.payload())
            # Exact old ordering: the child exited with a complete log, then
            # Path.write_text opens it with truncation before writing output.
            with log.open('w') as output:
                observed = log.read_text()
                self.assertEqual(observed, '')
                self.assertEqual(cb.book_result(self.book, observed, 0, self.nonce, True)[0], 'failed')
                output.write(self.payload())
            self.assertEqual(cb.book_result(self.book, log.read_text(), 0, self.nonce, True)[0], 'passed')

    def test_timeout_partial_output_and_activity_are_preserved(self):
        partial = b'proof still running\n\xff'
        class TimeoutChild:
            pid = 12345
            returncode = None
            def __init__(self, *args, **kwargs):
                self.log = kwargs['stdout']
            def communicate(self, **kwargs):
                if self.returncode is None:
                    self.log.write(partial)
                    raise subprocess.TimeoutExpired(['fixture'], 1)
            def kill(self):
                self.returncode = -9
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'book.pcert-convert.certify.log'
            with patch.object(cb.subprocess, 'Popen', TimeoutChild):
                with self.assertRaises(subprocess.TimeoutExpired) as caught:
                    cb.run_acl2(Path('fixture'), 'driver', 1, log_path=log, book=self.book, wave='convert')
            self.assertEqual(cb.timeout_output(caught.exception), partial)
            state = json.loads(log.with_name('book.pcert-convert.active.json').read_text())
            self.assertEqual((state['status'], state['wave'], state['exit_code']), ('timed-out', 'convert', -9))
            normalized = partial.decode('utf-8', errors='replace')
            cb.certs.write_text_atomic(log, normalized)
            self.assertEqual(log.read_bytes(), normalized.encode())
            self.assertEqual(cb.book_result(self.book, normalized, 'timed out after 1 seconds', self.nonce, True)[0], 'failed')

    def test_pcert_combination_keeps_exact_markers(self):
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'book.certify.log'
            parts = []
            for wave in cb.PCERT_ORDER:
                parts.append(f'{cb.WAVE_PREFIX}{wave.upper()} {self.book}')
                parts.append(cb.success_token(self.book, self.nonce) if wave == 'complete'
                             else cb.wave_token(self.book, self.nonce, wave))
            combined = '\n'.join(parts)
            cb.certs.write_text_atomic(log, combined)
            self.assertEqual(log.read_bytes(), combined.encode())
            self.assertEqual(cb.success_markers(combined, self.nonce), [cb.success_token(self.book, self.nonce)])
            self.assertEqual(cb.book_result(self.book, combined, 0, self.nonce, True)[0], 'passed')

    def test_publication_failure_keeps_old_log_and_cleans_temporary(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); log = root / 'book.certify.log'
            log.write_text(self.payload())
            with patch.object(Path, 'replace', side_effect=OSError('publication fixture')):
                with self.assertRaises(OSError):
                    cb.certs.write_text_atomic(log, 'replacement')
            self.assertEqual(log.read_text(), self.payload())
            self.assertEqual(list(root.glob('*.tmp')), [])

    def test_runner_final_log_sites_use_atomic_publisher(self):
        # Exercise wiring as well as the shared helper: reverting any final
        # per-book/wave/aggregate log publication must fail this control.
        tree = ast.parse(Path(cb.__file__).read_text())
        functions = {node.name: node for node in ast.walk(tree) if isinstance(node, ast.FunctionDef)}
        for name in ('certify', 'run_wave', 'collect_pcert'):
            calls = [node for node in ast.walk(functions[name]) if isinstance(node, ast.Call)]
            self.assertFalse(any(isinstance(node.func, ast.Attribute) and node.func.attr == 'write_text' for node in calls if name != 'certify'))
            publishers = [node for node in calls if isinstance(node.func, ast.Attribute) and node.func.attr == 'write_text_atomic']
            self.assertEqual(len(publishers), 1, name)
        cb_source = Path(cb.__file__).read_text()
        self.assertNotIn('log_path.write_text(', cb_source)
        self.assertIn('certs.write_text_atomic(run_dir / "certify.log", combined_log)', cb_source)
        self.assertIn('certs.write_text_atomic(run_dir / "version.log", version_log)', cb_source)


if __name__ == '__main__':
    unittest.main()
