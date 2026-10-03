"""Refuse moving inputs and keep actual native bootstrap/argv boundaries."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import native_source_runner as runner

class SourceRunnerTests(unittest.TestCase):
    def test_bootstrap_stays_inside_acl2_loop_and_preserves_attachment_order(self):
        source = '''(include-book "arena-attach")
(include-book "generic")
(defttag :fn-native-host)
(progn! (set-raw-mode t) (load "native.lisp"))
(defttag nil)
:q
(format t "raw saved metadata")
(load "host/native/strip-world.lisp")
(save-exec "image")'''
        result = runner.prefix(source, ['(defun gate (x) x)'])
        self.assertLess(result.index('arena-attach'), result.index('generic'))
        self.assertLess(result.index('(defun gate'), result.index(':fn-native-host'))
        self.assertNotIn(':q', result)
        self.assertNotIn('raw saved metadata', result)
        self.assertNotIn('save-exec', result)
        self.assertNotIn('strip-world', result)
        self.assertTrue(result.rstrip().endswith('(fn-native-entry state))'))

    def test_ordered_source_attachment_and_raw_overlay_match_actual_loads(self):
        result=runner.prefix('(include-book "umbrella")\n(defttag :fn-native-host)\n(progn! (set-raw-mode t) (load "owner.lisp"))\n:q',
            ['(defun new-host (x) x)'], ['(attach-stobj hist paged)'],
            [('owner.lisp','/source/history-root.lisp')])
        self.assertLess(result.index('attach-stobj'),result.index('umbrella'))
        self.assertLess(result.index('load "owner.lisp"'),result.index('load "/source/history-root.lisp"'))
        with self.assertRaisesRegex(ValueError,'anchor'):
            runner.prefix('(defttag :fn-native-host)',[],raw_after=[('absent.lisp','new.lisp')])

    def test_missing_logical_native_boundary_refuses(self):
        with self.assertRaises(ValueError):
            runner.prefix('(include-book "generic")', [])

    def test_prepare_binds_sources_and_refuses_changed_selected_event(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'host/native').mkdir(parents=True)
            (root / 'books').mkdir()
            (root / 'books/model.lisp').write_text('(defun model (x) x)')
            (root / 'host/native/build.lisp').write_text('(defttag :fn-native-host)\n:q\n(save-exec "image")')
            event = root / 'host/owner-host.lisp'
            event.write_text('(defun gate (x) x)')
            args = types.SimpleNamespace(world_root=str(root), source_root=str(root),
                output=str(root/'entry'), build='host/native/build.lisp',
                event=['host/owner-host.lisp:gate'], world_revision='a'*40,
                source_revision='b'*40, sbcl='/bin/false', core='/tmp/core',
                profile='developer', before_world=[],events_file=[],raw_after=[])
            manifest = runner.prepare(args)
            event.write_text('(defun gate (x) nil)')
            with self.assertRaisesRegex(ValueError, 'input changed'):
                runner.run(manifest, [])

    def test_exec_preserves_single_native_argv_and_stdin(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'manifest.json'
            path.write_text(json.dumps({'sha256':{}, 'world_root':directory,
                'bootstrap':'/bootstrap', 'profile':'developer',
                'sbcl':'/sbcl', 'core':'/core'}))
            with patch.object(runner.sys, 'platform', 'linux'), patch.object(runner.os, 'chdir'), patch.object(runner.os, 'execve') as execute:
                runner.run(path, ['--fn','tcpcl','-','once'])
            argv = execute.call_args.args[1]
            self.assertEqual(argv[-4:], ['--fn','tcpcl','-','once'])
            self.assertEqual(argv.count('--fn'), 1)
            self.assertEqual(execute.call_args.args[2]['ACL2_BOOK_HASH_ALISTP'], 'NIL')

    def test_local_execution_refuses_pool_bypass(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'manifest.json'
            path.write_text(json.dumps({'sha256':{}}))
            with patch.object(runner.sys,'platform','darwin'):
                with self.assertRaisesRegex(ValueError,'governed hbox'):
                    runner.run(path, [])
