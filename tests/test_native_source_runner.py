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
        self.assertIn("(set-ld-redefinition-action '(:warn . :overwrite) state)", result)
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
            (root / 'core').write_bytes(b'generic core')
            (root / 'sbcl').write_bytes(b'pinned executable')
            args = types.SimpleNamespace(world_root=str(root), source_root=str(root),
                output=str(root/'entry'), build='host/native/build.lisp',
                event=['host/owner-host.lisp:gate'], world_revision='a'*40,
                source_revision='b'*40, sbcl=str(root/'sbcl'), core=str(root/'core'),
                profile='developer', before_world=[],events_file=[],raw_after=[],input_manifest=[])
            manifest = runner.prepare(args)
            event.write_text('(defun gate (x) nil)')
            with self.assertRaisesRegex(ValueError, 'input changed'):
                runner.run(manifest, [])

    def test_cached_source_inventory_is_bound_as_an_execution_input(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'host/native').mkdir(parents=True)
            (root / 'host/native/build.lisp').write_text('(defttag :fn-native-host)\n:q')
            (root / 'core').write_bytes(b'generic core')
            (root / 'sbcl').write_bytes(b'pinned executable')
            pair = root / 'cached.cert'
            pair.write_bytes(b'actual pair')
            inventory = root / 'world.json'
            inventory.write_text(json.dumps({'inputs_sha256': {str(pair): runner.digest(pair)}}))
            args = types.SimpleNamespace(world_root=str(root), source_root=str(root),
                output=str(root/'entry'), build='host/native/build.lisp', event=[],
                world_revision='a'*40, source_revision='b'*40,
                sbcl=str(root/'sbcl'), core=str(root/'core'), profile='developer',
                before_world=[], events_file=[], raw_after=[], input_manifest=[str(inventory)])
            manifest = runner.prepare(args)
            pair.write_bytes(b'different pair')
            with self.assertRaisesRegex(ValueError, 'input changed'):
                runner.run(manifest, [])

    def test_exec_preserves_single_native_argv_and_stdin(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'manifest.json'
            path.write_text(json.dumps({'sha256':{}, 'world_root':directory,
                'bootstrap':'/bootstrap', 'entry_driver':'/strict-driver',
                'after_acl2_loop':runner.entry_after_loop(), 'profile':'developer',
                'sbcl':'/sbcl', 'core':'/core'}))
            with patch.object(runner.sys, 'platform', 'linux'), patch.object(runner.os, 'chdir'), patch.object(runner.os, 'execve') as execute:
                runner.run(path, ['--fn','tcpcl','-','once'])
            argv = execute.call_args.args[1]
            self.assertEqual(argv[-4:], ['--fn','tcpcl','-','once'])
            self.assertEqual(argv.count('--fn'), 1)
            self.assertEqual(execute.call_args.args[2]['ACL2_BOOK_HASH_ALISTP'], 'NIL')
            self.assertEqual(execute.call_args.args[2]['ACL2_CUSTOMIZATION'], 'NONE')
            self.assertIn(runner.entry_after_loop(), argv)
            self.assertTrue(any('with-open-file' in arg and '/strict-driver' in arg for arg in argv))

    def test_local_execution_refuses_pool_bypass(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'manifest.json'
            path.write_text(json.dumps({'sha256':{}}))
            with patch.object(runner.sys,'platform','darwin'):
                with self.assertRaisesRegex(ValueError,'governed hbox'):
                    runner.run(path, [])

    def test_direct_and_checkpoint_driver_share_strict_verdict(self):
        import json
        import native_source_cache as cache
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original = root / 'original.lisp'
            original.write_text('(defun bad (x) (undefined-call x))\n' + cache.ENTRY)
            manifest = root / 'original.json'
            manifest.write_text(json.dumps({'sha256': {}, 'bootstrap': str(original)}))
            prepared = json.loads(cache.prepare(manifest, root / 'cache').read_text())
            driver = Path(prepared['bootstrap']).read_text()
            self.assertEqual(driver, runner.strict_driver(Path(prepared['checkpoint_events'])))
            self.assertIn(':ld-error-action :return', driver)
            self.assertIn('(and (not erp) (eq reason :eof))', driver)
            self.assertTrue(driver.rstrip().endswith(':q'))
            self.assertIn('native entry refused', runner.entry_after_loop())

    def test_legacy_unguarded_direct_entry_refuses(self):
        import json
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'manifest.json'
            path.write_text(json.dumps({'sha256': {}, 'world_root': directory,
                'bootstrap':'/bootstrap', 'profile':'developer'}))
            with patch.object(runner.sys, 'platform', 'linux'), patch.object(runner.os, 'chdir'):
                with self.assertRaisesRegex(ValueError, 'strict source admission driver'):
                    runner.run(path, [])

class LogicalCheckpointTests(unittest.TestCase):
    def test_prefix_is_hash_bound_and_restart_stays_logical(self):
        import json
        import native_source_cache as cache
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prefix = root / 'early.lisp'
            prefix.write_text('(in-package "ACL2")\n(defun early (x) x)\n')
            manifest = root / 'runtime.json'
            manifest.write_text(json.dumps({'sha256': {}}))
            prepared = json.loads(cache.prepare(manifest, root / 'cache', prefix).read_text())
            self.assertEqual(prepared['checkpoint_mode'], 'logical-repl')
            self.assertEqual(prepared['sha256'][str(prefix.resolve())], runner.digest(prefix))
            self.assertEqual(Path(prepared['checkpoint_events']).read_text(), prefix.read_text())
            self.assertIn(":return-from-lp '(acl2::lp)", prepared['after_acl2_loop'])
            self.assertNotIn('fn-native-entry', prepared['after_acl2_loop'])
            self.assertIn(':ld-error-action :return', Path(prepared['bootstrap']).read_text())

    def test_logical_prefix_refuses_native_entry(self):
        import json
        import native_source_cache as cache
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            prefix = root / 'bad.lisp'; prefix.write_text(cache.ENTRY)
            manifest = root / 'runtime.json'; manifest.write_text(json.dumps({'sha256': {}}))
            with self.assertRaisesRegex(ValueError, 'must not enter native'):
                cache.prepare(manifest, root / 'cache', prefix)

    def test_logical_restart_refuses_native_argv(self):
        import json
        import native_source_cache as cache
        with tempfile.TemporaryDirectory() as directory:
            manifest = Path(directory) / 'execution.json'
            manifest.write_text(json.dumps({'execution_sha256': {}, 'checkpoint_mode': 'logical-repl'}))
            with patch.object(cache.sys, 'platform', 'linux'):
                with self.assertRaisesRegex(ValueError, 'resumes ACL2 LP'):
                    cache.execute(manifest, ['--fn', 'owner'])
