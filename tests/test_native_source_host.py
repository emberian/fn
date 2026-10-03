"""Actual host load order, local proof boundaries and inventory refusal."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import native_source_host as host


class HostSourceTests(unittest.TestCase):
    def setup_tree(self, directory):
        root = Path(directory)
        (root / 'host/native').mkdir(parents=True)
        (root / 'books').mkdir()
        (root / 'host/native/build.lisp').write_text('''(include-book "books/image-world")
(ld "host/outer.lisp" :ld-error-action :error)
(defttag :fn-native-host)
(progn! (set-raw-mode t) (load "host/native/io.lisp") (fnn-install-raw-dispatch))
:q
(save-exec "ignored")''')
        (root / 'host/outer.lisp').write_text('''(in-package "ACL2")
(include-book "../books/model")
(ld "inner.lisp" :ld-error-action :error)
(local (defthm private-proof t))
(defun actual-outer (x) (actual-inner x))
(verify-guards actual-outer)''')
        (root / 'host/inner.lisp').write_text('''(in-package "ACL2")
(local (include-book "../books/model"))
(defun actual-inner (x) x)
(definterface actual-inner :class :common-lisp-compliant)''')
        manifest = root / 'logical.json'
        manifest.write_text(json.dumps({'source': str(root),
            'repository_books': ['books/image-world.lisp', 'books/model.lisp']}))
        return root, manifest

    def test_current_nested_host_order_and_actual_raw_installation(self):
        with tempfile.TemporaryDirectory() as directory:
            root, world = self.setup_tree(directory)
            output = root / 'build/source-build.lisp'
            manifest = host.generate(root, world, output)
            text = output.read_text()
            self.assertLess(text.index('(defun actual-inner'), text.index('(defun actual-outer'))
            self.assertLess(text.index('(definterface actual-inner'), text.index('(fnn-install-raw-dispatch)'))
            self.assertIn('(local (defthm private-proof t))', ' '.join(text.split()))
            self.assertIn('(verify-guards actual-outer)', text)
            self.assertIn('(encapsulate ()', text)
            self.assertIn('(progn! (set-raw-mode t) (load "host/native/io.lisp") (fnn-install-raw-dispatch))', text)
            self.assertNotIn('include-book', text)
            self.assertNotIn('save-exec', text)
            data = json.loads(manifest.read_text())
            normal = Path(data['normal_host']).read_text()
            native = Path(data['native_installation']).read_text()
            self.assertIn('(defun actual-outer', normal)
            self.assertNotIn(':fn-native-host', normal)
            self.assertNotIn('set-raw-mode', normal)
            self.assertNotIn(':q', normal)
            self.assertIn('(fnn-install-raw-dispatch)', native)
            self.assertNotIn('(defun actual-outer', native)
            self.assertIn(str(Path(data['normal_host'])), data['inputs_sha256'])
            self.assertIn(str((root / 'host/inner.lisp').resolve()), json.loads(manifest.read_text())['inputs_sha256'])

    def test_unadmitted_dependency_refuses_instead_of_dropping_it(self):
        with tempfile.TemporaryDirectory() as directory:
            root, world = self.setup_tree(directory)
            (root / 'host/inner.lisp').write_text('(include-book "../books/missing")')
            with self.assertRaisesRegex(ValueError, 'absent from admitted world'):
                host.generate(root, world, root / 'build/source-build.lisp')

    def test_nested_host_cycle_is_not_an_admitted_empty_prefix(self):
        with tempfile.TemporaryDirectory() as directory:
            root, world = self.setup_tree(directory)
            (root / 'host/inner.lisp').write_text('(ld "outer.lisp" :ld-error-action :error)')
            with self.assertRaisesRegex(ValueError, 'recursive host LD'):
                host.generate(root, world, root / 'build/source-build.lisp')

    def test_cross_root_reuse_requires_every_actual_logical_book_to_match(self):
        import hashlib
        with tempfile.TemporaryDirectory() as directory:
            root, world = self.setup_tree(directory)
            data = json.loads(world.read_text())
            data['source'] = '/a/different/frozen/source'
            for name in data['repository_books']:
                (root / name).write_text('(defun same-model (x) x)')
            data['repository_sha256'] = {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                                         for name in data['repository_books']}
            world.write_text(json.dumps(data))
            host.generate(root, world, root / 'build/source-build.lisp')
            (root / 'books/model.lisp').write_text('(defun same-model (x) nil)')
            with self.assertRaisesRegex(ValueError, 'differs from admitted source'):
                host.generate(root, world, root / 'build/changed-build.lisp')


if __name__ == '__main__':
    unittest.main()
