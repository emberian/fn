"""Verify whole declaration moves and real cache dependency cuts; no ACL2."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import certs
import certify_books
import lisp_rewrite as lisp

BASELINE = '9666d7ba67e9893730ad4dd4c27797ac37b2a0c1'
PAIRS = [('conn-kind', 'conn-schema'), ('tls-kind', 'tls-schema')]


def forms(source, skip=()):
    return [lisp.flat(form) for form in lisp.parse(source).forms
            if isinstance(form, lisp.Lst) and lisp.flat(form.items[0]) not in skip]


class KindSchemaBoundaries(unittest.TestCase):
    def test_provider_imports_direct_discharge_owner(self):
        imports = forms((ROOT / 'books/tls-schema.lisp').read_text())
        self.assertIn('(include-book "owed-discharge")', imports)

    def test_all_original_declarations_and_import_order_preserved(self):
        for kind, schema in PAIRS:
            with self.subTest(kind=kind):
                old = subprocess.check_output(['git', 'show', f'{BASELINE}:books/{kind}.lisp'], cwd=ROOT, text=True)
                new = (ROOT / f'books/{schema}.lisp').read_text() + (ROOT / f'books/{kind}.lisp').read_text()
                self.assertEqual(forms(old, {'in-package', 'include-book', 'fn2-book-layer'}),
                                 forms(new, {'in-package', 'include-book', 'fn2-book-layer'}))
                original = lisp.parse(old)
                public = lisp.parse(ROOT / f'books/{kind}.lisp')
                old_imports = [lisp.flat(f) for f in original.forms if lisp.flat(f.items[0]) == 'include-book']
                new_imports = [lisp.flat(f) for f in public.forms if lisp.flat(f.items[0]) == 'include-book']
                self.assertEqual(new_imports[:-1], old_imports)
                self.assertEqual(new_imports[-1], f'(include-book "{schema}")')
                # The complete original DEFMachine event remains one event.
                self.assertEqual(len(lisp.match('_', original.forms, head='defmachine', deep=False)), 1)
                self.assertEqual(len(lisp.match('_', lisp.parse(ROOT / f'books/{schema}.lisp').forms,
                                                head='defmachine', deep=False)), 1)

    def test_public_event_order_matches_before_the_cut(self):
        original = {f'books/{kind}': subprocess.check_output(
            ['git', 'show', f'{BASELINE}:books/{kind}.lisp'], cwd=ROOT, text=True)
            for kind, _schema in PAIRS}

        def expand(book, overrides, seen):
            if book in seen:
                return []
            seen.add(book)
            source = overrides.get(book)
            if source is None:
                source = (ROOT / f'{book}.lisp').read_text()
            result = []
            for form in lisp.parse(source).forms:
                head = lisp.flat(form.items[0]) if isinstance(form, lisp.Lst) else ''
                if head == 'include-book':
                    if len(form.items) == 2:  # System/project includes are unchanged.
                        path = ROOT / Path(book).parent / (form.items[1].text[1:-1] + '.lisp')
                        child = path.resolve().relative_to(ROOT).with_suffix('').as_posix()
                        result.extend(expand(child, overrides, seen))
                elif head not in {'in-package', 'fn2-book-layer'}:
                    result.append(lisp.flat(form))
            return result

        for kind, _schema in PAIRS:
            with self.subTest(kind=kind):
                self.assertEqual(expand(f'books/{kind}', original, set()),
                                 expand(f'books/{kind}', {}, set()))

    def test_arm_generator_change_rekeys_only_public_registry_books(self):
        certify_books.ROOT = ROOT
        names = certify_books.with_dependencies(['books/conn-kind', 'books/tls-kind'])
        with tempfile.TemporaryDirectory(prefix='fn-kind-schema-') as tmp:
            root = Path(tmp)
            for name in names:
                target = root / f'{name}.lisp'
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / f'{name}.lisp', target)
            targets = [f'books/{name}' for pair in PAIRS for name in pair]
            before = {name: certs.closure_key(root, name)[0] for name in targets}
            arms = root / 'books/machine-arms.lisp'
            arms.write_text(arms.read_text() + '\n(value-triple :kind-schema-cache-control)\n')
            after = {name: certs.closure_key(root, name)[0] for name in targets}
            for kind, schema in PAIRS:
                self.assertNotIn('books/machine-arms', certs.closure(root, f'books/{schema}'))
                self.assertEqual(before[f'books/{schema}'], after[f'books/{schema}'])
                self.assertNotEqual(before[f'books/{kind}'], after[f'books/{kind}'])


if __name__ == '__main__':
    unittest.main()
