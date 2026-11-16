"""Proof-only source/actual-macro controls; no ACL2 admission or speed claim."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lisp
import proof_repl
BASELINE = '923c14ad7'


def tree(n):
    if isinstance(n, lisp.Pre):
        return n.prefix, tree(n.node)
    if isinstance(n, lisp.Lst):
        out, i = [], 0
        while i < len(n.items):
            if lisp.flat(n.items[i]) in (':hints', ':guard-hints'):
                i += 2
            else:
                out.append(tree(n.items[i])); i += 1
        return tuple(out)
    return n.text if isinstance(n, lisp.Str) else n.low


class SealerProofBoundaries(unittest.TestCase):
    def before(self):
        return subprocess.check_output(['git', 'show', BASELINE + ':books/sealer.lisp'], cwd=ROOT)

    def test_every_runtime_guard_public_formula_and_other_hint_exact(self):
        old = lisp.parse(self.before()).forms
        new = lisp.parse(ROOT / 'books/sealer.lisp').forms
        def selected(forms):
            return [tree(f) for f in forms if not (
                isinstance(f, lisp.Lst) and (
                    lisp.flat(f) == '(local (include-book "columns-call-guards"))' or
                    (isinstance(f, lisp.Lst) and len(f.items) > 1 and lisp.flat(f.items[1]) == 'fn2-seal-width-from-range-by-definition') or
                    (lisp.flat(f.items[0]) == 'defmacro' and lisp.flat(f.items[1]) == 'fn2-seal-shape')))]
        self.assertEqual(selected(old), selected(new))
        changed = {'fn2-seal-start', 'fn2-seal-most-runs-types', 'fn2-seal-plan-types',
                   'fn2-seal-compact-target-types', 'fn2-seal-take-page-types', 'fn2-seal-shape'}
        def untouched(forms):
            return [lisp.flat(f) for f in forms if not (
                lisp.flat(f) == '(local (include-book "columns-call-guards"))' or
                    (isinstance(f, lisp.Lst) and len(f.items) > 1 and lisp.flat(f.items[1]) == 'fn2-seal-width-from-range-by-definition') or
                (isinstance(f, lisp.Lst) and len(f.items) > 1 and lisp.flat(f.items[1]) in changed))]
        self.assertEqual(untouched(old), untouched(new))

    def test_scalar_subject_enabled_and_named_boundaries_not_opened(self):
        expected = {
            'fn2-seal-most-runs-types': ('fn2-seal-most-runs', ['fn2-seal-live-runs']),
            'fn2-seal-plan-types': ('fn2-seal-plan', ['fn2-seal-pressured-p', 'fn2-seal-live-runs', 'fn2-seal-select']),
            'fn2-seal-compact-target-types': ('fn2-seal-compact-target', ['fn2-seal-most-runs', 'fn2-seal-pressured-p', 'fn2-seal-select']),
            'fn2-seal-take-page-types': ('fn2-seal-take-page', ['fn2-seal-unit', 'fn2-pool-reserve', 'fn2-pool-class-for'])}
        a = lisp.parse(ROOT / 'books/sealer.lisp')
        for name, (subject, opaque) in expected.items():
            t = lisp.match(None, a.forms, deep=False, head='defthm', name=name)[0].node
            h = lisp.match(None, [t], head='fn2-columns-call-guard-hint')[0].node
            self.assertEqual(lisp.flat(h), "(fn2-columns-call-guard-hint '" + subject + " '(" + ' '.join(opaque) + ") '(" + subject + ") world)")

    def test_start_guard_retains_every_original_explicit_boundary(self):
        old = lisp.match(None, lisp.parse(self.before()).forms, deep=False,
                         head='defun', name='fn2-seal-start')[0].node
        new = lisp.match(None, lisp.parse(ROOT / 'books/sealer.lisp').forms, deep=False,
                         head='defun', name='fn2-seal-start')[0].node
        old_disable = lisp.match(None, [old], head='disable')[0].node
        hint = lisp.match(None, [new], head='fn2-columns-call-guard-hint')[0].node
        self.assertEqual([lisp.flat(n) for n in hint.items[2].node.items],
                         [lisp.flat(n) for n in old_disable.items[1:]] + ['min', 'nfix'])
        self.assertEqual(lisp.flat(hint.items[3]), 'nil')

    def test_width_bridge_retains_all_actual_numeric_premises(self):
        forms = lisp.parse(ROOT / 'books/sealer.lisp').forms
        bridge = lisp.match(None, forms, deep=False, head='defthm',
                            name='fn2-seal-width-from-range-by-definition')
        self.assertEqual(len(bridge), 1)  # Exported with the wrapper, not LOCAL.
        self.assertEqual(lisp.flat(bridge[0].node.items[2]),
            '(implies (and (natp bits) (integerp v) (<= 0 v) (< v (expt 2 bits))) (unsigned-byte-p bits v))')
        self.assertTrue(lisp.match(None, [bridge[0].node], head='enable'))

    def test_helper_has_explicit_owner_and_no_parent_expansion(self):
        a = lisp.parse(ROOT / 'books/sealer.lisp')
        self.assertTrue(any(lisp.flat(f) == '(local (include-book "columns-call-guards"))' for f in a.forms))
        graph = proof_repl.include_graph(ROOT, 'books/sealer')
        parents = proof_repl.include_graph(ROOT, 'books/machines-c-groups')
        self.assertEqual(set(graph), set(parents) | {'books/sealer'})

    @unittest.skipUnless(shutil.which('sbcl'), 'SBCL required for actual macro controls')
    def test_actual_wrapper_all_calls_and_explicit_alternate_modes(self):
        with tempfile.NamedTemporaryFile(suffix='.lisp') as f:
            f.write(self.before()); f.flush()
            r = subprocess.run(['sbcl', '--noinform', '--script', 'tests/sealer-proof-boundary-controls.lsp', f.name],
                               cwd=ROOT, text=True, capture_output=True, timeout=20)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn('SEALER CANONICAL WRAPPER SOURCE CONTROLS PASS', r.stdout)


if __name__ == '__main__':
    unittest.main()
