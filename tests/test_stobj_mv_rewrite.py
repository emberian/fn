import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_rewrite import parse
from stobj_mv_rewrite import rewrite, beta, PATHS

class StobjMVRewrite(unittest.TestCase):
    carriers = ('fn2-extents', 'fn2-core')
    def test_update_and_scalar_before_mutation_preserve_formula(self):
        source = '(mv (fn2-extent-state e fn2-extents) (update-fn2-extents-count 7 fn2-extents))'
        changed, n = rewrite(source, self.carriers)
        self.assertEqual(n, 1)
        self.assertLess(changed.index('fn2-mv-scalar-1'), changed.index('(fn2-extents (update-'))
        self.assertEqual(beta(parse(source).forms[0]), beta(parse(changed).forms[0]))
        self.assertEqual(rewrite(changed, self.carriers), (changed, 0))
    def test_nested_if_retains_both_branches(self):
        source = '(mv :ok (if valid (fn2-extents-set-count 0 n fn2-extents) fn2-extents))'
        changed, n = rewrite(source, self.carriers)
        self.assertEqual(n, 1)
        self.assertIn('(fn2-extents (if valid', changed)
        self.assertEqual(beta(parse(source).forms[0]), beta(parse(changed).forms[0]))
    def test_put_macro_and_core_stop(self):
        for source in ('(mv :ok (fn2-extents-put 0 (count 7)))',
                       '(mv :uncertain batch event (fn2-core-stop reason fn2-core))'):
            changed, n = rewrite(source, self.carriers)
            self.assertEqual(n, 1)
            self.assertEqual(beta(parse(source).forms[0]), beta(parse(changed).forms[0]))
    def test_scalar_accessors_strings_comments_untouched(self):
        source = '; (mv :ok (update-fn2-extents-count 7 fn2-extents))\n(mv (fn2-extents-count 0 fn2-extents) "literal" fn2-extents)'
        self.assertEqual(rewrite(source, self.carriers), (source, 0))
    def test_fresh_scalar_avoids_capture_and_quote_is_data(self):
        source = "(let ((fn2-mv-scalar-1 7)) (mv '(fn2-extents) (fn2-extents-set-count 0 n fn2-extents)))"
        changed, n = rewrite(source, self.carriers)
        self.assertEqual(n, 1)
        self.assertIn('fn2-mv-scalar-2', changed)
        quoted = '(mv (quote (fn2-extents)) (fn2-extents-set-count 0 n fn2-extents))'
        out, count = rewrite(quoted, self.carriers)
        self.assertEqual(count, 1)
        self.assertEqual(beta(parse(quoted).forms[0]), beta(parse(out).forms[0]))
    def test_comment_in_argument_preserved_between_arguments_refused(self):
        source = '(mv :ok (fn2-extents-set-count 0 ; keep\n n fn2-extents))'
        changed, n = rewrite(source, self.carriers)
        self.assertEqual(n, 1)
        self.assertIn('; keep', changed)
        with self.assertRaisesRegex(ValueError, 'between MV'):
            rewrite('(mv :ok ; keep\n (fn2-extents-set-count 0 n fn2-extents))', self.carriers)
    def test_bad_reordering_is_not_beta_equal(self):
        source = '(mv (read fn2-extents) (update-fn2-extents-count 7 fn2-extents))'
        mutant = '(let* ((fn2-extents (update-fn2-extents-count 7 fn2-extents)) (x (read fn2-extents))) (mv x fn2-extents))'
        self.assertNotEqual(beta(parse(source).forms[0]), beta(parse(mutant).forms[0]))
    def test_entire_twenty_one_class_is_now_idempotent(self):
        root = Path(__file__).resolve().parents[1]
        for name in PATHS:
            source = (root/'books'/(name+'.lisp')).read_text()
            self.assertEqual(rewrite(source), (source, 0), name)

if __name__ == '__main__': unittest.main()
