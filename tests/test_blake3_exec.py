"""The execution rewrite must preserve forms outside the selected definition heads."""
import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from blake3_exec import inline_rounds, compare, flatten_round, linear_entry, logical
from lisp_rewrite import parse, Atom, Lst, write

class Blake3ExecTests(unittest.TestCase):
    def test_real_book_roundtrip(self):
        text = Path('books/blake3.lisp').read_text()
        after, report = inline_rounds(text)
        self.assertEqual(compare(text, after)['changed'], [])
        self.assertEqual(report['residual'], [])
        self.assertEqual(inline_rounds(after)[0], after)

    def test_only_head_changes(self):
        before = '; hi\n(defun fn-b3-round (x) ; body\n x)\n(defthm lemma (equal x x))\n'
        after, _ = inline_rounds(before, {'fn-b3-round'})
        self.assertEqual(after, before.replace('(defun ', '(defun-inline '))

    def test_refuses_missing_or_wrong_kind(self):
        for src in ('(defun other (x) x)', '(defthm fn-b3-round (equal x x))'):
            with self.assertRaises(ValueError):
                inline_rounds(src, {'fn-b3-round'})

    def test_generators_reproduce_guard_verified_exec_bodies(self):
        text = Path('books/blake3.lisp').read_text()
        for name, generate in [('fn-b3-round', flatten_round), ('fn-b3-compress', linear_entry)]:
            def find(src):
                return next(f for f in parse(src).forms if isinstance(f, Lst)
                            and len(f.items) > 3 and isinstance(f.items[1], Atom)
                            and f.items[1].low == name)
            form = find(text)
            body = form.items[-1]
            self.assertEqual(body.items[0].low, 'mbe')
            original = body.items[2]
            restored = write(text, [(body.start, body.end, text[original.start:original.end])])
            regenerated = generate(restored)
            self.assertEqual(logical(find(regenerated).items[-1].items[4]), logical(body.items[4]))
            self.assertEqual(compare(text, regenerated)['changed'], [])
            with self.assertRaises(ValueError):
                generate(text)

    def test_statement_audit_keeps_rule_classes_and_nested_events(self):
        old = '(local (defthm a (equal x x) :rule-classes nil))'
        self.assertEqual(compare(old, old.replace('nil', ':rewrite'))['changed'], ['a'])
        self.assertEqual(compare('', '(encapsulate () ' + old + ')')['added'], ['a'])

    def test_statement_audit_uses_logic_and_detects_mutation(self):
        old = '(defun f (x) (declare (xargs :guard t)) (+ x 1)) (defthm a (equal (f x) (+ x 1)))'
        new = '(defun-inline f (x) (mbe :logic (+ x 1) :exec (the integer (+ 1 x)))) (defthm a (equal (f x) (+ x 1)) :hints (("Goal" :in-theory (enable f))))'
        self.assertEqual(compare(old, new)['changed'], [])
        self.assertEqual(compare(old, new.replace(':logic (+ x 1)', ':logic (+ x 2)'))['changed'], ['f'])
        self.assertEqual(compare(old, new.replace('(equal (f x) (+ x 1))', '(equal x x)'))['changed'], ['a'])

if __name__ == '__main__':
    unittest.main()
