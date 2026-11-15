"""ACL2 MIN/MAX arity controls, including machine expression lowering inputs."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr


def nary_calls(text):
    found = []
    def walk(node):
        if isinstance(node, lr.Pre):
            if node.prefix != "'":
                walk(node.node)
        elif isinstance(node, lr.Lst):
            items = node.items
            head = items[0].low if items and isinstance(items[0], lr.Atom) else ''
            if head == 'quote':
                return
            if head in ('min', 'max') and len(items) > 3:
                found.append(node)
            # Formal parameter lists are binders, even when the first is MIN/MAX.
            children = items[3:] if head in ('defun', 'defmacro') else items
            for child in children:
                walk(child)
    for form in lr.parse(text).forms:
        walk(form)
    return found


class MinAritySource(unittest.TestCase):
    def test_expression_contexts(self):
        fixture = """
(defun f (max a b c) (min a b))
(defconst *data* '((min a b c)))
(defconst *also-data* (quote ((max a b c))))
(defmachine example (:work (:let n (min 1 a b))))
(defun g (a b) (b* ((n (min 1 a b))) n))
(defmacro generated (a b) `(max 1 ,a ,b))
"""
        self.assertEqual([lr.flat(n) for n in nary_calls(fixture)],
                         ['(min 1 a b)', '(min 1 a b)', '(max 1 ,a ,b)'])

    def test_served_minimums(self):
        for name in ('books/cns-source-raw.lisp', 'books/cns.lisp'):
            with self.subTest(name=name):
                self.assertEqual(nary_calls((ROOT / name).read_text()), [])

    def test_operand_order_and_clamp(self):
        for a in (-1, 0, 1, 1024, 4096):
            for b in (-1, 0, 1, 1024, 4096):
                for c in (-1, 0, 1, 1024, 4096):
                    self.assertEqual(min(a, b, c), min(min(a, b), c))


if __name__ == '__main__':
    unittest.main()
