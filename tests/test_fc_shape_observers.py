"""Source controls for the old/new theorem template and macro connection."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from lisp_rewrite import parse, match, emit


class ShapeObserversSourceTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = parse(Path(__file__).resolve().parents[1] / 'books/format-check.lisp')

    def test_complete_theorem_template_is_unchanged(self):
        event = match(None, self.source, deep=False, head='defun', name='fn2-fc-shape-event')[0].node
        body = event.items[-1].node  # Quoted emitted event.
        # Exact original macro statement, with no hint or extra premise.
        old = parse('`(defthm ,name (implies ,guard (and ,@(fn2-fc-shape-claims outputs call))))').forms[0].node
        self.assertEqual([emit(x) for x in body.items[:3]], [emit(x) for x in old.items])
        self.assertEqual(len(body.items), 5)  # Only :hints follows the claim.

    def test_macro_uses_actual_event_producer(self):
        macro = match(None, self.source, deep=False, head='defmacro', name='fn2-fc-shape')[0].node
        expected = parse('(fn2-fc-shape-event name call guard outputs)').forms[0]
        self.assertEqual(emit(macro.items[-1]), emit(expected))


if __name__ == '__main__':
    unittest.main()
