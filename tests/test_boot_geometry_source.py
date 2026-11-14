"""Keep generated geometry declarations from swallowing their next defun."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_rewrite import Atom, Lst, parse


def is_head(node, name):
    return (isinstance(node, Lst) and node.items and
            isinstance(node.items[0], Atom) and node.items[0].text.lower() == name)


class BootGeometrySource(unittest.TestCase):
    def test_pack_geometry_is_top_level(self):
        forms = parse(ROOT / "books/boot.lisp").forms
        definitions = [f.items[1].text.lower() for f in forms
                       if is_head(f, "defun") and isinstance(f.items[1], Atom)]
        self.assertIn("fn2-boot-pack-geometry", definitions)
        self.assertIn("fn2-boot-bootstrap-pool", definitions)
        events = [f for f in forms if is_head(f, "make-event")]
        self.assertEqual(len(events), 1)
        self.assertEqual(len(events[0].items), 2)

    def test_old_parenthesis_pair_swallowing_is_detected(self):
        source = (ROOT / "books/boot.lisp").read_text()
        # Reintroduce the precise balanced pair: leave DECLARE open and close
        # the first B* binding before its return expression instead.
        source = source.replace(
            '(fn2-fields-rows fn2-fields)))))\n  (let*',
            '(fn2-fields-rows fn2-fields))))\n  (let*', 1)
        source = source.replace(
            '(fn2-fields-rows fn2-fields))))\n       (mv :geometry',
            '(fn2-fields-rows fn2-fields)))))\n       (mv :geometry', 1)
        forms = parse(source).forms
        self.assertFalse(any(is_head(f, "defun") and
                             f.items[1].text.lower() == "fn2-boot-pack-geometry"
                             for f in forms))


if __name__ == "__main__":
    unittest.main()
