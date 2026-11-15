"""The operation vocabulary and diagnostic ring must share one trace ABI."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from lisp_rewrite import Lst, Pre, flat, parse


def lists(node):
    if isinstance(node, Pre):
        yield from lists(node.node)
    elif isinstance(node, Lst):
        yield node
        for item in node.items:
            yield from lists(item)


def trace_family(source):
    return next(n for f in parse(source).forms for n in lists(f)
                if n.items and flat(n.items[0]) == "fn2-trace-kind")


def agrees(family, keywords):
    entries = {flat(n.items[0]): int(flat(n.items[1])) for n in family.items[1:]}
    return (entries.pop(":count") == len(keywords)
            and entries == {key: i for i, key in enumerate(keywords)})


class TraceKindManifestTests(unittest.TestCase):
    def test_foundation_matches_actual_ring_and_preserves_tags(self):
        family = trace_family(ROOT / "books/operations.lisp")
        enum = next(n for f in parse(ROOT / "books/trace.lisp").forms for n in lists(f)
                    if n.items and flat(n.items[0]) == ":enum"
                    and flat(n.items[1]) == "fn2-trace-kind")
        keywords = [flat(k) for k in enum.items[2].items]
        self.assertEqual(keywords, [":mailbox", ":machine", ":service", ":clock",
                                    ":signal", ":machine-start", ":enqueue"])
        self.assertTrue(agrees(family, keywords))
        old = trace_family("(fn2-trace-kind (:mailbox 0) (:machine 1) (:service 2) "
                           "(:clock 3) (:signal 4) (:count 5))")
        self.assertFalse(agrees(old, keywords))


if __name__ == "__main__":
    unittest.main()
