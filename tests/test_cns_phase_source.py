"""Declaration consistency only; not ACL2 admission or phase reachability."""
from pathlib import Path
import sys
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import lisp_rewrite as lr

def symbol(node):
    return node.low if isinstance(node, lr.Atom) else None

def declaration(path, head, name):
    return next(f for f in lr.parse(ROOT / path).forms
                if isinstance(f, lr.Lst) and len(f.items) > 1
                and symbol(f.items[0]) == head and symbol(f.items[1]) == name)

def option(form, name):
    return next(form.items[i + 1] for i, n in enumerate(form.items[:-1])
                if symbol(n) == name)

def names(node):
    return [symbol(x.items[0]) for x in node.items]

def missing(phases, declared_arms, holds, actual_arms):
    return (set(declared_arms) | set(holds) | set(actual_arms)) - set(phases)

class CNSPhaseSource(unittest.TestCase):
    def setUp(self):
        kind = declaration("books/cns-kind.lisp", "defmachine", "fn2-cns")
        arms = declaration("books/cns.lisp", "defmachine-arms", "fn2-cns")
        self.phases = [symbol(n) for n in option(kind, ":phases").items]
        self.declared = names(option(kind, ":arms"))
        self.holds = names(option(kind, ":holds"))
        self.actual = names(option(arms, ":arms"))

    def test_actual_registry_covers_declared_holds_and_actual_arms(self):
        self.assertFalse(missing(self.phases, self.declared, self.holds, self.actual))
        self.assertEqual(set(self.phases), set(self.actual))
        self.assertIn(":article", self.phases)
        self.assertIn(":item", self.phases)

    def test_removing_either_new_phase_is_detected(self):
        for phase in (":article", ":item"):
            with self.subTest(phase=phase):
                self.assertIn(phase, missing([p for p in self.phases if p != phase],
                                            self.declared, self.holds, self.actual))

if __name__ == "__main__":
    unittest.main()
