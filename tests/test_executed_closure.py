"""Controls for the world-IR call-reachability gate, not timing tests."""
import unittest

from tools.extract.executed_closure import Closure, Unresolved, calls


def call(name, *args):
    return ["c", name, list(args)]


def var(name):
    return ["v", name]


def quote(value):
    return ["q", value]


TRUE = quote(["y", "COMMON-LISP::T"])
NIL = quote(["y", "COMMON-LISP::NIL"])
BAD = "ACL2::WHOLE-STATEP"


def function(name, formals, body):
    return dict(name=name, formals=formals, body=body, kind="defun",
                **{"class": "common-lisp-compliant"})


def world(*functions):
    primitives = [("CONS", 2), ("CAR", 1), ("CDR", 1), ("EQUAL", 2),
                  ("CONSP", 1), ("<", 2)]
    return {"functions": [dict(name="COMMON-LISP::" + name, kind="prim",
                               formals=list(range(n))) for name, n in primitives]
            + list(functions)}


class ExecutedClosureTests(unittest.TestCase):
    def fixture(self, replace_node=False):
        node = var("OTHER") if replace_node else var("NODE")
        rebuilt = call("COMMON-LISP::CONS", node, NIL)
        checked = call("COMMON-LISP::CAR", rebuilt)
        guard = function("ACL2::GUARD", ["N", "HELD"],
                         call("COMMON-LISP::IF",
                              call("COMMON-LISP::EQUAL", var("N"), var("HELD")),
                              TRUE, call(BAD, var("N"))))
        root = function("ACL2::ROOT", ["NODE", "OTHER"],
                        call("ACL2::GUARD", checked, var("NODE")))
        return world(root, guard)

    def test_borrowed_node_prunes_but_static_edge_remains(self):
        w = self.fixture()
        self.assertIn(BAD, calls(w["functions"][-1]["body"]))
        result = Closure(w, [BAD]).check("ACL2::ROOT")
        self.assertFalse(result["violations"])
        self.assertGreater(result["resolved_branches"], 0)

    def test_replacing_node_exposes_fallback(self):
        result = Closure(self.fixture(True), [BAD]).check("ACL2::ROOT")
        self.assertEqual(result["violations"][BAD], ["ACL2::ROOT", "ACL2::GUARD", BAD])

    def test_unknown_branch_and_recursive_tail_are_not_skipped(self):
        loop = function("ACL2::LOOP", ["XS"],
                        call("COMMON-LISP::IF", call("COMMON-LISP::CONSP", var("XS")),
                             call("ACL2::LOOP", call("COMMON-LISP::CDR", var("XS"))),
                             call(BAD, var("XS"))))
        self.assertIn(BAD, Closure(world(loop), [BAD]).check("ACL2::LOOP")["violations"])

    def test_mutual_recursion_is_inspected(self):
        a = function("ACL2::A", ["X"], call("ACL2::B", var("X")))
        b = function("ACL2::B", ["X"],
                     call("COMMON-LISP::IF", var("X"), call("ACL2::A", NIL), call(BAD, var("X"))))
        self.assertIn(BAD, Closure(world(a, b), [BAD]).check("ACL2::A")["violations"])

    def test_concrete_argument_does_not_hide_later_recursive_case(self):
        root = function("ACL2::ROOT", [], call("ACL2::LOOP", quote(0), NIL))
        loop = function("ACL2::LOOP", ["N", "X"],
                        call("COMMON-LISP::IF", call("COMMON-LISP::EQUAL", var("N"), quote(0)),
                             call("ACL2::LOOP", quote(1), var("X")), call(BAD, var("X"))))
        self.assertIn(BAD, Closure(world(root, loop), [BAD]).check("ACL2::ROOT")["violations"])

    def test_unknown_definition_mutability_route_and_budget_fail_closed(self):
        root = function("ACL2::ROOT", ["X"], call("ACL2::MISSING", var("X")))
        with self.assertRaises(Unresolved):
            Closure(world(root), []).check("ACL2::ROOT")
        for field, value in (("stobjs_in", ["ACL2::STATE"]), ("class", "program")):
            changed = function("ACL2::ROOT", ["X"], var("X"))
            changed[field] = value
            with self.assertRaises(Unresolved):
                Closure(world(changed), []).check("ACL2::ROOT")
        with self.assertRaises(Unresolved):
            Closure(self.fixture(), [BAD], budget=1).check("ACL2::ROOT")


if __name__ == "__main__":
    unittest.main()
