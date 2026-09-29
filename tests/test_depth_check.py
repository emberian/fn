"""tools/depth_check.py: tail positions, the recursive components, the baseline rules."""
import unittest

from tools import depth_check as d

# The reader of the ledger module depth_check itself imported: its Sym class
# is the one depth_check tests against.
Reader = d.ledger.Reader


def form(text):
    return Reader(text).top_level()[0][0]


def sites(text):
    f = form(text)
    out = []
    d.seq(d._body_forms(f[3:]), True, out)
    return out


class TailPositionTests(unittest.TestCase):
    def test_a_cons_around_the_recursion_is_not_a_tail_call(self):
        s = sites("(defun f (x) (if (consp x) (cons (car x) (f (cdr x))) nil))")
        self.assertIn(("f", False), s)

    def test_an_accumulator_loop_is_a_tail_call(self):
        s = sites("(defun f (x acc) (declare (xargs :guard t)) \"doc\""
                  " (if (consp x) (let ((y (car x))) (f (cdr x) (cons y acc))) acc))")
        self.assertIn(("f", True), s)
        self.assertNotIn(("f", False), s)

    def test_mbe_runs_its_exec_branch_only(self):
        s = sites("(defun f (x) (mbe :logic (if (consp x) (+ 1 (f (cdr x))) 0)"
                  " :exec (f-loop x 0)))")
        self.assertEqual([c for c, _ in s], ["f-loop"])

    def test_cond_and_or_last_arguments_are_tail(self):
        s = sites("(defun f (x) (cond ((atom x) nil) ((g x) (f (cdr x))) (t (or (h x) (f (cddr x))))))")
        self.assertEqual({t for c, t in s if c == "f"}, {True})

    def test_a_let_binding_and_an_if_test_are_not_tail(self):
        s = sites("(defun f (x) (let ((r (f (cdr x)))) (if (f x) r nil)))")
        self.assertEqual({t for c, t in s if c == "f"}, {False})

    def test_mv_let_body_is_tail_and_its_producer_is_not(self):
        s = sites("(defun f (x) (mv-let (a b) (f (cdr x)) (f (list a b))))")
        self.assertEqual(sorted(t for c, t in s if c == "f"), [False, True])


class ComponentTests(unittest.TestCase):
    def test_mutual_recursion_is_one_component(self):
        comps = d._sccs({"a": ["b"], "b": ["a", "c"], "c": []})
        self.assertIn(["a", "b"], comps)
        self.assertIn(["c"], comps)


class MacroWrittenDefunTests(unittest.TestCase):
    def test_a_backquoted_defun_template_is_filled(self):
        template = form("(defun ,name (x) (if (consp x) (+ ,each (,name (cdr x))) 0))")
        filled = d._fill(template, {"name": form("(fn-q)")[0], "each": 1})
        self.assertEqual(str(filled[3][2][2][0]), "fn-q")
        self.assertEqual(str(filled[1]), "fn-q")
        self.assertRaises(d._Unexpandable, d._fill, form("(a ,(b c))"), {})


class BaselineTests(unittest.TestCase):
    ROW = {"function": "fn-walk", "component": ["fn-walk"], "nontail_calls": ["fn-walk"],
           "where": "books/x.lisp:1"}

    def test_an_unlisted_recursion_fails(self):
        problems = d.check([self.ROW], {"bounded": {}, "debt": {}})
        self.assertEqual(len(problems), 1)
        self.assertIn("fn-walk", problems[0])

    def test_a_listed_one_passes_and_a_stale_entry_fails(self):
        self.assertEqual(d.check([self.ROW], {"bounded": {}, "debt": {"fn-walk": "articles"}}), [])
        stale = d.check([], {"bounded": {}, "debt": {"fn-walk": "articles"}})
        self.assertEqual(len(stale), 1)
        self.assertIn("only shrinks", stale[0])

    def test_a_bounded_entry_names_its_bound(self):
        problems = d.check([self.ROW], {"bounded": {"fn-walk": ""}, "debt": {}}, set())
        self.assertTrue(any("names no bound" in p for p in problems))

    def bounded(self, why, constants=frozenset()):
        return d.check([self.ROW], {"bounded": {"fn-walk": why}, "debt": {}}, set(constants))

    # The regression (lane peer-list-depth, batch AZ): `peer list' over a peer
    # carrying ~1,100 principals died at 1,024 KiB in fn-napb-before-last, which
    # the baseline held under "bounded" with this text.  Operator data is not
    # a bound (D27): the check refuses it, and every reason of its class.
    def test_operator_data_is_not_a_bound(self):
        for why in ("Walks one rendered 'peer list' line for one peer; bounded "
                    "peer-config-row rendering, not traffic.",
                    "walks rows, the peer/config table keyed rows; bounded by the operator's profile",
                    "Walks config-generation entries; bounded by the profile's operator-set "
                    "max-config-generations field.",
                    "entries is the consumer registration table, capped by the operator's "
                    "store-profile field fn-bs-profile-max-consumers"):
            problems = self.bounded(why)
            self.assertEqual(len(problems), 1, why)
            self.assertIn("names no bound", problems[0])
            self.assertIn("D27", problems[0])

    def test_a_named_bound_passes(self):
        self.assertEqual(self.bounded("capped at *fn-cfg-max-rows*=1024 on decode",
                                      {"*fn-cfg-max-rows*"}), [])
        self.assertEqual(self.bounded("walks a 32-octet digest"), [])
        self.assertEqual(self.bounded("walks a number's decimal digits (log n)"), [])
        self.assertEqual(self.bounded("a fixed record's field list"), [])

    def test_a_cited_constant_must_exist(self):
        problems = self.bounded("capped at *fn-no-such-cap*")
        self.assertEqual(len(problems), 1)
        self.assertIn("does not define", problems[0])

    def test_the_trees_constants_are_read(self):
        self.assertIn("*fn-nctrl-max-command-frame*", d.defined_constants())


if __name__ == "__main__":
    unittest.main()
