"""Teeth for `tools/host_shape_check.py`: the break it exists for, and its limits.

At 9c344d1d host/owner-host.lisp passed `(fn-owner-clock-observation state)`,
an error triple, as an argument, and the image build on hbox was the first
thing to refuse it.  The first two cases pin that defect -- the whole file as
it stood at 9c344d1d, and the two definitions reduced to a fixture -- so it
stays caught.  The rest are the ways a shape lint goes wrong: flagging a form
ACL2 accepts, and passing one ACL2 refuses.

Nothing here runs ACL2.  The historical case reads 9c344d1d with `git show`,
so it needs this repository's history, which every lane worktree has.
"""

import subprocess
import sys
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import host_shape_check  # noqa: E402

FIXTURE = "host/zz-shape-fixture.lisp"

# The two definitions from `git show 9c344d1d:host/owner-host.lisp`, lines 89
# to 91 and 1115 to 1133, unchanged except that the callee's name is the
# fixture's own so the current owner-host definitions do not shadow it.
DEFECT_9C344D1D = """
(defun fn-zz-clock-observation (state)
  (declare (xargs :stobjs state :mode :program))
  (value (fn-own-clock (fn-owner-core state))))

(defun fn-zz-peer-carried-event
    (coordinates msgid received group-codes obligation subject evidence charge
                 observed-ml-key ed-observation ml-observation state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((s (fn-owner-store state))
         (groups (fn-store-groups-from-codes
                  group-codes
                  (fn-state-groups (fn-node-acceptance (fn-sn-node s))))))
    (value
     (if (equal groups :bad) nil
       (fn-pa-authorized-event
        (first coordinates) (second coordinates) (third coordinates)
        (fn-store-octets->string msgid) received groups
        (fn-store-octets->string obligation)
        (fn-store-octets->string subject)
        (fn-store-octets->string evidence) charge
        (fn-sn-keyring-snapshots s)
        observed-ml-key ed-observation ml-observation
        (fn-zz-clock-observation state))))))
"""


def findings_for(text: str) -> list[dict]:
    report = host_shape_check.analyze({FIXTURE: textwrap.dedent(text)})
    return [row for row in report.findings if row["where"].startswith(FIXTURE)]


class TheDefect(unittest.TestCase):
    def test_9c344d1d_owner_host_has_exactly_the_one_finding(self):
        historical = subprocess.run(
            ["git", "-C", str(ROOT), "show", "9c344d1d:host/owner-host.lisp"],
            capture_output=True, text=True, check=True).stdout
        report = host_shape_check.analyze({"host/owner-host.lisp": historical})
        self.assertEqual(
            [(row["definition"], row["callee"]) for row in report.findings],
            [("fn-owner-peer-carried-event", "fn-owner-clock-observation")])
        self.assertIn("error triple", report.findings[0]["problem"])
        self.assertIn("fn-pa-authorized-event", report.findings[0]["problem"])

    def test_reduced_fixture_is_one_finding(self):
        found = findings_for(DEFECT_9C344D1D)
        self.assertEqual(len(found), 1, found)
        self.assertEqual(found[0]["callee"], "fn-zz-clock-observation")

    def test_the_fix_is_clean(self):
        # 1a9dd747's repair: read the owner clock directly, one value.
        fixed = DEFECT_9C344D1D.replace(
            "(fn-zz-clock-observation state))))))",
            "(fn-own-clock (fn-owner-core state)))))))")
        self.assertEqual(findings_for(fixed), [])


class Positions(unittest.TestCase):
    """Each single-value position, and the mv-let arity, refuses a triple."""

    PRELUDE = """
    (defun fn-zz-triple (state)
      (declare (xargs :stobjs state :mode :program))
      (value 7))
    (defun fn-zz-pair (x)
      (mv x x))
    (defun fn-zz-one (x)
      (cons x x))
    (defun fn-zz-rec (xs state)
      (declare (xargs :stobjs state :mode :program))
      (if (endp xs) (fn-zz-rec-done state) (fn-zz-rec (cdr xs) state)))
    (defun fn-zz-rec-done (state)
      (declare (xargs :stobjs state :mode :program))
      (mv nil :done state))
    """

    def one(self, body: str) -> list[dict]:
        return findings_for(self.PRELUDE + """
        (defun fn-zz-subject (x state)
          (declare (xargs :stobjs state :mode :program))
          {})""".format(body))

    def assertFlags(self, body: str, fragment: str):
        found = self.one(body)
        self.assertEqual(len(found), 1, found)
        self.assertIn(fragment, found[0]["problem"])

    def test_let_binding(self):
        self.assertFlags("(let ((v (fn-zz-triple state))) (value v))", "`let` binding")

    def test_let_star_binding(self):
        self.assertFlags("(let* ((v (fn-zz-pair x))) (value v))", "`let*` binding")

    def test_if_test(self):
        self.assertFlags("(if (fn-zz-triple state) (value 1) (value 2))", "`if` test")

    def test_value_argument(self):
        self.assertFlags("(value (fn-zz-triple state))", "`value` argument")

    def test_list_element(self):
        self.assertFlags("(value (list x (fn-zz-pair x)))", "argument of `list`")

    def test_cond_test_and_arms(self):
        self.assertFlags("(cond ((fn-zz-pair x) (value 1)) (t (value 2)))", "`cond` test")
        self.assertFlags("(cond ((consp x) (value 1)) (t x))", "`cond` arm")

    def test_if_arms_disagree(self):
        self.assertFlags("(if (consp x) (value 1) nil)", "`if` arm")

    def test_case_key(self):
        self.assertFlags("(case (fn-zz-triple state) (:a (value 1)) (t (value 2)))", "`case` key")

    def test_mv_let_of_a_single_value(self):
        self.assertFlags("(mv-let (a b c) (fn-zz-one x) (mv a b c))", "`mv-let` of 3")

    def test_mv_let_of_the_wrong_count(self):
        self.assertFlags("(mv-let (a b c) (fn-zz-pair x) (mv a b c))", "`mv-let` of 3")

    def test_er_progn_of_a_single_value(self):
        self.assertFlags("(er-progn (fn-zz-one x) (value x))", "`er-progn` form")

    def test_er_let_star_binding(self):
        self.assertFlags("(er-let* ((v (fn-zz-one x))) (value v))", "`er-let*` binding")

    def test_pprogn_non_final(self):
        self.assertFlags("(pprogn (fn-zz-triple state) (value x))", "`pprogn`")

    def test_recursive_callee_gets_its_shape(self):
        self.assertFlags("(value (fn-zz-rec x state))", "`value` argument")

    def test_accepted_forms_are_clean(self):
        for body in (
                "(mv-let (erp val state) (fn-zz-triple state) (value (list erp val)))",
                "(mv-let (a b) (fn-zz-pair x) (value (list a b)))",
                "(er-let* ((v (fn-zz-triple state))) (value (cons v x)))",
                "(er-progn (fn-zz-triple state) (fn-zz-rec x state))",
                "(if (consp x) (fn-zz-triple state) (mv t nil state))",
                "(cond ((consp x) (value 1)) (t (er soft 'fn \"no ~x0\" x)))",
                "(let ((state (f-put-global 'fn-zz x state))) (value (fn-zz-one x)))",
                "(pprogn (f-put-global 'fn-zz x state) (value x))",
                "(prog2$ (cw \"~x0\" x) (fn-zz-triple state))",
                "(value (mv-list 3 (fn-zz-triple state)))"):
            with self.subTest(body=body):
                self.assertEqual(self.one(body), [])

    def test_unmodelled_macro_is_undecidable_not_a_finding(self):
        report = host_shape_check.analyze({FIXTURE: textwrap.dedent(self.PRELUDE + """
        (defun fn-zz-subject (x state)
          (declare (xargs :stobjs state :mode :program))
          (value (fn-zz-no-such-macro x)))""")})
        self.assertEqual([r for r in report.findings if r["where"].startswith(FIXTURE)], [])
        self.assertGreaterEqual(report.counts["undecidable"], 1)

    def test_raw_mode_region_is_not_checked(self):
        found = findings_for(self.PRELUDE + """
        (progn! (set-raw-mode t)
          (defun fn-zz-raw (state) (list (fn-zz-triple state))))""")
        self.assertEqual(found, [])


class TheTree(unittest.TestCase):
    def test_current_tree_has_no_findings(self):
        report = host_shape_check.analyze()
        self.assertEqual(report.findings, [])
        self.assertGreater(report.counts["positions"], 1000)
        self.assertGreater(report.counts["multi_valued_definitions"], 0)


if __name__ == "__main__":
    unittest.main()
