"""Teeth for `tools/harness_check.py`: the break it exists for, and its limits.

The signature lint exists because one host entry point gained a required
keyword-only argument and two callers in `tests/` were never updated, with no
error until the line ran. The first case below is that break, reduced to its
shape and pinned here so it stays caught. The rest are the two ways a lint
like this goes wrong: flagging a call that is fine, and passing a call that is
not.

Nothing here runs ACL2 or touches the real tree; each case builds a throwaway
corpus in a temporary directory and points the lint at it.
"""

import ast
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from tools import harness_check  # noqa: E402


def corpus(**files) -> tempfile.TemporaryDirectory:
    """A throwaway tree: `corpus(tools__host="...", tests__caller="...")`."""
    temporary = tempfile.TemporaryDirectory(prefix="fn-harness-check-")
    root = Path(temporary.name)
    for name, source in files.items():
        relative = name.replace("__", "/") + ".py"
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(source).lstrip(), encoding="utf-8")
    return temporary


HOST = """
    def receive_bpa_request(*, store_root, bid, inventory, download, delete,
                            bundle, source_eid, local_policy_authorized=True):
        return (store_root, bid, bundle)


    class Inbox:
        def __init__(self, stage_dir, *, destination_eid="ipn:2.1"):
            self.stage_dir = stage_dir
"""


class SignatureLintTests(unittest.TestCase):
    def findings(self, temporary) -> list:
        found, counts = harness_check.signature_findings(Path(temporary.name))
        self.counts = counts
        return found

    def test_the_2026_09_19_break_is_reported_with_both_line_numbers(self):
        """The incident, reduced: a caller that predates a required keyword."""
        temporary = corpus(tools__run_bp_receive=HOST, tests__ltp__lab="""
            from tools.run_bp_receive import receive_bpa_request

            def main(inbox, bid):
                return receive_bpa_request(
                    store_root="b", bid=bid, inventory=inbox.inventory,
                    download=inbox.download, delete=inbox.delete,
                    source_eid="ipn:1.1", local_policy_authorized=True)
        """)
        with temporary:
            found = self.findings(temporary)
            self.assertEqual(len(found), 1, found)
            self.assertEqual(found[0]["callee"], "receive_bpa_request")
            self.assertIn("missing 1 required argument: 'bundle'",
                          found[0]["problem"])
            self.assertTrue(found[0]["where"].endswith("tests/ltp/lab.py:4"),
                            found[0]["where"])
            self.assertTrue(found[0]["defined"].endswith(
                "tools/run_bp_receive.py:1"), found[0]["defined"])

    def test_the_repaired_caller_is_not_reported(self):
        temporary = corpus(tools__run_bp_receive=HOST, tests__ltp__lab="""
            from tools.run_bp_receive import receive_bpa_request

            def main(inbox, bid):
                return receive_bpa_request(
                    store_root="b", bid=bid, inventory=inbox.inventory,
                    download=inbox.download, delete=inbox.delete,
                    bundle=inbox.bundle, source_eid="ipn:1.1")
        """)
        with temporary:
            self.assertEqual(self.findings(temporary), [])
            self.assertEqual(self.counts["resolved"], 1)

    def test_a_misspelled_keyword_is_reported_as_unexpected(self):
        temporary = corpus(tools__run_bp_receive=HOST, tests__caller="""
            from tools import run_bp_receive

            def main(inbox, bid):
                return run_bp_receive.receive_bpa_request(
                    store_root="b", bid=bid, inventory=inbox.inventory,
                    download=inbox.download, delete=inbox.delete,
                    bundles=inbox.bundle, source_eid="ipn:1.1")
        """)
        with temporary:
            found = self.findings(temporary)
            problems = " ".join(row["problem"] for row in found)
            self.assertIn("unexpected keyword argument 'bundles'", problems)
            self.assertIn("missing 1 required argument: 'bundle'", problems)

    def test_a_constructor_is_bound_like_any_other_call(self):
        temporary = corpus(tools__run_bp_receive=HOST, tests__caller="""
            from tools.run_bp_receive import Inbox

            def main():
                return Inbox()
        """)
        with temporary:
            found = self.findings(temporary)
            self.assertEqual(len(found), 1, found)
            self.assertIn("missing 1 required argument: 'stage_dir'",
                          found[0]["problem"])

    def test_a_star_args_call_is_declined_rather_than_guessed(self):
        """`f(**rest)` is decidable only at run time; the lint counts it."""
        temporary = corpus(tools__run_bp_receive=HOST, tests__caller="""
            from tools.run_bp_receive import receive_bpa_request

            def main(rest):
                return receive_bpa_request(**rest)
        """)
        with temporary:
            self.assertEqual(self.findings(temporary), [])
            self.assertEqual(self.counts["undecidable"], 1)

    def test_a_callee_taking_kwargs_absorbs_an_unknown_keyword(self):
        temporary = corpus(tools__host="""
            def entry(a, **rest):
                return (a, rest)
        """, tests__caller="""
            from tools.host import entry

            def main():
                return entry(a=1, whatever=2)
        """)
        with temporary:
            self.assertEqual(self.findings(temporary), [])

    def test_a_locally_rebound_name_is_not_resolved(self):
        """A shadowed import is not the definition, so the lint declines."""
        temporary = corpus(tools__host="""
            def entry(a, b):
                return (a, b)
        """, tests__caller="""
            from tools.host import entry

            entry = lambda *args: args

            def main():
                return entry(1)
        """)
        with temporary:
            self.assertEqual(self.findings(temporary), [])

    def test_a_self_call_resolves_through_a_base_in_another_file(self):
        """`twonode_gate` subclasses `deploy_gate`; the lint follows that."""
        temporary = corpus(tools__deploy_gate="""
            class Gate:
                def skip(self, name, command, reason):
                    return (name, command, reason)
        """, tools__twonode_gate="""
            from tools.deploy_gate import Gate

            class TwoNode(Gate):
                def run(self):
                    self.skip("a", "b")
        """)
        with temporary:
            found = self.findings(temporary)
            self.assertEqual(len(found), 1, found)
            self.assertEqual(found[0]["callee"], "Gate.skip")
            self.assertIn("missing 1 required argument: 'reason'",
                          found[0]["problem"])


class Acl2ArityWalkTests(unittest.TestCase):
    """The host-file walker, over the binders fn actually writes."""

    def applications(self, source: str) -> dict:
        from tools import ledger
        found = []
        for form, _line in ledger.Reader(source).top_level():
            harness_check.acl2_applications(form, found)
        return {name: count for name, count in found}

    def test_an_application_is_counted_with_its_arity(self):
        found = self.applications("(defun f (x) (fn-g x 1 2))")
        self.assertEqual(found.get("fn-g"), 3)

    def test_a_let_binding_variable_is_not_an_application(self):
        found = self.applications(
            "(defun f (x) (let ((a (fn-g x)) (b 2)) (fn-h a b)))")
        self.assertEqual(found.get("fn-g"), 1)
        self.assertEqual(found.get("fn-h"), 2)
        self.assertNotIn("a", found)
        self.assertNotIn("b", found)

    def test_a_cond_clause_head_is_a_test_and_not_a_head(self):
        found = self.applications(
            "(defun f (x) (cond ((fn-p x) 1) (t (fn-q x 2))))")
        self.assertEqual(found.get("fn-p"), 1)
        self.assertEqual(found.get("fn-q"), 2)

    def test_a_quoted_list_is_not_walked(self):
        found = self.applications("(defun f (x) (member x '(fn-g fn-h)))")
        self.assertNotIn("fn-g", found)

    def test_the_formals_of_the_definition_are_not_applications(self):
        found = self.applications("(defun fn-f (octets lines) (fn-g octets))")
        self.assertNotIn("octets", found)
        self.assertEqual(found.get("fn-g"), 1)

    def test_only_a_named_same_line_test_fixture_is_waived(self):
        source = ('form = "(fn-example a)"  '
                  '# acl2-arity-fixture: fn-example synthetic reader input')
        self.assertTrue(harness_check.declared_arity_fixture(source, "fn-example"))
        self.assertFalse(harness_check.declared_arity_fixture(source, "fn-other"))
        self.assertFalse(harness_check.declared_arity_fixture(
            'form = "(fn-example a)"', "fn-example"))
        self.assertFalse(harness_check.declared_arity_fixture(
            'form = "(fn-example a)"  # acl2-arity-fixture: fn-example',
            "fn-example"))
        self.assertFalse(harness_check.declared_arity_fixture(
            'form = "# acl2-arity-fixture: fn-example fake comment"',
            "fn-example"))

    def test_unwaived_acl2_arity_finding_fails_the_default_gate(self):
        def broken(_root):
            return ([{"where": "host/caller.lisp:7", "callee": "fn-entry",
                      "problem": "called with 1 argument and takes 2"}],
                    {"applications": 1})

        with patch.dict(harness_check.LINTS, {"acl2-arity": (broken, True)}):
            self.assertEqual(harness_check.main(["--lint", "acl2-arity"]), 1)
            self.assertEqual(harness_check.main(["--lint", "acl2-arity",
                                                 "--report"]), 0)


class Acl2InPythonStringTests(unittest.TestCase):
    """ACL2 spelled as text in a Python file, which neither side can see."""

    def written(self, relative: str, source: str):
        """A one-file corpus written verbatim: this source is Python source."""
        temporary = tempfile.TemporaryDirectory(prefix="fn-acl2-string-")
        path = Path(temporary.name) / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        return temporary

    def forms(self, temporary) -> list:
        return list(harness_check.python_acl2_forms(Path(temporary.name)))

    def applications(self, temporary) -> dict:
        found = {}
        for _relative, _line, form in self.forms(temporary):
            if form is None:
                continue
            items = []
            harness_check.acl2_applications(form, items)
            found.update(dict(items))
        return found

    def test_the_served_differential_shape_is_read_with_its_arity(self):
        """`d484e9a` gave fn-served-open a seventh formal; this is the call."""
        temporary = self.written("tests/test_differential.py", '\n'.join([
            '"""A docstring naming (fn-served-open) in prose."""',
            '',
            'def model():',
            '    return ("(fn-served-open *fn-reader-archive* 510 8192"',
            '            " (fn-reader-post-config *fn-reader-archive* nil)"',
            '            " nil nil)")',
            '']))
        with temporary:
            found = self.applications(temporary)
            # Adjacent literals fold into one Constant, so the whole call is
            # one string and its arity is readable.  Seven formals, six here.
            self.assertEqual(found.get("fn-served-open"), 6)
            self.assertEqual(found.get("fn-reader-post-config"), 2)

    def test_a_docstring_is_prose_and_is_not_read(self):
        temporary = self.written("tools/thing.py", '\n'.join([
            '"""The reply code, read by ACL2 (fn-own-feed-response-code)."""',
            '',
            'def code():',
            '    return 1',
            '']))
        with temporary:
            self.assertEqual(self.forms(temporary), [])

    def test_a_placeholder_makes_the_form_undecided(self):
        """`" ".join(...)` in a slot stands for any number of arguments."""
        temporary = self.written("tools/thing.py", '\n'.join([
            'def call(rest):',
            '    return "(fn-served-open {})".format(rest)',
            '']))
        with temporary:
            forms = [form for _r, _l, form in self.forms(temporary)]
            self.assertIn(harness_check.PLACEHOLDER, repr(forms))

    def test_a_sentence_that_mentions_a_form_is_not_a_form(self):
        """Prose in a message, not a call: two v0_matrix findings were this."""
        temporary = self.written("tools/thing.py", '\n'.join([
            'def message():',
            '    return ("posting on this tree is the authenticated "',
            '            "principal\'s allowance (fn-auth-postingp, RFC 3977 "',
            '            "section 6.3.1.1). The feed was never reached.")',
            '']))
        with temporary:
            self.assertEqual([form for _r, _l, form in self.forms(temporary)],
                             [None])

    def test_a_string_that_is_a_fragment_is_declined(self):
        temporary = self.written("tools/thing.py", '\n'.join([
            'def call(rest):',
            '    return "(fn-served-reply-octets (append " + rest',
            '']))
        with temporary:
            self.assertEqual([form for _r, _l, form in self.forms(temporary)],
                             [None])


class WaiverLintTests(unittest.TestCase):
    def findings(self, temporary) -> list:
        found, counts = harness_check.waiver_findings(Path(temporary.name))
        self.counts = counts
        return found

    def test_a_skip_keyed_on_a_failure_message_is_flagged(self):
        """The shape that cost this tree a day of lab evidence."""
        temporary = corpus(tests__test_thing="""
            import unittest

            class T(unittest.TestCase):
                def test_one(self):
                    try:
                        start()
                    except RuntimeError as error:
                        if "books/owner" in str(error):
                            self.skipTest("the owner cluster is mid-repair")
                        raise
        """)
        with temporary:
            found = self.findings(temporary)
            self.assertEqual(len(found), 1, found)
            self.assertIn("reads a failure", found[0]["problem"])

    def test_a_skip_keyed_on_a_return_code_one_assignment_away_is_flagged(self):
        temporary = corpus(tests__test_thing="""
            import unittest

            class T(unittest.TestCase):
                def test_one(self):
                    done = run()
                    code = done.returncode
                    if code != 0:
                        self.skipTest("the tool did not run")
        """)
        with temporary:
            self.assertEqual(len(self.findings(temporary)), 1)

    def test_an_environmental_skip_is_not_flagged(self):
        temporary = corpus(tests__test_thing="""
            import shutil
            import unittest

            @unittest.skipUnless(shutil.which("openssl"), "openssl is not on PATH")
            class T(unittest.TestCase):
                def test_one(self):
                    if shutil.which("acl2") is None:
                        self.skipTest("ACL2 is not on PATH")
        """)
        with temporary:
            self.assertEqual(self.findings(temporary), [])
            self.assertEqual(self.counts["environmental"], 2)

    def test_a_declared_waiver_is_accepted_and_reported(self):
        temporary = corpus(tests__test_thing="""
            import unittest

            class T(unittest.TestCase):
                def test_one(self):
                    done = run()
                    if done.returncode != 0:
                        # waiver-ok: D13 expires 2026-12-01, owner w11/lab-gate
                        self.skipTest("the known refusal")
        """)
        with temporary:
            self.assertEqual(self.findings(temporary), [])
            self.assertEqual(self.counts["declared"], 1)

    def test_a_declaration_with_no_reason_is_not_a_waiver(self):
        temporary = corpus(tests__test_thing="""
            import unittest

            class T(unittest.TestCase):
                def test_one(self):
                    done = run()
                    if done.returncode != 0:
                        # waiver-ok:
                        self.skipTest("the known refusal")
        """)
        with temporary:
            self.assertEqual(len(self.findings(temporary)), 1)

    def test_a_declaration_naming_nothing_traceable_is_not_accepted(self):
        temporary = corpus(tests__test_thing="""
            import unittest

            class T(unittest.TestCase):
                def test_one(self):
                    done = run()
                    if done.returncode != 0:
                        # waiver-ok: it is broken and someone should look
                        self.skipTest("the known refusal")
        """)
        with temporary:
            self.assertEqual(len(self.findings(temporary)), 1)


class BindTests(unittest.TestCase):
    """`Signature.bind` against the cases CPython distinguishes."""

    def signature(self, source: str) -> harness_check.Signature:
        node = ast.parse(textwrap.dedent(source).lstrip()).body[0]
        return harness_check.signature_of(node, "x:1", "f", False)

    def test_a_positional_given_twice_is_reported(self):
        signature = self.signature("def f(a, b): pass")
        self.assertIn("multiple values for argument 'a'",
                      " ".join(signature.bind(1, ["a", "b"])))

    def test_too_many_positionals_are_reported(self):
        signature = self.signature("def f(a): pass")
        self.assertIn("takes 1 positional argument and 2 were given",
                      " ".join(signature.bind(2, [])))

    def test_a_vararg_absorbs_extra_positionals(self):
        signature = self.signature("def f(a, *rest): pass")
        self.assertEqual(signature.bind(4, []), [])

    def test_a_defaulted_keyword_only_is_not_required(self):
        signature = self.signature("def f(a, *, b=1): pass")
        self.assertEqual(signature.bind(1, []), [])

    def test_an_undefaulted_keyword_only_is_required(self):
        signature = self.signature("def f(a, *, b): pass")
        self.assertIn("missing 1 required argument: 'b'",
                      " ".join(signature.bind(1, [])))


if __name__ == "__main__":
    unittest.main()
