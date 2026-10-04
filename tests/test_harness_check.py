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
from unittest import mock
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


class RawArityTests(unittest.TestCase):
    """`raw-arity`: calls of the native host's raw Common Lisp `defun`s."""

    def scan(self, source: str, acl2_arity=None):
        from tools import ledger
        forms = ledger.Reader(textwrap.dedent(source)).top_level()
        return harness_check.raw_arity_scan(
            {"host/native/x.lisp": forms}, frozenset(), acl2_arity)[0]

    # The break it exists for, in the shape it had at dev 552c763e
    # (host/native/bp-app.lisp:213-215): nine required parameters, eight
    # arguments, the ingress dropped.
    DROPPED_INGRESS = """
        (defun fnn-bpapp-accept-locked
            (service journal inbound-id request node-id bundle-identity
                     ingress bundle-source bundle-destination)
          (list service journal inbound-id request node-id bundle-identity
                ingress bundle-source bundle-destination))
        (defun fnn-bpapp-deliver (service journal node-id identity adu source destination)
          (multiple-value-setq (app-result receipt)
            (fnn-owner-serialized
             service nil
             (lambda ()
               (fnn-bpapp-accept-locked
                service journal inbound-id (fnn-octets adu) node-id
                (fnn-octets identity) source destination)))))
        """

    def test_the_eight_of_nine_call_is_caught(self):
        found = self.scan(self.DROPPED_INGRESS)
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0]["callee"], "fnn-bpapp-accept-locked")
        self.assertEqual(found[0]["problem"], "called with 8 arguments and takes 9")

    def test_the_nine_argument_call_is_clean(self):
        fixed = self.DROPPED_INGRESS.replace(
            "(fnn-octets identity) source destination",
            "(fnn-octets identity) ingress source destination")
        self.assertEqual(self.scan(fixed), [])

    def test_optional_rest_and_key_bound_the_count(self):
        source = """
            (defun fnn-a (x &optional y) (list x y))
            (defun fnn-b (x &rest ys) (list x ys))
            (defun fnn-c (x &key y) (list x y))
            (defun fnn-use () (list (fnn-a 1) (fnn-a 1 2) (fnn-a 1 2 3)
                                    (fnn-b) (fnn-b 1 2 3 4) (fnn-c 1 :y 2)))
            """
        found = [(row["callee"], row["problem"]) for row in self.scan(source)]
        self.assertEqual(sorted(found), [
            ("fnn-a", "called with 3 arguments and takes 1 to 2"),
            ("fnn-b", "called with 0 arguments and takes at least 1")])

    def test_binders_quote_and_local_functions_are_not_calls(self):
        source = """
            (defun fnn-a (x) x)
            (defun fnn-use (fnn-a)
              (flet ((fnn-a (x y) (list x y)))
                (list (fnn-a 1 2) '(fnn-a 1 2) #'fnn-a
                      (multiple-value-bind (fnn-a b) (values 1 2) (list b)))))
            """
        self.assertEqual(self.scan(source), [])

    def test_a_funcall_of_a_named_function_is_a_call(self):
        found = self.scan("(defun fnn-a (x) x) (defun fnn-u () (funcall #'fnn-a 1 2))")
        self.assertEqual([row["callee"] for row in found], ["fnn-a"])

    def test_a_dispatched_acl2_call_counts_state(self):
        source = """
            (defun fnn-core (name &rest args) (list name args))
            (defun fnn-core-state (name &rest args) (list name args))
            (defun fnn-u (o)
              (list (fnn-core 'fn-pure o) (fnn-core-state 'fn-pure o)
                    (fnn-core-state 'fn-stateful o)))
            """
        stale = set(harness_check.RAW_DISPATCHERS) - {"fnn-core", "fnn-core-state"}
        found = [row for row in self.scan(source, {"fn-pure": 1, "fn-stateful": 2})
                 if row["callee"] not in stale]
        self.assertEqual([(row["callee"], row["problem"]) for row in found], [
            ("fn-pure", "dispatched with 2 arguments (state included) and takes 1")])

    def test_cold_dispatch_macros_count_literal_subject_arguments(self):
        source = """
            (defmacro fnn-core-cold-values (name &rest arguments)
              `(fnn-cold-call ,name ,@arguments))
            (defmacro fnn-core-cold-single (name &rest arguments)
              `(first (fnn-cold-call ,name ,@arguments)))
            (defmacro fnn-core-cold-pool (name &rest arguments)
              `(fnn-cold-call ,name ,@arguments (fnn-live-page-read-pool)))
            (defun fnn-u ()
              (list (fnn-core-cold-values 'fn-cold 7 8)
                    (fnn-core-cold-single 'fn-cold 7 8)
                    (fnn-core-cold-pool 'fn-cold 7)
                    (fnn-core-cold-values 'fn-cold 7)
                    (fnn-core-cold-single 'fn-cold 7 8 9)
                    (fnn-core-cold-pool 'fn-cold 7 8)
                    '(fnn-core-cold-values 'fn-cold)
                    `(fnn-core-cold-pool 'fn-cold)))
            """
        found = self.scan(source, {"fn-cold": 2})
        macro_names = {"fnn-core-cold-values", "fnn-core-cold-single",
                       "fnn-core-cold-pool"}
        self.assertFalse([row for row in found if row["callee"] in macro_names])
        self.assertEqual([row["problem"] for row in found
                          if row["callee"] == "fn-cold"], [
            "dispatched with 1 argument (state included) and takes 2",
            "dispatched with 3 arguments (state included) and takes 2",
            "dispatched with 3 arguments (state included) and takes 2"])

    def test_cold_dispatch_macro_wrong_signature_is_stale(self):
        found = self.scan("""
            (defmacro fnn-core-cold-pool (name argument)
              `(fnn-cold-call ,name ,argument (fnn-live-page-read-pool)))
            """, {"fn-cold": 2})
        rows = [row for row in found if row["callee"] == "fnn-core-cold-pool"]
        self.assertEqual(len(rows), 1)
        self.assertIn("RAW_DISPATCHERS names it", rows[0]["problem"])

    def test_pool_dispatch_counts_the_dedicated_stobj(self):
        source = """
            (defun fnn-core-page-read-pool (name &rest args) (list name args))
            (defun fnn-u ()
              (list (fnn-core-page-read-pool 'fn-cold 7 '(1 2))
                    (fnn-core-page-read-pool 'fn-cold 7)))
            """
        found = [row for row in self.scan(source, {"fn-cold": 3})
                 if row["callee"] == "fn-cold"]
        self.assertEqual([(row["callee"], row["problem"]) for row in found], [
            ("fn-cold", "dispatched with 2 arguments (state included) and takes 3")])

    def test_buffer_state_dispatch_counts_buffer_and_trailing_arena_run(self):
        source = """
            (defun fnn-core-buffer-state (name &rest args) (list name args))
            (defun fnn-u ()
              (list (fnn-core-buffer-state 'fn-refuse 7 0 :unavailable)
                    (fnn-core-buffer-state 'fn-refuse 7)))
            """
        with patch.dict(harness_check.ARENA_ENTRIES, {"fn-refuse": 2}):
            found = [row for row in self.scan(source, {"fn-refuse": 7})
                     if row["callee"] == "fn-refuse"]
        self.assertEqual([(row["callee"], row["problem"]) for row in found], [
            ("fn-refuse", "dispatched with 5 arguments (state included) and takes 7")])

    def test_the_tree_has_no_raw_arity_finding(self):
        found, counts = harness_check.raw_arity_findings(ROOT)
        self.assertEqual(found, [])
        self.assertGreater(counts["applications"], 1000)
        self.assertGreater(counts["dispatched_applications"], 500)


class DuplicateDefunTests(unittest.TestCase):
    """`duplicate-defun`: a raw name defined twice across one image's files."""

    def scan(self, **files):
        from tools import ledger
        return harness_check.duplicate_defun_scan(
            {"host/native/{}.lisp".format(name): ledger.Reader(
                textwrap.dedent(source)).top_level()
             for name, source in files.items()})[0]

    # The break it exists for, in the shape it had at dev 8fd16ef72
    # (host/native/io.lisp): the service log's writer, then a log rig's
    # printer under the same name, which replaced it in the image.
    TWO_LOG_LINES = """
        (defun fnn-log-line (line)
          (fnn-out "~a" line))
        (defun fnn-log-start (log)
          (fnn-log-line "started"))
        (defun fnn-log-line (what log size)
          (fnn-out "~a ~a ~a" what log size))
        """

    def test_the_fnn_log_line_double_definition_is_caught(self):
        found = self.scan(io=self.TWO_LOG_LINES)
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0]["callee"], "fnn-log-line")
        self.assertEqual(found[0]["where"], "host/native/io.lisp:6")
        self.assertEqual(found[0]["defined"], "host/native/io.lisp:2")

    def test_the_renamed_rig_printer_is_clean(self):
        fixed = self.TWO_LOG_LINES.replace(
            "(defun fnn-log-line (what log size)",
            "(defun fnn-log-kernel-line (what log size)")
        self.assertEqual(self.scan(io=fixed), [])

    def test_a_definition_in_another_file_is_caught(self):
        found = self.scan(a="(defun fnn-x () 1)", b="(defun fnn-x (y) y)")
        self.assertEqual([(row["callee"], row["where"], row["defined"]) for row in found],
                         [("fnn-x", "host/native/b.lisp:1", "host/native/a.lisp:1")])

    def test_a_nested_definition_is_a_definition(self):
        found = self.scan(a="(defun fnn-x () 1)",
                          b="(eval-when (:load-toplevel) (let ((z 1)) (defun fnn-x () z)))")
        self.assertEqual([row["callee"] for row in found], ["fnn-x"])

    def test_quoted_data_and_local_functions_are_not_definitions(self):
        source = """
            (defun fnn-x () 1)
            (defun fnn-y () (list '(defun fnn-x () 2) (flet ((fnn-x () 3)) (fnn-x))))
            """
        self.assertEqual(self.scan(a=source), [])

    def test_each_images_entry_is_the_named_exemption(self):
        self.assertEqual(self.scan(build="(defun fn-native-entry (state) state)",
                                   io="(defun fn-native-entry (st) st)"), [])
        self.assertIn("fn-native-entry", harness_check.DUPLICATE_ALLOWED)

    def test_the_tree_has_no_duplicate_definition(self):
        found, counts = harness_check.duplicate_defun_findings(ROOT)
        self.assertEqual(found, [])
        self.assertGreater(counts["definitions"], 1000)


class DerivedStubTests(unittest.TestCase):
    """test-stubs / test-harness-reach (entry-guards-2): a call an extracted
    host function makes is stubbed by hand, extracted, or covered by a
    derived stub whose lambda list is the host's; the derived block is
    compared with what the host derives today."""

    HOST = textwrap.dedent("""
        (defun fnn-top (service octets)
          (fnn-a service octets)
          (fnn-b service octets 1))
        (defun fnn-a (service extra) (list service extra))
        (defun fnn-b (service octets &optional (n 0) &key ((:why reason) nil)
                      &aux (x 1))
          (list service octets n reason x))
        """)

    def scan(self, host: str, harness: str):
        from tools import ledger
        forms = ledger.Reader(host).top_level()
        rawdefs, _ = harness_check.raw_definitions({"host/native/x.lisp": forms})
        bodies, origins = {}, {}
        for form, _line in forms:
            name = str(form[1]).lower()
            bodies[name] = form
            origins[name] = (form[2], "host/native/x.lisp")
        return harness_check.harness_scan("tests/native_x_raw.lisp", harness,
                                          rawdefs, bodies, origins)

    HARNESS = textwrap.dedent("""
        (defpackage "ACL2" (:use "CL"))
        (in-package "ACL2")
        (defun fnn-a (service) service)
        ;; extracts fnn-top from host/native/x.lisp
        """)

    def test_the_host_lambda_list_is_derived_without_defaults(self):
        from tools import ledger
        formals = ledger.Reader(
            "(a b &optional (c 1) &key ((:k v) 2) d &aux (x 1))").top_level()[0][0]
        self.assertEqual(harness_check.derived_lambda_list(formals),
                         ("(a b &optional c &key ((:k v)) d)", ["a", "b", "c", "v", "d"]))

    def test_a_stale_hand_stub_and_an_unstubbed_call_are_both_found(self):
        scan = self.scan(self.HOST, self.HARNESS)
        self.assertEqual([row["callee"] for row in scan["stale"]], ["fnn-a"])
        self.assertEqual(sorted(scan["unresolved"]), ["fnn-b"])
        self.assertIsNone(scan["current"])
        self.assertIn("(defun fnn-b (service octets &optional n &key ((:why reason)))",
                      scan["expected"])
        self.assertIn("(harness-stub-reached 'fnn-b \"host/native/x.lisp\")",
                      scan["expected"])

    def test_the_written_block_is_current_and_goes_stale_with_the_host(self):
        first = self.scan(self.HOST, self.HARNESS)
        written = harness_check.with_stub_block(self.HARNESS, first["expected"])
        self.assertLess(written.index('(in-package "ACL2")'),
                        written.index(harness_check.STUB_BEGIN))
        again = self.scan(self.HOST, written)
        self.assertEqual(again["current"], again["expected"])
        # The derived stubs are not hand stubs: the reach is unchanged.
        self.assertEqual(sorted(again["unresolved"]), ["fnn-b"])
        # The host's fnn-b grows a formal: the block is stale.
        changed = self.HOST.replace("(service octets &optional", "(service octets more &optional")
        drifted = self.scan(changed, written)
        self.assertNotEqual(drifted["current"], drifted["expected"])
        # Rewriting replaces the block in place, once.
        rewritten = harness_check.with_stub_block(written, drifted["expected"])
        self.assertEqual(rewritten.count(harness_check.STUB_BEGIN), 1)
        self.assertIn("(service octets more &optional n", rewritten)

    def test_a_hand_stub_takes_the_call_out_of_the_block(self):
        harness = self.HARNESS + "(defun fnn-b (service octets n) (list service octets n))\n"
        scan = self.scan(self.HOST, harness)
        self.assertEqual(scan["unresolved"], {})
        self.assertIsNone(scan["expected"])

    def test_the_tree_has_no_stale_stub_and_no_unresolved_call(self):
        findings, counts = harness_check.test_stub_findings(ROOT)
        self.assertEqual(findings, [])
        reach, _ = harness_check.test_harness_reach_findings(ROOT)
        self.assertEqual(reach, [])
        self.assertGreater(counts["derived_stubs"], 0)
        self.assertTrue(harness_check.LINTS["test-harness-reach"][1], "reach gates")


class RawMacroTemplateTests(unittest.TestCase):
    def calls(self, source):
        from tools import ledger
        calls = []
        for form, _ in ledger.Reader(source).top_level():
            harness_check.raw_applications(form, calls)
        return calls

    def test_section_envelope_literal_core_calls_are_inventory(self):
        calls = self.calls("""(defmacro envelope (s classes c &body body)
          `(let ((gate (fnn-gate ,s)))
             (when (fn-fs-section-class-ok ,classes ,c)
               (fnn-section ,s ,@body))
             (fn-fs-unwind ,c nil)))""")
        self.assertTrue(("fn-fs-section-class-ok", 2) in calls,
                        "literal macro core calls must be inventoried")
        self.assertIn(("fn-fs-unwind", 2), calls)
        self.assertIn(("fnn-section", None), calls)
        self.assertIn(("fnn-gate", 1), calls)

    def test_interpolated_heads_and_quoted_data_are_not_calls(self):
        calls = self.calls("""(defmacro envelope (name x)
          `(progn (,name ,x) '(fn-data ,x) (fn-live ,(fn-expand x))
                  (fnn-call ',name ,x) (fnn-call 'fn-known ,x)))""")
        self.assertIn(("fn-live", 1), calls)
        self.assertIn(("fn-expand", 1), calls)
        self.assertIn(("'fn-known", 1), calls)
        self.assertFalse(any(name in {"name", "fn-data", "'name"}
                             for name, _ in calls), calls)

    def test_normal_backquote_is_data_and_nested_template_is_opaque(self):
        calls = self.calls("""(defun data (x) `(fn-data ,(fn-active x)))
          (defmacro nested (x) `(list `(fn-inner ,(fn-inner-expand x))))""")
        self.assertIn(("fn-active", 1), calls)
        self.assertFalse(any(name in {"fn-data", "fn-inner", "fn-inner-expand"}
                             for name, _ in calls), calls)

    def test_local_function_shadowing_and_macrolet_templates(self):
        calls = self.calls("""(macrolet ((m (x) `(flet ((fn-local (y) y))
                                            (fn-local ,x) (fn-real ,x))))
                              (m 1))""")
        self.assertIn(("fn-real", 1), calls)
        self.assertFalse(any(name == "fn-local" for name, _ in calls), calls)

    def test_splices_do_not_invent_an_arity_but_fixed_template_calls_check(self):
        found = RawArityTests().scan("""(defun fnn-target (a b) a)
          (defmacro uncertain (&body body) `(fnn-target ,@body))
          (defmacro wrong (x) `(fnn-target ,x))""")
        self.assertEqual(len(found), 1, found)
        self.assertIn("called with 1 argument", found[0]["problem"])


class NestedFixtureTests(unittest.TestCase):
    HOST = """(defun fnn-top (x) (fnn-real x) (fnn-missing x))
(defun fnn-real (x) x)
(defun fnn-missing (x) x)
"""

    def sources(self):
        from tools import ledger
        return {"host/native/example.lisp": ledger.Reader(self.HOST).top_level()}

    def test_existing_scan_api_preserves_real_nested_extraction(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "tests").mkdir()
            (root / "tests/parent.lisp").write_text('(load "tests/child.lisp")\n; extract fnn-top\n')
            (root / "tests/child.lisp").write_text(
                '(load-deployed-forms "host/native/example.lisp" \'((defun fnn-real)))\n')
            with mock.patch.object(harness_check, "raw_host_sources", return_value=self.sources()):
                rows = harness_check.harness_scans(root)
            parent = next(scan for _, name, _, scan in rows if name == "tests/parent.lisp")
            self.assertTrue("fnn-real" not in parent["unresolved"],
                            "real function extracted by nested fixture must not be overwritten")
            self.assertEqual(set(parent["unresolved"]), {"fnn-missing"})
            self.assertNotIn("(defun fnn-real", parent["expected"])

    def test_nested_hand_stub_arity_is_checked(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "tests").mkdir()
            (root / "tests/parent.lisp").write_text('(load "tests/child.lisp")\n; extract fnn-top\n')
            (root / "tests/child.lisp").write_text('(defun fnn-real () nil)')
            with mock.patch.object(harness_check, "raw_host_sources", return_value=self.sources()):
                rows = harness_check.harness_scans(root)
            parent = next(scan for _, name, _, scan in rows if name == "tests/parent.lisp")
            self.assertEqual([r["callee"] for r in parent["stale"]], ["fnn-real"])

    def test_quoted_and_dynamic_load_mentions_are_not_followed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            text = '(defun loader () (load "tests/missing.lisp"))\n\'(load "tests/missing.lisp")\n(load variable)'
            self.assertEqual(harness_check.harness_fixture_sources(root, "tests/root.lisp", text),
                             {"tests/root.lisp": text})

    def test_nested_cycle_missing_file_and_escape_refuse(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "tests").mkdir()
            (root / "tests/child.lisp").write_text('(load "tests/root.lisp")')
            for text, message in (('(load "tests/child.lisp")', "cycle"),
                                  ('(load "tests/missing.lisp")', "unreadable"),
                                  ('(load "../outside.lisp")', "escapes")):
                with self.subTest(text=text), self.assertRaisesRegex(ValueError, message):
                    harness_check.harness_fixture_sources(root, "tests/root.lisp", text)

    def test_nested_generated_trap_is_not_treated_as_a_real_hand_definition(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory); (root / "tests").mkdir()
            block = harness_check.derived_stub_block({"fnn-missing": (["x"], "host/native/example.lisp")})
            (root / "tests/child.lisp").write_text(block)
            sources = harness_check.harness_fixture_sources(root, "tests/root.lisp", '(load "tests/child.lisp")')
            self.assertNotIn("fnn-missing", sources["tests/child.lisp"])


if __name__ == "__main__":
    unittest.main()
