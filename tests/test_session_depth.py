"""Unit checks for the session-depth check (`tools/session_depth.py`).

Every fixture below is a small inline book that reconstructs the ladder the
served path really has -- auth over peer over post over the reader session,
with all three base accessors reading `car' -- and then the four wrong-depth
call sites that shipped on 2026-09-20.  The point of the positive cases is
that the checker must flag each of those four; the point of the negative
cases is that it must stay quiet on the corrected spelling, on a correct walk
at a lower level, and on a deliberate wrong-level witness that says so.
"""

import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

SPEC = importlib.util.spec_from_file_location(
    "session_depth", Path(__file__).resolve().parents[1] / "tools" / "session_depth.py"
)
session_depth = importlib.util.module_from_spec(SPEC)
sys.modules["session_depth"] = session_depth
SPEC.loader.exec_module(session_depth)


LADDER = """(in-package "ACL2")
(defun fn-auth-session-base (x) (fn-inj-nth 0 x))
(defun fn-peer-session-base (x) (fn-ag-car x))
(defun fn-post-session-base (x) (fn-inj-nth 0 x))
(defun fn-post-session-awaiting (x) (fn-inj-nth 1 x))
(defun fn-nntp-session-group (x) (car (cdr x)))
(defun fn-post-session-shapep (x) (and (true-listp x) (equal (len x) 2)))
(defun fn-nntp-sessionp (x) (and (true-listp x) (equal (len x) 4)))
(defun fn-post-sessionp (x)
  (and (fn-post-session-shapep x) (fn-nntp-sessionp (fn-post-session-base x))))
(defun fn-peer-sessionp (x) (fn-post-sessionp (fn-peer-session-base x)))
(defun fn-auth-sessionp (x) (fn-peer-sessionp (fn-auth-session-base x)))
(defun fn-served-conn-session (x) (fn-ag-car x))
(defun fn-own-conn-session (c) (fn-ag-car c))
(defmacro fn-peer-reader-session (ps)
  `(fn-post-session-base (fn-peer-session-base ,ps)))
(defmacro fn-auth-post-session (as)
  `(fn-peer-session-base (fn-auth-session-base ,as)))
(defmacro fn-auth-reader-session (as)
  `(fn-peer-reader-session (fn-auth-session-base ,as)))
(defun fn-peer-single (ps text)
  (fn-nntp-single (fn-post-session-base (fn-peer-session-base ps)) text))
(defun fn-peer-transit-outcome (ps submission d completion)
  (fn-peer-single ps (fn-peer-transit-code submission d completion)))
(defun fn-nntp-post-outcome (ps completion)
  (if (not (fn-post-sessionp ps)) nil (fn-post-single ps completion)))
"""


def run(sources: dict[str, str], strict: bool = False):
    """The checker over inline books; returns (findings, exit code)."""
    with tempfile.TemporaryDirectory() as directory:
        paths = []
        for name, text in sources.items():
            path = Path(directory) / name
            path.write_text(text, encoding="utf-8")
            paths.append(str(path))
        books = session_depth.read_books([Path(p) for p in paths])
        levels = session_depth.Levels()
        session_depth.infer(books, levels)
        findings = session_depth.check(books, levels)
        code = session_depth.main((["--strict"] if strict else []) + paths)
    return findings, code


def kinds(findings, kind):
    return [f for f in findings if f.kind == kind and not f.waived]


class LadderInference(unittest.TestCase):
    def test_the_ladder_alone_is_clean(self):
        findings, code = run({"ladder.lisp": LADDER})
        self.assertEqual(kinds(findings, "DEPTH"), [])
        self.assertEqual(kinds(findings, "ARGUMENT"), [])
        self.assertEqual(code, 0)

    def test_a_correct_walk_one_level_down_is_not_a_defect(self):
        # fn-peer-single walks peer -> post -> reader.  It is drift (a walk
        # spelled by hand) and never a defect.
        findings, _ = run({"ladder.lisp": LADDER})
        chains = kinds(findings, "CHAIN")
        self.assertEqual([f.where for f in chains], ["fn-peer-single"])

    def test_a_projection_definition_is_not_drift(self):
        _, code = run({"ladder.lisp": LADDER.replace(
            "(defun fn-peer-single (ps text)\n"
            "  (fn-nntp-single (fn-post-session-base (fn-peer-session-base ps)) text))",
            "(defun fn-peer-single (ps text)\n"
            "  (fn-nntp-single (fn-peer-reader-session ps) text))")}, strict=True)
        self.assertEqual(code, 0)

    def test_the_formals_are_inferred_from_the_calls(self):
        books = session_depth.read_books([])
        levels = session_depth.Levels()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ladder.lisp"
            path.write_text(LADDER, encoding="utf-8")
            books = session_depth.read_books([path])
        session_depth.infer(books, levels)
        self.assertEqual(levels.argument[("fn-peer-transit-outcome", 0)], "peer")
        self.assertEqual(levels.argument[("fn-nntp-post-outcome", 0)], "post")
        self.assertEqual(levels.argument[("fn-peer-single", 0)], "peer")


class TheFourThatShipped(unittest.TestCase):
    """Each of these is the real 2026-09-20 defect, reduced to its shape."""

    def flags(self, body: str, kind: str, mentions: str):
        findings, code = run({"ladder.lisp": LADDER, "site.lisp": body})
        hits = [f for f in kinds(findings, kind) if mentions in f.text]
        self.assertTrue(hits, f"{kind} mentioning {mentions!r} not flagged: "
                              f"{[str(f) for f in findings]}")
        self.assertEqual(code, 1)
        return hits

    def test_own_conn_boundedp_tested_the_post_shape_on_the_whole_session(self):
        self.flags('(in-package "ACL2")\n'
                   "(defun fn-own-conn-boundedp (conn groups)\n"
                   "  (and (fn-post-sessionp (fn-own-conn-session conn)) groups))\n",
                   "ARGUMENT", "wants a post session")

    def test_served_post_outcome_reached_one_wrapper_short(self):
        self.flags('(in-package "ACL2")\n'
                   "(defun fn-served-post-outcome (conn completion)\n"
                   "  (fn-nntp-post-outcome\n"
                   "   (fn-peer-session-base (fn-served-conn-session conn)) completion))\n",
                   "DEPTH", "fn-peer-session-base wants a peer session")

    def test_the_test_side_had_the_same_short_reach(self):
        self.flags('(in-package "ACL2")\n'
                   "(assert-event\n"
                   "  (not (fn-post-session-awaiting\n"
                   "        (fn-post-session-base\n"
                   "         (fn-peer-session-base\n"
                   "          (fn-served-conn-session *conn*))))))\n",
                   "DEPTH", "fn-peer-session-base wants a peer session")

    def test_served_transit_outcome_passed_the_whole_session(self):
        self.flags('(in-package "ACL2")\n'
                   "(defun fn-served-transit-outcome (conn submission decision completion)\n"
                   "  (fn-peer-transit-outcome (fn-served-conn-session conn)\n"
                   "                           submission decision completion))\n",
                   "ARGUMENT", "wants a peer session")

    def test_the_corrected_spellings_are_clean(self):
        findings, code = run({"ladder.lisp": LADDER, "site.lisp":
                              '(in-package "ACL2")\n'
                              "(defun fn-own-conn-boundedp (conn groups)\n"
                              "  (and (fn-auth-sessionp (fn-own-conn-session conn)) groups))\n"
                              "(defun fn-served-post-outcome (conn completion)\n"
                              "  (fn-nntp-post-outcome\n"
                              "   (fn-auth-post-session (fn-served-conn-session conn))\n"
                              "   completion))\n"
                              "(defun fn-served-transit-outcome (conn s d c)\n"
                              "  (fn-peer-transit-outcome\n"
                              "   (fn-auth-session-base (fn-served-conn-session conn)) s d c))\n"
                              "(assert-event\n"
                              "  (not (fn-post-session-awaiting\n"
                              "        (fn-auth-post-session (fn-served-conn-session *conn*)))))\n"})
        self.assertEqual(kinds(findings, "DEPTH"), [])
        self.assertEqual(kinds(findings, "ARGUMENT"), [])
        self.assertEqual(code, 0)


class Bindings(unittest.TestCase):
    def test_a_level_travels_through_let_star(self):
        findings, _ = run({"ladder.lisp": LADDER, "site.lisp":
                           '(in-package "ACL2")\n'
                           "(defun fn-own-conn-boundedp (conn groups)\n"
                           "  (let* ((as (fn-own-conn-session conn))\n"
                           "         (s (fn-post-session-base as)))\n"
                           "    (and s groups)))\n"})
        self.assertTrue([f for f in kinds(findings, "DEPTH")
                         if "fn-post-session-base wants a post session" in f.text])

    def test_a_shadowed_binding_does_not_carry_a_level(self):
        findings, code = run({"ladder.lisp": LADDER, "site.lisp":
                              '(in-package "ACL2")\n'
                              "(defun fn-own-conn-boundedp (conn groups)\n"
                              "  (let ((conn (fn-auth-post-session"
                              " (fn-own-conn-session conn))))\n"
                              "    (and (fn-post-sessionp conn) groups)))\n"})
        self.assertEqual(kinds(findings, "ARGUMENT"), [])
        self.assertEqual(code, 0)


class Waivers(unittest.TestCase):
    def test_a_waiver_with_a_reason_suppresses_and_is_reported(self):
        source = ('(in-package "ACL2")\n'
                  "; session-depth-ok: a deliberate wrong-level witness.\n"
                  "(assert-event (fn-post-sessionp (fn-served-conn-session *forged*)))\n")
        findings, code = run({"ladder.lisp": LADDER, "site.lisp": source})
        waived = [f for f in findings if f.waived]
        self.assertEqual(len(waived), 1)
        self.assertIn("deliberate wrong-level witness", waived[0].waived)
        self.assertEqual(code, 0)

    def test_a_waiver_without_a_reason_is_not_a_waiver(self):
        source = ('(in-package "ACL2")\n'
                  "; session-depth-ok:\n"
                  "(assert-event (fn-post-sessionp (fn-served-conn-session *forged*)))\n")
        findings, code = run({"ladder.lisp": LADDER, "site.lisp": source})
        self.assertEqual([f for f in findings if f.waived], [])
        self.assertEqual(code, 1)

    def test_a_waiver_covers_only_the_form_it_precedes(self):
        source = ('(in-package "ACL2")\n'
                  "; session-depth-ok: only the next form.\n"
                  "(assert-event (fn-post-sessionp (fn-served-conn-session *a*)))\n"
                  "(assert-event (fn-post-sessionp (fn-served-conn-session *b*)))\n")
        findings, code = run({"ladder.lisp": LADDER, "site.lisp": source})
        self.assertEqual(len([f for f in findings if f.waived]), 1)
        self.assertEqual(len(kinds(findings, "ARGUMENT")), 1)
        self.assertEqual(code, 1)


class Drift(unittest.TestCase):
    def test_a_hand_spelled_walk_is_drift_and_fails_only_under_strict(self):
        source = ('(in-package "ACL2")\n'
                  "(defun fn-served-post-outcome (conn completion)\n"
                  "  (fn-nntp-post-outcome\n"
                  "   (fn-peer-session-base"
                  " (fn-auth-session-base (fn-served-conn-session conn)))\n"
                  "   completion))\n")
        findings, code = run({"ladder.lisp": LADDER, "site.lisp": source})
        chains = [f for f in kinds(findings, "CHAIN")
                  if "fn-auth-post-session" in f.text]
        self.assertTrue(chains)
        self.assertEqual(kinds(findings, "DEPTH"), [])
        self.assertEqual(kinds(findings, "ARGUMENT"), [])
        self.assertEqual(code, 0)
        _, strict = run({"ladder.lisp": LADDER, "site.lisp": source}, strict=True)
        self.assertEqual(strict, 1)


if __name__ == "__main__":
    unittest.main()
