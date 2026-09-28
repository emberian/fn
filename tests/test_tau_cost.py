"""tools/tau_cost.py: the tau-off source, the enable pairs, the log parser."""

from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import tau_cost  # noqa: E402

BOOK = """; A book.
(in-package "ACL2")

(include-book "a")
(local (include-book "b"))

(defun f (x) (declare (xargs :guard t)) x)

(encapsulate ()
  (defthm g (equal (f x) x)))
"""


def log(book, variant, runtime, summaries, errors=(), wall=3, code=0):
    body = [f"FN-TAU-COST-BOOK {book} {variant}"]
    for kind, name, seconds, steps in summaries:
        body += ["", "Summary", f"Form:  ( {kind} {name} ...)",
                 f"Time:  {seconds:.2f} seconds (prove: 0.00, print: 0.00, other: 0.00)"]
        if steps is not None:
            body.append(f"Prover steps counted:  {steps}")
    body += list(errors)
    body += ["; (EV-REC *RETURN-LAST-ARG3* ...) took ",
             f"; {runtime + 0.1:.2f} seconds realtime, {runtime:.2f} seconds runtime",
             f"FN-TAU-COST-WALL {book} {variant} {wall} {code} 1.0/1.2"]
    return "\n".join(body) + "\n"


class TauCostTests(unittest.TestCase):
    def test_tau_off_goes_after_the_header_includes_once(self):
        text = tau_cost.tau_off(BOOK)
        self.assertLess(text.index('(include-book "b")'),
                        text.index("(disable (tau-system))"))
        self.assertLess(text.index("(disable (tau-system))"), text.index("(defun f"))
        self.assertEqual(tau_cost.tau_off(text), text)

    def test_enable_around_wraps_the_top_level_form_that_defines_a_name(self):
        text, found = tau_cost.enable_around(tau_cost.tau_off(BOOK), {"g", "absent"})
        self.assertEqual(found, {"g"})
        start = text.index(tau_cost.ON_OPEN)
        self.assertLess(start, text.index("(encapsulate"))
        self.assertLess(text.index("(defthm g"), text.index(tau_cost.ON_CLOSE, start))
        # Idempotent: a wrapped form is not wrapped again.
        again, _ = tau_cost.enable_around(text, {"g"})
        self.assertEqual(again, text)

    def test_rank_pairs_variants_and_separates_cascades(self):
        on = log("books/x", "on", 4.0, [("DEFUN", "F", 0.5, 10), ("DEFTHM", "G", 2.0, 99)])
        off = log("books/x", "off", 1.5, [("DEFUN", "F", 1.2, 10), ("DEFTHM", "G", 0.1, 99)],
                  errors=["ACL2 Error in ( DEFUN F ...):  guard failed.",
                          "ACL2 Error [Failure] in ( DEFUN F ...):  See :DOC failure.",
                          "ACL2 Error [Translate] in ( DEFTHM G ...):  undefined.",
                          "ACL2 Error [Failure] in ( DEFTHEORY T ...):  x."])
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "x.on.log").write_text(on)
            (root / "x.off.log").write_text(off)
            result = tau_cost.rank([root / "x.on.log", root / "x.off.log"], 0.5)
        row = result["books"][0]
        self.assertEqual((row["saved"], row["fraction"]), (2.5, 0.625))
        self.assertEqual(row["failing"], ["defun f"])
        self.assertEqual(row["cascaded"], ["deftheory t", "defthm g"])
        self.assertEqual(row["slower"], [["defun f", 0.5, 1.2]])
        self.assertEqual(len(tau_cost.selected(result, 1.0, 0.2)), 1)
        self.assertEqual(tau_cost.selected(result, 3.0, 0.7), [])


if __name__ == "__main__":
    unittest.main()
