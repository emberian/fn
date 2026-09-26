"""Static wiring and cost-scope checks for the native served read path.

These checks are not timing evidence.  ACL2 proves correspondence and
preservation; this file keeps the production call on that proved entry and
keeps the entry predicate free of retained-buffer recognizers.
"""
from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[1]


def definition(source: str, name: str) -> str:
    start = source.index(f"(defun {name} ")
    next_form = source.find("\n(defun ", start + 1)
    next_theorem = source.find("\n(defthm ", start + 1)
    ends = [value for value in (next_form, next_theorem) if value >= 0]
    return source[start:min(ends) if ends else len(source)]


class NativeServedCostTests(unittest.TestCase):
    def test_owner_calls_fast_span_entry(self) -> None:
        # The native read path is the span over the octet buffer (REP-012):
        # the host fills the buffer and calls fn-owner-chunk-span, which
        # calls fn-scar-ocfg-read-span, whose fold checks only the fast
        # predicate; no list of the read's octets is built on the way.
        native = (ROOT / "host/native/owner.lisp").read_text()
        host = (ROOT / "host/owner-host.lisp").read_text()
        span = (ROOT / "books/served-span.lisp").read_text()
        handoff = definition(native, "fnn-owner-handle-chunk")
        self.assertIn("(fnn-octets-fill incoming)", handoff)
        self.assertIn("(fnn-owner-buffer-action 'fn-owner-chunk-span cid", handoff)
        self.assertNotIn("fnn-octet-list incoming", handoff)
        self.assertNotIn("'fn-owner-chunk cid", handoff)
        self.assertIn("(fn-scar-ocfg-read-span", definition(host, "fn-owner-chunk-span"))
        self.assertIn("(fn-scar-step-span-fast", definition(span, "fn-scar-own-read-span"))
        fast = definition(span, "fn-scar-step-span-fast")
        self.assertIn("fn-wire-fast-statep", fast)
        self.assertNotIn("fn-wire-statep", fast)

    def test_span_fold_reads_the_buffer_by_index(self) -> None:
        # The served span fold reads each octet of the range from the buffer
        # by index (fn-octets-get); the list of the range's octets
        # (fn-oct-slice-list) is the logical model in the theorems only.
        # The per-line index scan (no wire state inside a line) is PKT-479
        # and has no static check until it lands.
        span = (ROOT / "books/served-span.lisp").read_text()
        fold = definition(span, "fn-scar-feed-span")
        self.assertIn("(fn-octets-get i fn-octets)", fold)
        self.assertNotIn("fn-oct-slice-list", fold)
        self.assertNotIn("fn-octets-list", fold)

    def test_fast_predicate_has_fixed_spine_and_scalar_scope(self) -> None:
        wire = (ROOT / "books/wire.lisp").read_text()
        body = definition(wire, "fn-wire-fast-statep")
        self.assertIn("fn-wire-state-shapep", body)
        self.assertNotRegex(body, re.compile(r"octet-listp|octet-linesp|lines-size|\(len "))
        # Static source count: one fixed-spine check and twelve scalar selector
        # applications.  This is the predicate's ACL2 expression count, not a
        # host instruction, allocation, elapsed-time, or whole-read estimate.
        self.assertEqual(
            len(re.findall(r"\(fn-wire-state-[a-z-]+ x\)", body)), 12
        )

    def test_fast_entry_never_calls_full_recognizer(self) -> None:
        served = (ROOT / "books/served-tls-prefix.lisp").read_text()
        body = definition(served, "fn-served-step-counted-fast")
        self.assertIn("fn-wire-fast-statep", body)
        self.assertNotIn("fn-wire-statep", body)


if __name__ == "__main__":
    unittest.main()
