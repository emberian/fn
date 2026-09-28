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
        # The native read path is the span over the octet buffer (REP-012)
        # and, since the catalog slice's step 8, the catalog: the host fills
        # the buffer and calls fn-owner-chunk-span with the live arena and
        # catalog, which calls fn-scr-ocfg-read-span
        # (books/served-catalog-chain.lisp, equal to fn-scar-ocfg-read-span
        # under the catalog relation), whose fold checks only the fast
        # predicate; no list of the read's octets is built on the way.
        native = (ROOT / "host/native/owner.lisp").read_text()
        host = (ROOT / "host/owner-host.lisp").read_text()
        chain = (ROOT / "books/served-catalog-chain.lisp").read_text()
        # Since scheduler-3 (1b3160bce) fnn-owner-handle-chunk runs the read
        # through fnn-owner-handle-chunk-read and the XREDEEM publication in
        # its own quantum; the fill and the span call are the read's.
        self.assertIn("(fnn-owner-handle-chunk-read service cid incoming socket class peerp)",
                      definition(native, "fnn-owner-handle-chunk"))
        handoff = definition(native, "fnn-owner-handle-chunk-read")
        self.assertIn("(fnn-octets-fill incoming)", handoff)
        self.assertIn("(fnn-core-buffer-state 'fn-owner-chunk-span cid", handoff)
        self.assertNotIn("fnn-octet-list incoming", handoff)
        self.assertNotIn("'fn-owner-chunk cid", handoff)
        # fn-owner-chunk-span reads at the reader view (fn-owner-at-reader-view)
        # through fn-owner-chunk-span-at, which calls the catalog chain.
        self.assertIn("(fn-owner-chunk-span-at", definition(host, "fn-owner-chunk-span"))
        # Since scheduler-3 (PKT-828) through fn-orr-read-span
        # (books/owner-reader-read.lisp), which calls fn-scr-ocfg-read-span
        # on both arms: at the captured reader view and, with none, directly.
        # Since time-model-2 (PRF-323) the host calls fn-otm-read-span
        # (books/owner-time-admission.lisp), which is fn-orr-read-span on
        # both arms: admitted as is, shedding with the posting bit off.
        self.assertIn("(fn-otm-read-span", definition(host, "fn-owner-chunk-span-at"))
        admission = definition((ROOT / "books/owner-time-admission.lisp").read_text(),
                               "fn-otm-read-span")
        self.assertEqual(admission.count("(fn-orr-read-span"), 2)
        reader = definition((ROOT / "books/owner-reader-read.lisp").read_text(),
                            "fn-orr-read-span")
        self.assertEqual(reader.count("(fn-scr-ocfg-read-span"), 2)
        self.assertIn("(fn-scr-step-span-fast", definition(chain, "fn-scr-own-read-span"))
        fast = definition(chain, "fn-scr-step-span-fast")
        self.assertIn("fn-wire-fast-statep", fast)
        self.assertNotIn("fn-wire-statep", fast)

    def test_span_fold_reads_the_buffer_by_index(self) -> None:
        # The served span fold reads each octet of the range from the buffer
        # by index (fn-octets-get); the list of the range's octets
        # (fn-oct-slice-list) is the logical model in the theorems only.
        # PKT-479: the fold is the LOGIC of the host-called core; it is
        # executed by the catalog chain's scan, one framed event at a time
        # (fn-scr-scan-span, KEYSTONE fn-scr-scan-span-is-feed-span).
        span = (ROOT / "books/served-catalog-chain.lisp").read_text()
        fold = definition(span, "fn-scr-feed-span")
        self.assertIn("(fn-octets-get i fn-octets)", fold)
        self.assertNotIn("fn-oct-slice-list", fold)
        self.assertNotIn("fn-octets-list", fold)
        core = definition(span, "fn-scr-step-span-core")
        self.assertRegex(core, re.compile(
            r"\(mbe :logic \(fn-scr-feed-span conn i end [^)]*\)\s+"
            r":exec \(fn-scr-scan-span conn i end [^)]*\)\)"))
        self.assertIn("(fn-wire-scan (fn-served-conn-wire conn) i end fn-octets)",
                      definition(span, "fn-scr-scan-span"))
        # The carried chain (the reference the catalog chain is equated to)
        # keeps its own scan.
        carried = definition((ROOT / "books/served-span.lisp").read_text(),
                             "fn-scar-step-span-core")
        self.assertRegex(carried, re.compile(
            r"\(mbe :logic \(fn-scar-feed-span conn i end [^)]*\)\s+"
            r":exec \(fn-scar-scan-span conn i end [^)]*\)\)"))
        scan = (ROOT / "books/wire-scan.lisp").read_text()
        plain = definition(scan, "fn-wscan-plain-end")
        self.assertIn("fn-octets-get", plain)
        self.assertNotRegex(plain, re.compile(r"\(cons |fn-oct-slice-list|fn-octets-list"))

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
