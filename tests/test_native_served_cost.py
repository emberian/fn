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
    def test_owner_reads_the_span_over_the_buffer(self) -> None:
        # The native read path is the span over the octet buffer (REP-012):
        # the host fills the buffer and calls fn-owner-chunk-span with the
        # live arena and catalog; no list of the read's octets is built on
        # the host's side.
        native = (ROOT / "host/native/owner.lisp").read_text()
        host = (ROOT / "host/owner-host.lisp").read_text()
        # Since scheduler-3 (1b3160bce) fnn-owner-handle-chunk runs the read
        # through fnn-owner-handle-chunk-read and the XREDEEM publication in
        # its own quantum; the fill and the span call are the read's.
        self.assertIn("(fnn-owner-handle-chunk-read service cid incoming socket class peerp)",
                      definition(native, "fnn-owner-handle-chunk"))
        handoff = definition(native, "fnn-owner-handle-chunk-read")
        self.assertIn("(fnn-owner-read-buffer-fill service incoming)", handoff)
        self.assertIn("(fnn-octets-fill incoming)", definition(native, "fnn-owner-read-buffer-fill"))
        # Since composed-owner (Row A4 (c)) the read goes through
        # fnn-owner-chunk-span-no-io: the same span call with the extent
        # reader's disk I/O refused (a cold page is read off the mutex).
        self.assertIn("(fnn-owner-chunk-span-no-io\n                    cid incoming sched", handoff)
        self.assertIn("(fnn-core-buffer-state 'fn-owner-chunk-span cid",
                      definition(native, "fnn-owner-chunk-span-no-io"))
        self.assertNotIn("fnn-octet-list incoming", handoff)
        self.assertNotIn("'fn-owner-chunk cid", handoff)
        # fn-owner-chunk-span reads at the reader view through
        # fn-owner-chunk-span-at -> fn-owner-chunk-span-evaluate, which now
        # calls fn-asto-mca-read-span (an ARTICLE capture, else the
        # available-metadata read, fn-av-mca-read-span,
        # books/served-available-read.lisp).  That route does not reach
        # the credit chain this test used to follow (fn-mca-read-span ->
        # fn-oas- -> fn-otm- -> fn-orr- -> fn-scr-ocfg-read-span ->
        # fn-scr-step-span-fast), so the fast-predicate, list-free span is
        # not shown for the host's read any more: its refinement is owed
        # (PRF-1287 and the evaluate's own comment, "selective owner
        # refinement/guards are owed").  The claim is not made here.
        evaluate = definition(host, "fn-owner-chunk-span-evaluate")
        self.assertIn("(fn-asto-mca-read-span", evaluate)
        self.assertIn("(fn-av-mca-read-span credits oc views id start stop cache sched",
                      definition(host, "fn-asto-mca-read-span"))
        self.assertIn("(fn-owner-chunk-span-evaluate id start end sched",
                      definition(host, "fn-owner-chunk-span-current-result"))
        self.assertIn("(fn-owner-chunk-span-current-result id start end sched",
                      definition(host, "fn-owner-chunk-span-at"))

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
