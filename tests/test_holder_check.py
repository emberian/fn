"""tools/holder_check.py: the holder world closed over the raw host.

On the tree: no refusal (every declared host holder's acquire/release is
called inside its :in functions, no undeclared call site, every root's
keeper exists).  On a synthetic tree: a declared :in that does not exist,
an acquire called in none of its :in functions, an undeclared call site,
and a :physical effect marked in the wrong order are each refused by name.
"""
from pathlib import Path
import tempfile
import unittest

from tools import holder_check


HOST = """\
(defun fnn-pin () (fnn-step '(:pin)))
(defun fnn-unpin (g) (fnn-step (list :unpin g)))
(defun fnn-publish () (let ((g (fnn-pin))) (fnn-cut :installed) (fnn-cut :released) (fnn-unpin g)))
(defun fnn-rogue () (let ((g (fnn-pin))) (fnn-unpin g)))
"""

BOOK_OK = """\
(def-holder fn-toy
  :shape :stamped :key "a generation"
  :holders ((publication :host t :acquire fnn-pin :release fnn-unpin :in (fnn-publish))
            (rogue :host t :acquire fnn-pin :release fnn-unpin :in (fnn-rogue))
            (ledger :root t :in (fn-ledger) :status (:repinned "a toy")))
  :effect (:physical *toy-cuts* :cut :released :after :installed))
"""

BOOK_BAD = """\
(def-holder fn-toy
  :shape :stamped :key "a generation"
  :holders ((publication :host t :acquire fnn-pin :release fnn-unpin :in (fnn-publish))
            (ghost :host t :acquire fnn-pin :release fnn-unpin :in (fnn-nowhere))
            (idle :host t :acquire fnn-stamp :release fnn-unpin :in (fnn-publish)))
  :effect (:physical *toy-cuts* :cut :installed :after :released))
"""


def _tree(book: str) -> Path:
    root = Path(tempfile.mkdtemp())
    (root / "books").mkdir()
    (root / "host" / "native").mkdir(parents=True)
    (root / "books" / "toy.lisp").write_text(book, encoding="utf-8")
    (root / "books" / "ledger.lisp").write_text("(defun fn-ledger (x) x)\n", encoding="utf-8")
    (root / "host" / "native" / "toy.lisp").write_text(HOST, encoding="utf-8")
    return root


class HolderCheck(unittest.TestCase):
    def test_tree_has_no_refusal(self):
        refusals, _notes = holder_check.check()
        self.assertEqual(refusals, [], "\n".join(refusals))

    def test_synthetic_ok(self):
        refusals, notes = holder_check.check(_tree(BOOK_OK), strict=True)
        self.assertEqual(refusals, [], "\n".join(refusals))
        self.assertTrue(any("root ledger :repinned" in n for n in notes))

    def test_synthetic_refusals(self):
        refusals, _notes = holder_check.check(_tree(BOOK_BAD), strict=True)
        text = "\n".join(refusals)
        self.assertIn(":in fnn-nowhere is no function of the raw host", text)
        self.assertIn(":acquire fnn-stamp is no function of the raw host", text)
        self.assertIn("fnn-rogue calls fnn-pin, which is declared only in", text)
        self.assertIn(":installed is marked before :released", text)


class HolderCutMap(unittest.TestCase):
    """tests/campaign/native_cuts.py verify_holder_cut_map: the declared cuts,
    the host's +fnn-holder-cuts+ and its markers agree both ways."""

    def test_tree_agrees(self):
        from tests.campaign import native_cuts
        self.assertEqual(native_cuts.verify_holder_cut_map(), [])

    def test_a_missing_host_name_or_marker_is_a_mismatch(self):
        from tests.campaign import native_cuts
        if not native_cuts.holder_cuts():
            self.skipTest("no def-holder declaration in this tree")
        host = (Path(__file__).resolve().parent.parent / native_cuts.HOLDER_CUTS_HOST).read_text()
        dropped = host.replace('"fn-pio-file-holds-released"', "", 1)
        text = "\n".join(native_cuts.verify_holder_cut_map(host_text=dropped))
        self.assertIn("declared holder cut fn-pio-file-holds-released is not in +fnn-holder-cuts+", text)
        unmarked = host.replace("(fnn-holder-cut :fn-pio-file-holds-decided)", "", 1)
        text = "\n".join(native_cuts.verify_holder_cut_map(host_text=unmarked))
        self.assertIn("is marked by no (fnn-holder-cut :fn-pio-file-holds-decided)", text)
        extra = host.replace('"fn-pio-file-holds-released"', '"fn-pio-file-holds-released" "fn-ghost-decided"', 1)
        text = "\n".join(native_cuts.verify_holder_cut_map(host_text=extra))
        self.assertIn("+fnn-holder-cuts+ names fn-ghost-decided, which no def-holder declares", text)


if __name__ == "__main__":
    unittest.main()
