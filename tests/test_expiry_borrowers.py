"""Every test class that borrows ExpiryMixin.node carries what node() reads.

CONVERGE-1 red #2 (2026-10-07): reclaim-optin (D53) made ExpiryMixin.node read
`self.reclaim_live`; five classes that borrow node() method by method, without
inheriting the mixin, never got the attribute, and page_io / over_pins failed
with AttributeError on every image.  This scans tests/ so the next attribute
node() grows cannot be missed the same way.  No image needed.
"""
import importlib
import inspect
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BORROW = re.compile(r"ExpiryMixin\.node\b")
NEEDS = ("reclaim_live",)


class ExpiryBorrowerTests(unittest.TestCase):
    def test_every_borrower_of_node_has_what_node_reads(self):
        from tests import test_native_expiry as expiry
        source = inspect.getsource(expiry.ExpiryMixin.node)
        for name in NEEDS:
            self.assertIn("self." + name, source, "node() no longer reads %s: update NEEDS" % name)
        missing = []
        for path in sorted((ROOT / "tests").glob("test_*.py")):
            if path.name in ("test_native_expiry.py", Path(__file__).name) or not BORROW.search(path.read_text(encoding="utf-8")):
                continue
            module = importlib.import_module("tests." + path.stem)
            for cname, cls in inspect.getmembers(module, inspect.isclass):
                if cls.__module__ != module.__name__ or issubclass(cls, expiry.ExpiryMixin):
                    continue
                uses = BORROW.search(inspect.getsource(cls) or "")
                if uses:
                    missing += ["%s.%s lacks %s" % (path.stem, cname, n) for n in NEEDS if not hasattr(cls, n)]
        self.assertEqual(missing, [])


if __name__ == "__main__":
    unittest.main()
