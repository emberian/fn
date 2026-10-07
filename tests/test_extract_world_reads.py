"""X3: the extracted closure holds no book function that reads the world.

Book-build helpers (def-carried's fn-cd-*, definterface's fn-di-*, defteeth's
fn-dt-*/fn-dk-*) read the ACL2 world (fgetprop, table-alist,
congruent-stobj-rep) and have no meaning in the bare core, which holds only
the snapshot's rows.  The only world-reading book function the host install
path applies is fn-rdv-row-digest, over rows carried with their digests
(books/raw-dispatch-verdict.lisp).  Measured on the extraction IR of
2026-10-06 (core.json, 14028 functions): the 38 world readers outside predefined
ACL2 functions were all reached through the host word FN-DI-RAW-WITH-PROBLEM,
which D40's verdict install path removed.  This pins the host words.
"""
import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUILD_TIME = re.compile(r"\((fn-(?:di|cd|cw|cdv|dt|dk)-[a-z0-9$*-]+)")


class HostWorldReadTests(unittest.TestCase):
    def test_host_native_applies_no_build_time_world_reader(self):
        found = {}
        for path in sorted((ROOT / "host/native").glob("*.lisp")):
            for line in path.read_text().splitlines():
                code = line.split(";", 1)[0]
                for name in BUILD_TIME.findall(code):
                    found.setdefault(name, set()).add(path.name)
        self.assertEqual(found, {})

    def test_the_guard_sees_one(self):
        self.assertTrue(BUILD_TIME.search("(fn-di-raw-with-problem name kvs w)"))


if __name__ == "__main__":
    unittest.main()
