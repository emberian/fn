"""tools/cost_obligations.py: the def-cost registry and its ratchet."""
from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from tools import cost_obligations  # noqa: E402

GENERATOR = """(in-package "ACL2")
(defconst *fn-cost-contracts*
  '((car 0 "one cell read")
    (len (binary-+ '1 (len a1)) "walks the list")))
"""


def tree(entries: list[dict], books: dict[str, str], hosts: dict[str, str]) -> Path:
    root = Path(tempfile.mkdtemp())
    (root / "planning").mkdir()
    (root / "books").mkdir()
    (root / "host").mkdir()
    (root / "planning" / "interfaces.json").write_text(json.dumps({"entries": entries}))
    (root / "books" / "def-cost.lisp").write_text(GENERATOR)
    for name, text in books.items():
        (root / "books" / name).write_text(text)
    for name, text in hosts.items():
        (root / "host" / name).write_text(text)
    return root


def entry(name: str, cls: str = "common-lisp-compliant", dispatched=("host/native/io.lisp",)) -> dict:
    return {"name": name, "class": cls, "dispatched_from": list(dispatched)}


class CostObligationsTests(unittest.TestCase):
    def test_rows_claims_and_contracts(self):
        root = tree(
            [entry("fn-a"), entry("fn-b"), entry("fn-c", "program"), entry("fn-d", "ideal"),
             entry("fn-e", dispatched=())],
            {"x.lisp": "(def-cost fn-a :visits (+ 1 n) :sizes ((n (len octets))))\n"
                       "(def-cost fn-z)\n"},
            {"cost-host.lisp": "(def-cost fn-b :visits (+ 2 n) :sizes ((n (len octets)))"
                               " :unaccounted (fn-example-step))\n"})
        doc = cost_obligations.build(root)
        rows = {r["name"]: r for r in doc["entries"]}
        self.assertEqual(set(rows), {"fn-a", "fn-b", "fn-c", "fn-d"})   # fn-e is not dispatched
        self.assertEqual(rows["fn-a"]["claim"], "proved")
        self.assertEqual(rows["fn-a"]["theorem"], "fn-a-visits-bound")
        self.assertEqual(rows["fn-a"]["sizes"], ["n"])
        self.assertEqual(rows["fn-b"]["claim"], "partial")
        self.assertEqual(rows["fn-b"]["unaccounted"], ["fn-example-step"])
        self.assertEqual(rows["fn-b"]["declared_in"], "host/cost-host.lisp")
        self.assertEqual(rows["fn-c"]["claim"], "none")
        self.assertEqual(doc["counts"], {"proved": 1, "partial": 1, "derived": 0, "none": 2})
        self.assertEqual(doc["by_class"]["program"]["none"], 1)
        self.assertEqual(doc["undispatched_declarations"], ["fn-z"])
        contracts = cost_obligations.build_contracts(root)
        self.assertEqual([c["primitive"] for c in contracts["contracts"]], ["car", "len"])
        self.assertEqual(contracts["contracts"][1]["template"], "(binary-+ (quote 1) (len a1))")
        self.assertEqual(contracts["unwitnessed"], 2)

    def test_two_declarations_of_one_name_refused(self):
        root = tree([entry("fn-a")],
                    {"x.lisp": "(def-cost fn-a)\n", "y.lisp": "(def-cost fn-a)\n"}, {})
        with self.assertRaises(ValueError):
            cost_obligations.declarations(root)

    def test_check_ratchets_by_name_against_the_base(self):
        root = tree([entry("fn-a"), entry("fn-new")],
                    {"x.lisp": "(def-cost fn-a :visits n :sizes ((n (len xs))))\n"}, {})
        doc = cost_obligations.build(root)
        cdoc = cost_obligations.build_contracts(root)
        (root / "planning" / "cost-obligations.json").write_text(cost_obligations.render(doc))
        (root / "planning" / "cost-contracts.json").write_text(cost_obligations.render(cdoc))
        # the base held fn-a proved and fn-new absent; fn-new is undeclared and unbaselined
        base = {"entries": [{"name": "fn-a", "claim": "proved", "theorem": "fn-a-visits-bound"}]}
        findings = cost_obligations.check(root, base=base, base_contracts=cdoc, baseline=set())
        self.assertTrue(any("fn-new" in f and "no def-cost" in f for f in findings), findings)
        self.assertEqual(cost_obligations.check(root, base=base, base_contracts=cdoc,
                                                baseline={"fn-new"}), [])
        # a downgrade: the base held fn-a proved, the tree now says partial
        (root / "books" / "x.lisp").write_text(
            "(def-cost fn-a :visits n :sizes ((n (len xs))) :unaccounted (fn-walk))\n")
        doc = cost_obligations.build(root)
        (root / "planning" / "cost-obligations.json").write_text(cost_obligations.render(doc))
        findings = cost_obligations.check(root, base=base, base_contracts=cdoc, baseline={"fn-new"})
        self.assertTrue(any("fell from proved to partial" in f for f in findings), findings)
        # a stale committed file
        (root / "planning" / "cost-obligations.json").write_text("{}\n")
        findings = cost_obligations.check(root, base=base, base_contracts=cdoc, baseline={"fn-new"})
        self.assertTrue(any("differs from what the tree says" in f for f in findings), findings)

    def test_contracts_are_a_reviewed_base(self):
        root = tree([entry("fn-a")], {}, {})
        cdoc = cost_obligations.build_contracts(root)
        doc = cost_obligations.build(root)
        (root / "planning" / "cost-obligations.json").write_text(cost_obligations.render(doc))
        (root / "planning" / "cost-contracts.json").write_text(cost_obligations.render(cdoc))
        base_c = {"unwitnessed": 2, "contracts": [
            {"primitive": "car", "template": "0"},
            {"primitive": "len", "template": "(len a1)"},
            {"primitive": "nth", "template": "(nfix a1)"}]}
        findings = cost_obligations.check(root, base={"entries": []}, base_contracts=base_c,
                                          baseline={"fn-a"})
        self.assertTrue(any("len changed its template" in f for f in findings), findings)
        self.assertTrue(any("nth vanished" in f for f in findings), findings)


if __name__ == "__main__":
    unittest.main()
