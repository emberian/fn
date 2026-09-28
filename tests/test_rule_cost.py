"""tools/rule_cost.py: the listing parser and the exported-rule ranking."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import rule_cost  # noqa: E402

# The shape ACL2 8.7 prints for (show-accumulated-persistence :frames),
# measured on persvati 2026-09-28.
LOG = """FN-RULE-COST-BOOK books/b
Prover steps counted:  65
Prover steps counted:  35
FN-RULE-COST-SECTION frames
Accumulated Persistence (727 :tries useful, 249 :tries not useful)

   :frames   :tries    :ratio  rune
   --------------------------------
       604      604 (    1.00) (:TYPE-PRESCRIPTION FN-A-IS-CONSP)
       490      490    [useful]
       114      114    [useless]
   --------------------------------
       381       35 (   10.88) (:REWRITE FN-A-TRUE-LISTP . 2)
         0        0    [useful]
       381       35    [useless]
   --------------------------------
       117       90 (    1.30) (:REWRITE DEFAULT-CDR)
         0        0    [useful]
       117       90    [useless]
   --------------------------------
        50       50 (    1.00) (:DEFINITION FN-B-OWN)
        50       50    [useful]
         0        0    [useless]
   --------------------------------
FN-RULE-COST-WALL books/b 7
"""


class RuleCostTest(unittest.TestCase):
    def test_parse_log_splits_useful_and_useless(self):
        parsed = rule_cost.parse_log(LOG)
        self.assertEqual(parsed["book"], "books/b")
        self.assertEqual(parsed["wall"], 7)
        self.assertEqual(parsed["steps"], 100)
        self.assertTrue(parsed["complete"])
        self.assertEqual(parsed["runes"]["(:REWRITE FN-A-TRUE-LISTP . 2)"],
                         {"frames": 381, "tries": 35, "useful": 0, "useless": 381})
        self.assertEqual(parsed["runes"]["(:TYPE-PRESCRIPTION FN-A-IS-CONSP)"]["useful"], 490)

    def test_rank_counts_only_rules_another_fn_book_defines(self):
        owner = {"fn-a-is-consp": "books/a", "fn-a-true-listp": "books/a",
                 "fn-b-own": "books/b"}
        with tempfile.TemporaryDirectory() as scratch:
            log = Path(scratch) / "b.log"
            log.write_text(LOG, encoding="utf-8")
            result = rule_cost.rank([log], owner)
        runes = [row["rune"] for row in result["runes"]]
        # DEFAULT-CDR is ACL2's, FN-B-OWN is the profiled book's own.
        self.assertEqual(runes, ["(:REWRITE FN-A-TRUE-LISTP . 2)",
                                 "(:TYPE-PRESCRIPTION FN-A-IS-CONSP)"])
        self.assertEqual(result["runes"][0]["books_useful"], 0)
        self.assertEqual(result["runes"][1]["useful_in"], ["books/b"])
        self.assertEqual(result["books"]["books/b"]["exported_useless"], 495)


if __name__ == "__main__":
    unittest.main()
