"""Internal archive schemas cannot enter native or cold semantic root1."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
class Domain(unittest.TestCase):
 def test_native_selection_refuses_internal_before_candidate_mutation(self):
  s=(ROOT/'books/checkpoint-metadata-source.lisp').read_text()
  n=lr.match('(defun fn2-checkpoint-source-consider ?*body)',lr.parse(s).forms,deep=False)[0].node
  body=n.items[-1]
  self.assertEqual(body.items[0].low,'if')
  expected=lr.parse('(not (fn2-run-layout-internal-p schema))').forms[0]
  def tree(n):return n.low if hasattr(n,'low') else tuple(tree(x) for x in n.items)
  self.assertEqual(tree(body.items[1].items[1]),tree(expected))
 def test_cold_manifest_refuses_internal_before_child_enqueue(self):
  s=(ROOT/'books/checkpoint-restore-semantic-work.lisp').read_text()
  gates=lr.match('(unless (and (posp height) (<= height *fn2-run-max-levels*) (posp (fn2-run-layout-fields schema 0)) (not (fn2-run-layout-internal-p schema))))',lr.parse(s).forms)
  self.assertEqual(len(gates),1)
  self.assertNotIn('(<= schema 19)',s)
if __name__=='__main__':unittest.main()
