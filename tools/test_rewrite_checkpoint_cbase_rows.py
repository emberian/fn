from pathlib import Path
import json,unittest
from rewrite_checkpoint_cbase_rows import rewrite
class Rows(unittest.TestCase):
 def test_exact_projection(self):
  f=json.loads((Path(__file__).parent/'fixtures/checkpoint_cbase_rows.json').read_text())
  self.assertEqual(rewrite(f['before']),f['after'])
  self.assertEqual(rewrite(f['after']),f['after'])
 def test_canonical_words_and_no_row_alias(self):
  f=json.loads((Path(__file__).parent/'fixtures/checkpoint_cbase_rows.json').read_text())
  s=rewrite(f['before'])
  self.assertIn('(fn2-checkpoint-summary-descriptor-word r i fn2-checkpoint-summary)',s)
  self.assertIn('(fn2-checkpoint-cbase-row-hash-p 0 r c ',s)
  self.assertIn('(fn2-checkpoint-summary-candidate r fn2-checkpoint-summary)',s)
  self.assertIn('(fn2-checkpoint-cbase-row-held-p 0 ',s)
if __name__=='__main__':unittest.main()
