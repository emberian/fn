from pathlib import Path
import json,unittest
from rewrite_checkpoint_cbase_start import rewrite
class Start(unittest.TestCase):
 def test_exact_shared_extraction(self):
  f=json.loads((Path(__file__).parent/'fixtures/checkpoint_cbase_start.json').read_text())
  out,helper=rewrite(f['before'])
  out=out.replace('(include-book "checkpoint-cbase-identity")','(include-book "checkpoint-cbase-start")')
  self.assertEqual((out,helper),(f['after'],f['helper']))
  self.assertEqual(rewrite(out),(out,None))
 def test_all_hashes_use_canonical_row(self):
  f=json.loads((Path(__file__).parent/'fixtures/checkpoint_cbase_start.json').read_text())
  for i in range(8):self.assertIn(f'(hash-{i} (fn2-checkpoint-summary-descriptor-word r {i} fn2-checkpoint-summary))',f['helper'])
if __name__=='__main__':unittest.main()
