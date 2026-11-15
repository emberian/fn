from pathlib import Path
import json,unittest
from rewrite_checkpoint_cbase_release_rows import rewrite
class ReleaseRows(unittest.TestCase):
 def test_exact_and_idempotent(self):
  f=json.loads((Path(__file__).parent/'fixtures/checkpoint_cbase_release_rows.json').read_text())
  self.assertEqual(rewrite(f['before']),f['after']);self.assertEqual(rewrite(f['after']),f['after'])
 def test_active_alias_and_private_row(self):
  f=json.loads((Path(__file__).parent/'fixtures/checkpoint_cbase_release_rows.json').read_text());s=f['after']
  self.assertIn('(fn2-checkpoint-cbase-row-release-step budget 0 ',s)
  self.assertIn('(fn2-checkpoint-summary-row-retire-row s r ',s)
  self.assertIn('(fn2-checkpoint-summary-lease-count s fn2-checkpoint-summary)',s)
  self.assertIn('(fn2-checkpoint-summary-row-retire-begin s ',s)
if __name__=='__main__':unittest.main()
