from pathlib import Path
import json,unittest
from rewrite_successor_bind_consumption import rewrite_assembly,rewrite_bind
class Consumption(unittest.TestCase):
 def test_exact_idempotent(self):
  f=json.loads((Path(__file__).parent/'fixtures/successor_bind_consumption.json').read_text())
  for p,fn in [('books/runs-assemble.lisp',rewrite_assembly),('books/machines-c-bind.lisp',rewrite_bind)]:
   self.assertEqual(fn(f['before'][p]),f['after'][p]);self.assertEqual(fn(f['after'][p]),f['after'][p])
 def test_boundaries_derive_from_actual_dispatcher(self):
  f=json.loads((Path(__file__).parent/'fixtures/successor_bind_consumption.json').read_text())
  self.assertIn('(fn2-run-layout-max-size (fn2-overlays-schema o fn2-overlays) 0)',f['after']['books/runs-assemble.lisp'])
  self.assertIn('(fn2-run-layout-value-ok sid j len)',f['after']['books/machines-c-bind.lisp'])
if __name__=='__main__':unittest.main()
