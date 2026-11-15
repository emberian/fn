from pathlib import Path
import json,unittest
from rewrite_successor_slot_prepare import rewrite
from lisp_rewrite import parse,match
ROOT=Path(__file__).resolve().parents[1]
class SlotPrepare(unittest.TestCase):
 def test_exact_and_idempotent(self):
  f=json.loads((ROOT/'tools/fixtures/successor_slot_prepare.json').read_text())
  self.assertEqual(rewrite(f['before']),f['after']);self.assertEqual(rewrite(f['after']),f['after'])
 def test_one_actual_preparation_body(self):
  f=json.loads((ROOT/'tools/fixtures/successor_slot_prepare.json').read_text());p=parse(ROOT/'books/machines-c-bind.lisp');q=parse(f['after'])
  for name in ['fn2-succ-bind-slot','fn2-succ-bind-slot-prepare']:
   a=match(None,p.forms,deep=False,head='defun',name=name)[0];b=match(None,q.forms,deep=False,head='defun',name=name)[0]
   self.assertEqual(p.text[a.start:a.end],q.text[b.start:b.end])
if __name__=='__main__':unittest.main()
