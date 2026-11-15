#!/usr/bin/env python3
import json,subprocess,sys,tempfile,unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
class ClosureProjection(unittest.TestCase):
    def test_exact_projection_and_idempotence(self):
        fixture=json.loads((ROOT/'tools/fixtures/checkpoint_bank_closure_projection.json').read_text())
        with tempfile.TemporaryDirectory(prefix='fn-bank-closure-') as tmp:
            p=Path(tmp)/'books/checkpoint-bank-cold.lisp';p.parent.mkdir();p.write_text(fixture['old'])
            command=[sys.executable,str(ROOT/'tools/rewrite_checkpoint_bank_closure.py')]
            subprocess.run(command,cwd=tmp,check=True,capture_output=True,text=True)
            self.assertEqual(p.read_text(),fixture['new'])
            subprocess.run(command,cwd=tmp,check=True,capture_output=True,text=True)
            self.assertEqual(p.read_text(),fixture['new'])
if __name__=='__main__':unittest.main()
