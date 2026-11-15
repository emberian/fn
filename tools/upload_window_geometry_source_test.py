#!/usr/bin/env python3
"""Exact moves plus actual TAKE/shared resolver geometry controls."""
from pathlib import Path
import hashlib
import json
import subprocess
import tempfile
import unittest
import lisp_rewrite as lr
from upload_window_geometry_rewrite import transform
ROOT=Path(__file__).resolve().parents[1]
BASE='bf24da0bb'
class WindowGeometry(unittest.TestCase):
 def test_exact_transform_replay(self):
  names=['books/upload-scan.lisp','books/upload-kind.lisp','books/ordered.lisp']
  with tempfile.TemporaryDirectory() as td:
   root=Path(td)
   for f in names:
    p=root/f;p.parent.mkdir(parents=True,exist_ok=True)
    p.write_bytes(subprocess.check_output(['git','show',BASE+':'+f],cwd=ROOT))
   transform(root)
   for f in names+['books/upload-window-geometry.lisp','docs/design/receipts/upload-window-geometry-source.json']:
    self.assertEqual((root/f).read_bytes(),(ROOT/f).read_bytes(),f)
 def test_original_constants_unchanged_unique(self):
  receipt=json.loads((ROOT/'docs/design/receipts/upload-window-geometry-source.json').read_text())
  leaf=lr.parse(ROOT/'books/upload-window-geometry.lisp')
  for item in receipt['forms']:
   pattern='(defconst '+item['symbol']+' ?v)'
   ms=lr.match(pattern,leaf.forms);self.assertEqual(len(ms),1)
   self.assertEqual(hashlib.sha256(leaf.text[ms[0].start:ms[0].end].encode()).hexdigest(),item['sha256'])
   self.assertFalse(lr.match(pattern,lr.parse(ROOT/item['source']).forms))
 def test_actual_declarations_use_same_shared_requirements(self):
  p=lr.parse(ROOT/'books/upload-kind.lisp')
  for slot,gen,size in [('c0-slot','c0-gen','*fn2-upload-header-workspace-bytes*'),
                        ('c1-slot','c1-gen','*fn2-upload-body-window-bytes*')]:
   self.assertEqual(len(lr.match('(:chunk-window :slot '+slot+' :gen '+gen+' :class (:bytes '+size+'))',p.forms)),1)
  p=lr.parse(ROOT/'books/upload-window-geometry.lisp')
  self.assertTrue(lr.match('(defconst *fn2-upload-header-workspace-bytes* (+ *fn2-upload-header-octets* *fn2-upload-digest-octets* *fn2-overview-octets-max*))',p.forms))
if __name__=='__main__':unittest.main()
