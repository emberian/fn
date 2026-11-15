#!/usr/bin/env python3
"""Source controls for the exact physical-stride rewrite class, not ACL2 execution."""
from pathlib import Path
import subprocess
import unittest
import lisp_rewrite as lr
from upload_physical_stride_rewrite import RULES, transform
ROOT=Path(__file__).resolve().parents[1]
class PhysicalStride(unittest.TestCase):
 def test_exact_authorized_transform(self):
  for name,rules in RULES.items():
   original=subprocess.check_output(['git','show',f'fe9f761ab:{name}'],cwd=ROOT,text=True)
   expected=transform(original,rules)
   # Separate raw-threshold semantic commit updates only this operation doc.
   expected=expected.replace('Whether stored octets of a length are longer than one extent (named through a manifest).',
                             'Whether stored octets exceed the raw commitment span (named through a manifest).')
   self.assertEqual(expected,(ROOT/name).read_text(),name)
 def test_resource_grouping_unchanged(self):
  p=lr.parse(ROOT/'books/assembly-callbacks-d-upload.lisp')
  self.assertEqual(len(lr.match('(mod blk *fn2-commit-write-resources*)',p.forms)),3)
  self.assertEqual(len(lr.match('(* *fn2-storage-extent-units* row-cext)',p.forms)),1)
  self.assertEqual(len(lr.match('(* *fn2-commit-extent-bytes* row-cext)',p.forms)),1)
 def test_actual_control_entrypoints(self):
  p=lr.parse(ROOT/'tests/upload-manifest-physical-unit.lisp')
  for name in ['fn2-upload-payload-reserve','fn2-upload-block-entry','fn2-am-get-entry',
               'fn2-upload-manifest-extents','fn2-rp-entries','fn2-recovery-claim-article']:
   self.assertTrue(lr.match('('+name+' ?*args)',p.forms),name)
if __name__=='__main__': unittest.main()
