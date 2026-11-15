#!/usr/bin/env python3
"""Source controls for the exact physical-stride rewrite class, not ACL2 execution."""
from pathlib import Path
import subprocess
import unittest
import tempfile
import lisp_rewrite as lr
from upload_physical_stride_rewrite import RULES, transform
from upload_payload_group_rewrite import transform as payload_group
ROOT=Path(__file__).resolve().parents[1]
def paired_consumer(text,name,reverse=False):
 # Replay the reviewed minimal consumer donor, not a replacement baseline.
 patch=subprocess.check_output(['git','diff','0506c97c96^','0506c97c96','--',name],cwd=ROOT)
 if not patch:return text
 with tempfile.TemporaryDirectory(prefix='fn-paired-consumer-') as directory:
  root=Path(directory);target=root/name;target.parent.mkdir(parents=True);target.write_text(text)
  args=['git','apply','--whitespace=nowarn']+(['--reverse'] if reverse else [])+['-']
  subprocess.run(args,cwd=root,input=patch,check=True,capture_output=True)
  return target.read_text()
class PhysicalStride(unittest.TestCase):
 def test_exact_authorized_transform(self):
  for name,rules in RULES.items():
   original=subprocess.check_output(['git','show',f'fe9f761ab:{name}'],cwd=ROOT,text=True)
   expected=transform(original,rules)
   # Separate raw-threshold semantic commit updates only this operation doc.
   expected=expected.replace('Whether stored octets of a length are longer than one extent (named through a manifest).',
                             'Whether stored octets exceed the raw commitment span (named through a manifest).')
   paired=paired_consumer(expected,name)
   self.assertEqual(paired_consumer(paired,name,reverse=True),expected)
   expected=paired
   if name=='books/assembly-callbacks-d-upload.lisp':
    # Explicit second semantic change, with an inverse receipt to the old
    # three-block grouping. Do not silently rebaseline the physical rewrite.
    grouped=payload_group(expected)
    self.assertEqual(payload_group(grouped, reverse=True),expected)
    expected=grouped
   self.assertEqual(expected,(ROOT/name).read_text(),name)
 def test_payload_grouping_uses_physical_extent(self):
  p=lr.parse(ROOT/'books/assembly-callbacks-d-upload.lisp')
  self.assertEqual(len(lr.match('(mod blk *fn2-commit-write-resources*)',p.forms)),0)
  self.assertEqual(len(lr.match('(mod blk *fn2-storage-extent-units*)',p.forms)),3)
  self.assertEqual(len(lr.match('(* *fn2-storage-extent-units* row-cext)',p.forms)),1)
  self.assertEqual(len(lr.match('(* *fn2-commit-extent-bytes* row-cext)',p.forms)),1)
 def test_group_transform_rejects_missing_site(self):
  source=(ROOT/'books/assembly-callbacks-d-upload.lisp').read_text()
  with self.assertRaises(ValueError):
   payload_group(source.replace('(mod blk *fn2-storage-extent-units*)','0',1),reverse=True)
 def test_actual_control_entrypoints(self):
  p=lr.parse(ROOT/'tests/upload-manifest-physical-unit.lisp')
  for name in ['fn2-upload-payload-reserve','fn2-upload-block-entry','fn2-am-get-entry',
               'fn2-upload-manifest-extents','fn2-rp-entries','fn2-recovery-claim-article']:
   self.assertTrue(lr.match('('+name+' ?*args)',p.forms),name)
 def test_manifest_threshold_forms_unchanged(self):
  old=subprocess.check_output(['git','show','0943d496f:books/article-manifest.lisp'],cwd=ROOT,text=True)
  current=(ROOT/'books/article-manifest.lisp').read_text()
  self.assertEqual([lr.emit(f,drop_comments=True) for f in lr.parse(old).forms],
                   [lr.emit(f,drop_comments=True) for f in lr.parse(current).forms])
 def test_real_sixteenth_seventeenth_producer_control(self):
  p=lr.parse(ROOT/'tests/upload-group16-served-unit.lisp')
  for name in ['fn2-turn','fn2-cw-adapter-one','fn2-format-source-manifest-header-decode',
               'fn2-am-get-entry','fn2-alloc-handle-code','fn2-up16-extents-p']:
   self.assertTrue(lr.match('('+name+' ?*args)',p.forms),name)
  for name in ['fn2-upload-block-entry','fn2-upload-payload-reserve','fn2-extents-set-state','fn2-upload-put-core']:
   self.assertFalse(lr.match('('+name+' ?*args)',p.forms),name)
if __name__=='__main__': unittest.main()
