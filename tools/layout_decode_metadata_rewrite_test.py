"""Metadata projection preserves authoritative baseline decoder/encoder semantics."""
from pathlib import Path
import hashlib,unittest
import lisp_rewrite as lr
import layout_decode_metadata_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]
def read(p):return (ROOT/p).read_text()
def form(s,p):
 n=lr.match(p,lr.parse(s).forms)[0].node
 return s[n.start:n.end]
class Metadata(unittest.TestCase):
 def test_authoritative_baseline_and_runtime_exact_preservation(self):
  before=read('tools/fixtures/layout-full-decode-before.lisp')
  self.assertEqual(hashlib.sha256(before.encode()).hexdigest(),'2060684efd33bb23e0c426275edc9a3dc6c47b50ceda0b80207c84ec7fd89d48')
  after=rw.rewrite(before);self.assertEqual(rw.rewrite(after),after)
  for name in ['fn2-layout-decode-run','fn2-layout-decode-step','fn2-layout-decode','fn2-layout-encode','fn2-codec-spec-events','fn2-layout-scan','fn2-layout-emit']:
   p='(defun '+name+' ?*body)';self.assertEqual(form(before,p),form(after,p),name)
  self.assertIn('(,step base slot gen off end okind oslot ogen 4096 fn2-fields fn2-pool)',after)
  for text in ['(in-theory (disable fn2-layoutp-head))','(local (in-theory *fn2-codec-proof-runes*))']:
   self.assertEqual(before.count(text),after.count(text))
 def test_shared_provider_is_identical_to_quarantined_work_declaration(self):
  after=rw.rewrite(read('tools/fixtures/layout-full-decode-before.lisp'));full=read('books/layout.lisp')
  for p in ['(defun fn2-layout-decode-transition-bound ?*body)','(defthm fn2-layout-decode-transition-bound-positive ?*body)']:
   self.assertEqual(form(after,p),form(full,p))
  self.assertIn(':decode-transitions ,transitions-name',after)
if __name__=='__main__':unittest.main()
