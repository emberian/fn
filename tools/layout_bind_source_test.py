#!/usr/bin/env python3
"""Generator boundary controls; actual macro/unit assertions are unrun."""
from pathlib import Path
import unittest
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
S=(ROOT/'books/layout-bind.lisp').read_text()
def fn(name):return lr.match('(defun '+name+' ?*body)',lr.parse(S).forms,deep=False)[0].node
def calls(n,name):return lr.match('('+name+' ?*args)',[n])
class LayoutBind(unittest.TestCase):
 def test_binder_uses_actual_layout_registry_and_refuses_missing_declaration(self):
  n=lr.match('(defmacro deflayout-binder ?*body)',lr.parse(S).forms,deep=False)[0].node
  s=S[n.start:n.end]
  self.assertIn("(table-alist 'fn2-layouts (w state))",s)
  self.assertIn('(fn2-layoutp layout)',s)
  self.assertIn("(er soft 'deflayout-binder",s)
 def test_fields_and_offsets_derive_from_the_existing_layout(self):
  n=fn('fn2-layout-bind-bindings')
  self.assertTrue(calls(n,'fn2-codec-field'))
  self.assertTrue(calls(n,'fn2-layout-bind-bindings'))
  self.assertFalse(calls(n,'fn2-pool-write'))
  self.assertFalse(calls(n,'fn2-pool-read'))
  self.assertTrue(calls(n,'fn2-fields-put'))
  self.assertTrue(calls(n,'fn2-fields-set-value'))
 def test_generated_function_has_real_guard_and_direct_output_frames(self):
  n=fn('fn2-layout-bind-events')
  s=S[n.start:n.end]
  self.assertIn('(fn2-fields-wfp fn2-fields)',s)
  self.assertIn('(fn2-fields-rows fn2-fields)',s)
  self.assertIn('(fn2-layout-bind-guards layout)',s)
  self.assertIn(':position nil :raw-rows t',s)
 def test_archive_header_uses_generic_binder_and_still_existing_codec(self):
  s=(ROOT/'books/event-archive-format.lisp').read_text()
  self.assertIn('(deflayout-binder fn2-event-archive-header-bind fn2-event-archive-header)',s)
  self.assertIn('(deflayout fn2-event-archive-header',s)
  self.assertNotIn('fn2-pool-write',s)
if __name__=='__main__':unittest.main()
