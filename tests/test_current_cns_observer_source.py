"""Current ROOT metadata protocol projection, not a streamed FETCH runtime claim."""
from pathlib import Path
import json,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import cns_read_observer_rewrite as rw
BEFORE=json.loads((ROOT/'tools/fixtures/cns-current-physical-before.json').read_text())
class CurrentCns(unittest.TestCase):
 def test_exact_current_named_projection(self):
  refresh=(ROOT/'tools/cns_read_observer_refresh.lisp').read_text();mid=(ROOT/'tools/cns_read_observer_mid.lisp').read_text()
  after=rw.transform_callbacks(BEFORE['callbacks'],refresh,mid)
  kind=rw.transform_kind(BEFORE['kind'])
  self.assertEqual(after,(ROOT/'books/cns.lisp').read_text())
  self.assertEqual(kind,(ROOT/'books/cns-kind.lisp').read_text())
  self.assertEqual(rw.transform_callbacks(after,refresh,mid),after)
  self.assertEqual(rw.transform_kind(kind),kind)
 def test_actual_request_provider_uses_current_binding_predicate(self):
  s=(ROOT/'books/cns-request-observer.lisp').read_text()
  self.assertIn('(fn2-read-parent-binding-current-p x parent receipt',s)
  self.assertIn('(fn2-read-parent-bind-one x parent receipt',s)
  self.assertIn('(fn2-read-parent-clear-one x parent receipt',s)
  self.assertIn('(fn2-c-source-reader-release parent receipt',s)
  self.assertNotIn('observer-enter-children',s)
 def test_no_false_streamed_scope(self):
  # This ROOT source predates the streamed family. Its protocol API can be
  # tested now; full manifest/coverage execution requires the canonical rolling
  # source join and cannot be inferred from this projection.
  s=(ROOT/'books/cns.lisp').read_text();rootarms=rw.named(lr.parse(s).forms,'defmachine-arms','fn2-cns')
  names={rw.head(n) for n in rw.value(rootarms,':arms').items}
  self.assertNotIn(':source',names)
  self.assertIn('(fn2-cns-request-observer-events)',s)
if __name__=='__main__':unittest.main()
