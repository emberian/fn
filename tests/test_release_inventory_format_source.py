"""Source controls for the shared authenticated inventory wire seam only."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk
import rewrite_release_inventory_frontier as frontier

def definition(text,name):
    return next(n for raw in forms(text) for n in walk(read_sexp(raw)) if n[:2]==['defun',name])
def linked_contract(text):
    f=definition(text,'fn2-checkpoint-linked-header-pack');calls=list(walk(f))
    return all(x in calls for x in [
        ['sequence-ordinal',['if',['equal','role','4'],['-','ordinal','1'],'ordinal']],
        ['or',['not',['equal','role','4']],['posp','ordinal']],
        ['fn2-checkpoint-map-page-shapep','total','sequence-ordinal','first','count','has-next','slots'],
        ['fn2-checkpoint-page-completed-extent-p','token','okind','oslot','ogen','role',['+','ordinal','1'],'child','fn2-checkpoint-page-verified','fn2-checkpoint-construction','fn2-extents']])
class InventoryWire(unittest.TestCase):
    def test_frontier_authenticates_count_and_full_ref(self):
        text=(ROOT/'books/event-proof-format.lisp').read_text()
        self.assertIn('(inventory-count :varint)',text)
        self.assertIn('(fn2-format-prefix "INVENTORY-" *fn2-format-ref*)',text)
        self.assertIn('(fn2-format-prefix "DIRECTORY-" *fn2-format-ref*)',text)
        self.assertIn('(* 32 (ceiling *fn2-event-frontier-header-max-size* 32))',text)
    def test_shared_linked_codec_distinguishes_physical_and_local_ordinals(self):
        text=(ROOT/'books/checkpoint-linked-header.lisp').read_text()
        self.assertTrue(linked_contract(text))
        self.assertFalse(linked_contract(text.replace('(- ordinal 1)','ordinal',1)))
        self.assertFalse(linked_contract(text.replace('(posp ordinal)','t',1)))
        self.assertFalse(linked_contract(text.replace('total sequence-ordinal first','total ordinal first',1)))
        self.assertIn('(4 *page-kind-merkle-node*)',text)
        self.assertIn('(4 *checkpoint-map-body-kind-release-inventory*)',text)
    def test_two_ref_hash_windows_use_one_shared_declaration(self):
        text=(ROOT/'books/event-frontier-ref-fields.lisp').read_text()
        self.assertIn('(fn2-event-frontier-ref-bindings *fn2-format-ref* prefix)',text)
        self.assertIn('(ref-off frontier-ref-offset)',text)
        self.assertIn('(fn2-checkpoint-page-verified-allocation frontier-ref-extent fn2-checkpoint-page-verified)',text)
        linked=(ROOT/'books/checkpoint-linked-header.lisp').read_text()
        self.assertIn('(fn2-pool-write slot gen (+ off i) byte',linked)
        self.assertIn('(- left 1) (+ i 1) off extent',linked)
        self.assertIn('(unsigned-byte-p 32 (+ off i left))',linked)
        build=(ROOT/'books/event-build.lisp').read_text()
        self.assertIn('(fn2-event-frontier-put-ref "DIRECTORY-" base child 0 scratch sgen)',build)
    def test_structural_frontier_carrier_threading_is_bounded_and_idempotent(self):
        original='(defun '+frontier.NAME+' (budget a) (declare (xargs :stobjs (a) :guard (and (ap a)))) (mv :ok '+' '.join(frontier.OUTPUTS)+'))'
        out,count=frontier.rewrite(original)
        self.assertEqual(count,4)
        self.assertEqual(frontier.rewrite(out),(out,0))
        self.assertIn(frontier.TABLE+'p '+frontier.TABLE,out)
        self.assertEqual(out.count(frontier.TABLE+'-wfp'),1)
        actual=(ROOT/'books/checkpoint-restore-events.lisp').read_text()
        self.assertEqual(frontier.rewrite(actual),(actual,0))
        f=definition(actual,frontier.NAME)
        self.assertIn('fn2-checkpoint-restore-release-inventory-capture',str(f))
        # Field capture follows actual root format/header/ref authentication;
        # no consumer-provided count/Ref/ready scalar is accepted.
        body=actual[actual.index('(defun '+frontier.NAME):]
        self.assertLess(body.index('(fn2-event-frontier-header-decode'),body.index('(fn2-checkpoint-restore-release-inventory-capture'))
    def test_existing_linked_tags_and_root_convention_are_preserved(self):
        text=(ROOT/'books/checkpoint-map-format.lisp').read_text()
        self.assertIn('(:allocation-map :recovery-arena :event-proof-directory :release-inventory)',text)
        body=(ROOT/'books/checkpoint-linked-header.lisp').read_text()
        for role,kind in [('2','allocation-map'),('3','manifest')]:
            self.assertIn('('+role+' *page-kind-'+kind+'*)',body)
        self.assertIn('role ordinal extent epoch allocation',body)
        self.assertNotIn('(+ ordinal 2)',body)
if __name__=='__main__':unittest.main()
