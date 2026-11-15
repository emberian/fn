from pathlib import Path
import json,sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
import ledger

def function(text,name):
    m=lr.match('(defun '+name+' ?*body)',lr.parse(text).forms)
    assert len(m)==1
    return text[m[0].start:m[0].end]

class SliceComposition(unittest.TestCase):
    def test_actual_core_wrapper_changes_only_shared_slice_call(self):
        before=json.loads((ROOT/'tools/fixtures/feed-slice-current-wrapper.json').read_text())['function']
        after=function((ROOT/'books/assembly-callbacks-d.lisp').read_text(),'fn2-upload-feed-pool')
        expected=before.replace('fn2-upload-feed-loop','fn2-upload-feed-slice').replace('discard raw 0 rslot','discard raw rslot')
        self.assertEqual(ledger.read_forms(after),ledger.read_forms(expected))
    def test_public_face_and_actual_core_share_one_projection(self):
        text=(ROOT/'books/upload-feed.lisp').read_text()
        self.assertIn('fn2-upload-feed-slice',function(text,'fn2-upload-feed'))
        body=function(text,'fn2-upload-feed-slice')
        self.assertIn('(fn2-feed-cap dslot fn2-pool) nil fn2-pool)',body)
        self.assertIn('(declare (ignore lines))',body)
        self.assertIn('(mv status next mode2 discard2 copied fn2-pool)',body)
        self.assertIn('fn2-upload-feed-slice-projection-by-definition',text)
    def test_count_worker_has_one_owner_and_txn_reaches_it(self):
        import certs
        txn=(ROOT/'books/txn.lisp').read_text()
        feed=(ROOT/'books/upload-feed.lisp').read_text()
        self.assertNotIn('(defun fn2-txn-count-loop ',txn)
        self.assertEqual(feed.count('(defun fn2-txn-count-loop '),1)
        self.assertIn('books/upload-feed',certs.closure(ROOT,'books/txn'))
    def test_control_uses_actual_slice_and_whole_pool_refusal(self):
        text=(ROOT/'tests/upload-feed-slice-unit.lisp').read_text()
        self.assertIn('(fn2-upload-feed-slice budget',text)
        self.assertIn('(equal before (fn2-pool-copy fn2-pool))',text)
        for args in ['3 100 nil','8 100 nil','8 1 nil','8 100 t']:
            self.assertIn('(fn2-ufs-run '+args+')',text)

if __name__=='__main__':unittest.main()
