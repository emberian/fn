"""Stage12 observes the exact hook before generic machine pending decrement."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
def one(s,name):return lr.match(f'(defun {name} ?*body)',lr.parse(s).forms,deep=False)[0].node
def tree(n):return n.low if hasattr(n,'low') else tuple(tree(x) for x in n.items)
class ReadState(unittest.TestCase):
    def test_original_owner_and_record_binding_is_shared(self):
        source=(ROOT/'books/recovery-release.lisp').read_text()
        before=(ROOT/'tools/fixtures/release-owner-binding-before.lisp').read_text()
        old=one(before,'fn2-rp-release-current-p').items[-1]
        shared=one(source,'fn2-rp-release-owner-metadata-p').items[-1]
        self.assertEqual(tree(old.items[-1]),tree(shared.items[-1]))
        current=one(source,'fn2-rp-release-current-p').items[-1]
        self.assertEqual([tree(x) for x in old.items[1:-1]],[tree(x) for x in current.items[1:-1]])
    def test_observer_pending1_has_no_pending0_authorization_call(self):
        source=(ROOT/'books/recovery-release.lisp').read_text()
        n=one(source,'fn2-recovery-release-read-state');text=lr.emit(n)
        self.assertIn('(= (fn2-machine-pending id fn2-core) 1)',text)
        self.assertIn('(fn2-rp-release-owner-metadata-p id ogen fn2-core)',text)
        self.assertIn('(fn2-rp-release-installation-metadata-p fn2-core)',text)
        self.assertFalse(lr.match('(fn2-rp-current-unit-auth-p ?*args)',[n]))
        self.assertFalse(lr.match('(fn2-rp-release-current-p ?*args)',[n]))
        self.assertFalse(lr.match('(fn2-allocation-release-put ?*args)',[n]))
        for word in [':ready',':waiting',':uncertain',':stale']:self.assertIn(word,text)
if __name__=='__main__':unittest.main()
