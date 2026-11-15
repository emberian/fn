"""Source routing controls; actual ACL2 recovery execution is a separate gate."""
from pathlib import Path
import sys, unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
import lisp_rewrite as lr
ROOT = Path(__file__).resolve().parents[1]
def form(text, name):
    for f in lr.parse(text).forms:
        if hasattr(f, 'items') and len(f.items)>1 and getattr(f.items[1], 'low', '') == name:
            return text[f.start:f.end]
    raise AssertionError(name)
class OwnershipOrder(unittest.TestCase):
    def setUp(self):
        self.adopt=(ROOT/'books/recovery-selected-adopt.lisp').read_text()
        self.machine=(ROOT/'books/recovery-machine.lisp').read_text()
    def test_selected_install_defers_without_mutating_allocator(self):
        body=form(self.adopt,'fn2-recovery-install-adopt')
        self.assertIn('(t :deferred)',body)
        self.assertNotIn('fn2-checkpoint-suffix-allocation-begin-record',body)
        self.assertNotIn('fn2-recovery-selected-adopt-position',body)
        self.assertIn('(fn2-recovery-adopt p fn2-core)',body) # full-base path retained
    def test_authentication_precedes_every_replay_mutation(self):
        body=form(self.adopt,'fn2-recovery-replay-adopt')
        self.assertLess(body.index('fn2-rp-current-unit-auth-p'),body.index('fn2-recovery-selected-adopt-position'))
        self.assertLess(body.index('fn2-recovery-payload-node'),body.index('fn2-recovery-selected-adopt-position'))
        for word in ['fn2-recovery-payload-head','(rc-own-left (if journalp count (- left 1)))',"'(5 6 7 8)"]:
            self.assertIn(word,body)
    def test_frontier_then_ownership_then_records(self):
        start=self.machine.index('  (replay-frontier :')
        end=self.machine.index('  (replay-open :',start)
        arms=self.machine[start:end]
        self.assertIn('((:done) (:set (rc-stage 5) (rc-own-token 0) (rc-own-left 0))',arms)
        self.assertIn('((:owned) (:set (rc-stage 0))',arms)
        self.assertIn("(member-equal row-rc-stage '(5 6 7 8))) (:goto replay-adopt)",self.machine)
    def test_fixed_records_unit_is_opened_only_for_a_new_commit(self):
        # Role 1 is one fixed records unit, unlike PAYLOAD manifest units.
        reset = '(rc-role 1) (rc-roff 0) (rc-rend 0)'
        replay = self.machine[self.machine.index('  (install-finish :'):]
        self.assertEqual(replay.count(reset), 2)
        install = self.machine[self.machine.index('  (install-finish :'):self.machine.index('  (replay-frontier :')]
        advance = self.machine[self.machine.index('  (replay-commit-end :'):self.machine.index('  (replay-lifecycle :')]
        self.assertIn(reset, install)
        self.assertIn('(rc-commit (+ 1 row-rc-base))', install)
        self.assertIn(reset, advance)
        self.assertIn('(rc-commit (+ 1 row-rc-commit))', advance)
        for begin, end in [('replay-flush', 'replay-commit-end'),
                           ('replay-lifecycle', 'replay-record'),
                           ('replay-record', ':arms')]:
            start = self.machine.index('  (' + begin + ' :')
            stop = self.machine.index('  (' + end + ' :', start) if end != ':arms' else self.machine.index(' :arms', start)
            body = self.machine[start:stop]
            self.assertNotIn('(rc-rend 0)', body)
            self.assertNotIn('(:next :read)', body)
        self.assertIn('(equal row-rc-rend 0)) (:goto replay-open)', self.machine)

    def test_resumed_worker_binds_exact_candidate(self):
        body=form(self.adopt,'fn2-recovery-selected-adopt-position')
        for name in ['worker-kind','worker-slot','worker-gen','classification','commit','extent','epoch','allocation','owner-kind','owner']:
            self.assertIn('fn2-checkpoint-suffix-allocation-'+name,body)
        self.assertIn('(mv :candidate fn2-checkpoint-suffix-allocation fn2-extents fn2-alloc-edges)',body)
if __name__=='__main__': unittest.main()
