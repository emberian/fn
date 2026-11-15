"""Actual inventory factories and shared page engine; source checks only."""
from pathlib import Path
import sys
import unittest
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'tools'))
from lisp_source import forms,read_sexp
from checkpoint_master_source_check import walk
import lisp_rewrite as lr

def text(name):return (ROOT/'books'/(name+'.lisp')).read_text()
def operation(name):
    return next(read_sexp(f) for f in forms(text('checkpoint-restore-release-inventory-reader'))
                if read_sexp(f)[:2]==['fn2-checkpoint-release-reader-operation',name])
class InventoryReader(unittest.TestCase):
    def test_same_physical_and_linked_reader_not_a_seventh_root(self):
        source=text('checkpoint-restore-release-inventory-reader')
        self.assertIn('fn2-checkpoint-restore-reader-page-step',str(operation('fn2-checkpoint-restore-release-inventory-page-step')))
        self.assertNotIn('(fn2-format-run ',source)
        generic=text('checkpoint-restore-read')
        self.assertIn('(6 (mv :ok *page-kind-merkle-node* *checkpoint-map-body-kind-release-inventory*',generic)
        self.assertIn('(6 (fn2-release-inventory-entry-decode',generic)
        rootbegin=next(read_sexp(f) for f in forms(text('checkpoint-restore-reader')) if read_sexp(f)[:2]==['defun','fn2-checkpoint-restore-reader-begin'])
        self.assertIn(['member-equal','role',['quote',['2','3','4','5']]],list(walk(rootbegin)))
    def test_capture_has_no_caller_ref_count_success_or_generation(self):
        capture=operation('fn2-checkpoint-restore-release-inventory-capture')
        self.assertEqual(capture[2],[])
        self.assertIn('fn2-checkpoint-restore-events-current-p',str(capture))
        self.assertIn('*fn2-checkpoint-restore-events-phase-frontier*',str(capture))
        self.assertIn('*fn2-checkpoint-restore-reader-phase-page*',str(capture))
        self.assertIn('*fn2-event-frontier-header-field-inventory-count*',str(capture))
        self.assertIn('fn2-checkpoint-release-copy-pool-hash',str(capture))
        self.assertNotIn(':ready',text('checkpoint-restore-release-inventory-state'))
    def test_exact_map_and_pending_target_before_advancing(self):
        entry=str(operation('fn2-checkpoint-restore-release-inventory-entry'))
        for premise in ('fn2-checkpoint-release-map-handle-p','*fn2-extent-state-retire-pending*',
                        'fn2-checkpoint-restore-map-retirement','fn2-checkpoint-restore-release-entries-target-generation',
                        'fn2-checkpoint-restore-release-entries-generation','fn2-checkpoint-release-copy-entry-hash'):
            self.assertIn(premise,entry)
        self.assertIn("['<', 'tail', 'journal']",entry)
        self.assertEqual(entry.count('fn2-origin-physicalp'),3)
        calls=list(walk(operation('fn2-checkpoint-restore-release-inventory-entry')))
        claims=[c for c in calls if c and c[0]=='fn2-checkpoint-restore-reach-claim']
        self.assertEqual(len(claims),3)
        self.assertEqual([c[1] for c in claims],['*fn2-checkpoint-restore-reach-role-journal*','*fn2-checkpoint-restore-reach-role-journal*','*fn2-checkpoint-restore-reach-role-release-descriptor*'])
        self.assertTrue(all(c[2]!='e' for c in claims))
        self.assertNotIn('fn2-alloc-free',entry)
    def test_terminal_is_actual_reader_and_source_coverage(self):
        source=text('checkpoint-restore-release-inventory-source')
        for required in ('*fn2-checkpoint-restore-reader-phase-done*','fn2-checkpoint-map-page-count',
                         'fn2-checkpoint-restore-reader-entry-ordinal','fn2-checkpoint-restore-release-inventory-consumed',
                         'fn2-checkpoint-restore-release-inventory-hashes-p','fn2-checkpoint-restore-reach-reader-p'):
            self.assertIn(required,source)
        self.assertIn('(fn2-checkpoint-restore-release-entries-generation head',source)
        self.assertIn('(fn2-checkpoint-restore-release-entries-journal-extent tail',source)
        finish=operation('fn2-checkpoint-restore-release-inventory-finish')
        self.assertEqual(finish[2],[])
        self.assertIn('fn2-checkpoint-restore-release-inventory-reader-terminal-p',str(finish))
        self.assertNotIn('fn2-alloc',str(finish))
    def test_wire_schema_is_the_scalar_store_map(self):
        source=text('checkpoint-restore-release-inventory-reader')
        self.assertIn('(fn2-checkpoint-release-entry-stores *fn2-release-inventory-entry*)',source)
        self.assertIn('(fn2-codec-field',source)
        self.assertIn('(eq (cadar layout) :digest)',source)
        self.assertNotIn('(fn2-checkpoint-restore-release-entries-set-h0',source)
    def test_existing_columns_typed_carrier_contracts(self):
        source=text('checkpoint-restore-release-inventory-source')
        reader=text('checkpoint-restore-release-inventory-reader')
        self.assertIn('fn2-columns-carrier-hyps',source)
        self.assertIn('fn2-columns-carrier-specs',reader)
        self.assertIn('fn2-checkpoint-release-row-specs',reader)
        self.assertNotIn('fn2-checkpoint-root1-child-hyps',source+reader)
if __name__=='__main__':unittest.main()
