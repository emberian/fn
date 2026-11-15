"""SOURCE controls for current-root subjects and truthful proof projection."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr
import checkpoint_reader_root_projection as p


class RootReaderProjection(unittest.TestCase):
    def test_named_root_reader_and_checkpoint_schemas_preserved(self):
        # Composed foundations can replace an identical slot predicate with
        # its canonical declaration. Do not freeze entire unrelated books.
        checkpoint = (ROOT/'books/checkpoint.lisp').read_text()
        for table in ('fn2-checkpoints','fn2-checkpoint-refs','fn2-checkpoint-bytes'):
            pattern = '(defcolumns '+table+' ?*body)'
            self.assertEqual(p.norm(p.unique(checkpoint, pattern)),
                             p.norm(p.unique(p.source(p.BASE,'books/checkpoint.lisp'),pattern)))
        old = p.source(p.BASE, 'books/checkpoint-descriptor-read.lisp')
        now = (ROOT/'books/checkpoint-descriptor-read.lisp').read_text()
        pattern = '(defun fn2-checkpoint-check-step ?*body)'
        self.assertEqual(p.norm(p.unique(old, pattern)), p.norm(p.unique(now, pattern)))
        # The actual canonical evidence interface must remain available; its
        # newer implementation is not overwritten with donor bytes.
        provider=(ROOT/'books/square-evidence.lisp').read_text()
        fn=p.unique(provider,'(defun fn2-square-predicate-evidence-events-with-hints ?*body)')
        self.assertEqual(p.norm(fn.items[2]),
                         ('name','positive','negative','positive-hints','negative-hints','recheck','world'))

    def test_guard_expansion_and_actual_format_workers_match(self):
        for path, names in [('books/format-check.lisp',
          ('fn2-fc-guard','fn2-format-run','fn2-fc-byte','fn2-fc-advance',
           'fn2-fc-run-bytes','fn2-fc-step','fn2-fc-reset')),
          ('books/blake3.lisp', ('fn2-b3-ready',))]:
            for name in names:
                head = 'defmacro' if name == 'fn2-fc-guard' else 'defun'
                pattern = '('+head+' '+name+' ?*body)'
                self.assertEqual(p.norm(p.unique(p.source(p.BASE,path),pattern)),
                                 p.norm(p.unique(p.source(p.DONOR,path),pattern)), name)

    def test_structural_projection_and_original_fixture(self):
        before = p.source(p.BASE, 'books/checkpoint-descriptor-read.lisp')
        self.assertEqual(before, (ROOT/'tools/fixtures/checkpoint-reader-root-before.lisp').read_text())
        donor = p.source(p.DONOR, 'books/checkpoint.lisp')
        self.assertEqual(p.reader(before, donor), (ROOT/'books/checkpoint-descriptor-read.lisp').read_text())
        self.assertEqual(p.interfaces(donor), (ROOT/'books/checkpoint-reader-interfaces.lisp').read_text())

    def test_original_carriers_arguments_and_claim_generation(self):
        old = p.source(p.BASE, 'books/checkpoint-descriptor-read.lisp')
        macro = p.unique(old, '(fn2-checkpoints-preserves fn2-checkpoint-check-step ?*body)')
        text = (ROOT/'books/checkpoint-descriptor-read.lisp').read_text()
        # Existing original formals/positions/prefixes are identical. H/C are
        # generated from them; hints do not become a new hypothesis.
        expected = p.unique(text, '(expected-args ?args)').items[1].node
        self.assertEqual(p.norm(expected), p.norm(macro.items[2]))
        carrier_node = p.unique(text, '(carriers ?value)').items[1].node
        old_carriers = macro.items[next(i for i,n in enumerate(macro.items) if getattr(n,'low',None)==':carriers')+1]
        for a,b in zip(carrier_node.items,old_carriers.items):
            self.assertEqual(p.norm(lr.Lst(a.items[:4])),p.norm(lr.Lst(b.items[:4])))
        self.assertEqual(len(carrier_node.items),8)
        self.assertIn('(hyps (fn2-columns-carrier-hyps carriers))', text)
        self.assertIn('(facts (fn2-columns-preservation-facts name (cons name args) specs hyps hints))',text)
        self.assertIn('(defthm-owed ,(cadr fact) ,args ,(caddr fact)',text)

    def test_narrow_interfaces_do_not_replace_original_contracts(self):
        lower = (ROOT/'books/checkpoint-reader-interfaces.lisp').read_text()
        self.assertIn(':prefix "-FIELDS-ONLY"', lower)
        self.assertIn('fn2-checkpoint-decode-fields-domain-value-type', lower)
        self.assertEqual(sum(1 for n in lr.parse(lower).forms
                             if isinstance(n,lr.Lst) and n.items and getattr(n.items[0],'low',None)=='defthm'),7)
        self.assertNotIn('(defun ',lower)
        self.assertNotIn('(local (defthm',lower)

    def test_real_controls_and_canonical_predicate_replay_retained(self):
        negative = (ROOT/'tests/checkpoint-reader-scalar-domain-unit.lisp').read_text()
        expected = p.source(p.DONOR,'tests/checkpoint-reader-scalar-domain-unit.lisp').replace(
            '(include-book "../books/checkpoint")','(include-book "../books/checkpoint-descriptor-read")')
        self.assertEqual(negative,expected)
        text=(ROOT/'tests/checkpoint-reader-refutation-unit.lisp').read_text()
        self.assertEqual(text,p.source(p.DONOR,'tests/checkpoint-reader-refutation-unit.lisp'))
        self.assertIn('(fn2-evidence-hypothesis-cut hyp guard)',text)
        self.assertIn('(fn2-square-predicate-evidence-events-with-hints',text)
        self.assertIn('`(fn2-assert-square-evidence ,claim)',text)


if __name__ == '__main__':
    unittest.main()
