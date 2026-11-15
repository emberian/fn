"""Source projection controls, not execution or a parser implementation."""
import hashlib
from pathlib import Path
import unittest
import lisp_rewrite as lr
import layout_payload_span_rewrite as rw

ROOT=Path(__file__).resolve().parents[1]
BASE=(ROOT/'tools/fixtures/layout-full-decode-before.lisp').read_text()


def form(source,name):
    n=lr.match(f'(defun {name} ?*body)',lr.parse(source).forms,deep=False)[0].node
    return source[n.start:n.end]


class Span(unittest.TestCase):
    def test_exact_qualified_baseline_public_and_model_forms_unchanged(self):
        self.assertEqual(hashlib.sha256(BASE.encode()).hexdigest(),
                         '2060684efd33bb23e0c426275edc9a3dc6c47b50ceda0b80207c84ec7fd89d48')
        after=rw.rewrite(BASE)
        self.assertEqual(after,rw.rewrite(after))
        for name in ['fn2-layout-scan','fn2-layout-decode-run','fn2-layout-decode',
                     'fn2-layout-decode-step','fn2-layout-byte','fn2-layout-encode',
                     'fn2-codec-spec-events','fn2-codec-byte-form']:
            self.assertEqual(form(BASE,name),form(after,name),name)
        self.assertIn('(,step base slot gen off end okind oslot ogen 4096 fn2-fields fn2-pool)',after)
        # Opaque chunk does not alter the old G1/runes/hints or codec tables.
        beforegen=form(BASE,'fn2-codec-events');aftergen=form(after,'fn2-codec-events')
        for token in ['(local (in-theory *fn2-codec-proof-runes*))',
                      ':encode ,encode :decode ,decode :decode-step ,step :start ,start :size ,sizefn']:
            self.assertEqual(beforegen.count(token),aftergen.count(token))

    def test_source_type_and_range_are_required_without_runtime_whole_scan(self):
        after=rw.rewrite(BASE);chunk=form(after,'fn2-layout-payload-chunk')
        self.assertNotIn('fn2-poolp',chunk)
        self.assertIn('(min fuel (- size pos) (- end next))',chunk)
        self.assertIn('(fn2-layout-range-code slot gen next (+ next n) nil okind oslot ogen fn2-pool)',chunk)
        gen=form(after,'fn2-codec-events')
        self.assertLess(gen.index('(fn2-pool-read slot gen next'),gen.index('(chunk (fn2-layout-payload-chunk'))
        self.assertLess(gen.index('Pool returned a non-octet.'),gen.index('(chunk (fn2-layout-payload-chunk'))
        self.assertIn('(and (not empty) (= payload 1))',gen)
        self.assertIn('(,bytefn phase (+ pos (- chunk 1)) v hi size payload byte)',gen)
        self.assertIn('(,scan (- fuel chunk) base phase',gen)
        self.assertIn('(,scan (- fuel chunk) base (,nextfn phase)',gen)
        lemma=lr.match('(defthm fn2-layout-readable-span-octet ?*body)',lr.parse(after).forms)[0].node
        self.assertIn('(fn2-poolp fn2-pool)',after[lemma.start:lemma.end])
        self.assertIn('(equal (mv-list 3 (,scan ,@scanargs fn2-fields fn2-pool))',gen)
        self.assertIn('"-EXEC-HYPS"',gen)
        self.assertIn('"-EXEC-REFINES"',gen)

    def test_mbe_logical_subject_is_exact_original_generated_scanner(self):
        before=form(BASE,'fn2-codec-events');after=form(rw.rewrite(BASE),'fn2-codec-events')
        original=lr.match('(defun ,scan ?*body)',lr.parse(before).forms)[0].node.items[-1]
        changed=lr.match('(defun ,scan ?*body)',lr.parse(after).forms)[0].node.items[-1]
        self.assertEqual(changed.items[0].low,'mbe')
        self.assertEqual(changed.items[1].low,':logic')
        self.assertEqual(before[original.start:original.end],after[changed.items[2].start:changed.items[2].end])
        self.assertEqual(changed.items[3].low,':exec')

    def test_real_control_compares_every_visit_to_existing_model(self):
        fixture=(ROOT/'tests/layout-payload-span-unit.lisp').read_text()
        self.assertIn('(fn2-layout-decode-run ',fixture)
        self.assertIn('(fn2-span-fixture-decode-step ',fixture)
        self.assertIn('(equal (fn2-span-compiled-state code next fn2-fields) (car expected))',fixture)
        for text in ['(fn2-pool-semanticp fn2-pool)', '(fn2-span-test 6144 1)',
                     '(fn2-span-test 6144 4096)', '(eq zero-code :bounds)',
                     '(eq owner-code :owner)', '(equal frame (fn2-span-frame fn2-fields))']:
            self.assertIn(text,fixture)

    def test_refinement_teeth_use_same_generated_terms_and_remove_only_type(self):
        fixture=(ROOT/'tools/fixtures/layout-span-refinement-teeth.lisp').read_text()
        for text in ["(fn2-codec-events 'fn2-span-fixture", '(car (last scan))',
                     '(cadr (member-eq :exec body))',
                     "(without-pool-type (list 'and (cadr whole) (cadddr whole)))",
                     "(left (list 'mv-list 3 (cons 'fn2-span-fixture-scan args)))",
                     '(fn2-span-teeth-build positive 0 24 nil nil)',
                     '(fn2-span-teeth-build positive 8 12 nil nil)',
                     '(fn2-span-teeth-build positive 19 24 23 9)',
                     '(fn2-span-teeth-build removed 8 24 6 256)']:
            self.assertIn(text,fixture)
        old=(ROOT/'tests/layout-model-empty-boundary-unit.lisp').read_text()
        self.assertIn("'(t :more 1 2 1 :more 1 1 0)",old)


if __name__=='__main__': unittest.main()
