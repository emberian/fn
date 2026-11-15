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
        self.assertIn('(mbe :logic (fn2-poolp fn2-pool) :exec t)',chunk)
        self.assertIn('(min fuel (- size pos) (- end next))',chunk)
        self.assertIn('(fn2-layout-range-code slot gen next (+ next n) nil okind oslot ogen fn2-pool)',chunk)
        gen=form(after,'fn2-codec-events')
        self.assertLess(gen.index('(fn2-pool-read slot gen next'),gen.index('(chunk (fn2-layout-payload-chunk'))
        self.assertLess(gen.index('Pool returned a non-octet.'),gen.index('(chunk (fn2-layout-payload-chunk'))
        self.assertIn('(and (not empty) (= payload 1))',gen)
        self.assertIn('(,bytefn phase (+ pos (- chunk 1)) v hi size payload byte)',gen)
        self.assertIn('(,scan (- fuel chunk) base phase',gen)
        self.assertIn('(,scan (- fuel chunk) base (,nextfn phase)',gen)


if __name__=='__main__': unittest.main()
