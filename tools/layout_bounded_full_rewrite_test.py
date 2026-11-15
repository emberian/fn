import hashlib
from pathlib import Path
import unittest
import lisp_rewrite as lr
import layout_payload_span_rewrite as span
import layout_bounded_full_rewrite as rw

ROOT=Path(__file__).resolve().parents[1]
BASE=(ROOT/'tools/fixtures/layout-full-decode-before.lisp').read_text()


def form(source,name):
    n=rw.one(source,name);return source[n.start:n.end]


class Full(unittest.TestCase):
    def test_model_error_is_independent_of_full_and_scan_changes(self):
        after=rw.model_error(BASE)
        self.assertEqual(after,rw.model_error(after))
        self.assertEqual(after,BASE.replace("((unless (member-eq code '(:ok :more))) (mv code off fn2-fields))",
                                           "((unless (member-eq code '(:ok :more))) (mv code n fn2-fields))",1))
        original=(ROOT/'tests/layout-model-error-boundary-unit.lisp').read_text()
        self.assertIn("'(t :nonzero-padding 0 :nonzero-padding 3 t t)",original)

    def test_actual_span_caps_full_work_and_preflight_precedes_mutation(self):
        self.assertEqual(hashlib.sha256(BASE.encode()).hexdigest(),
                         '2060684efd33bb23e0c426275edc9a3dc6c47b50ceda0b80207c84ec7fd89d48')
        after=rw.full(BASE)
        self.assertEqual(after,rw.full(after))
        for name in ['fn2-layout-scan','fn2-layout-decode-step','fn2-codec-spec-events',
                     'fn2-codec-byte-form','fn2-layout-byte','fn2-layout-encode']:
            self.assertEqual(form(BASE,name),form(after,name),name)
        self.assertIn('(fuel (+ 1 (min (nfix (- end off)) ,max-name) ,(fn2-codec-empty-count layout)))',after)
        n=lr.match('(defun ,decode ?*body)',lr.parse(form(after,'fn2-codec-events')).forms)[0].node
        text=lr.flat(n)
        self.assertLess(text.index('fn2-layout-range-code'),text.index(',start'))
        self.assertNotIn('4096',text)
        self.assertIn('(,scan fuel base',form(after,'fn2-codec-events'))
        self.assertNotIn(':oversized',form(after,'fn2-codec-events'))

    def test_three_named_projections_commute_without_a_second_scanner(self):
        first=rw.full(rw.model_error(span.rewrite(BASE)))
        second=span.rewrite(rw.model_error(rw.full(BASE)))
        self.assertEqual(first,second)
        self.assertEqual(form(first,'fn2-codec-spec-events'),form(BASE,'fn2-codec-spec-events'))
        self.assertEqual(len(lr.match('(defun fn2-layout-scan ?*body)',lr.parse(first).forms)),1)
        self.assertEqual(len(lr.match('(defun ,scan ?*body)',lr.parse(first).forms)),1)
        self.assertIn('(posp budget) (<= budget 4096)',first)

    def test_actual_post_projection_controls_cover_results_and_effects(self):
        fixture=(ROOT/'tools/fixtures/layout-bounded-full-unit.lisp').read_text()
        for text in ['(fn2-span-case 6144 4096', '(fn2-span-fixture-decode ',
                     '(fn2-layout-decode ', '(equal frame (fn2-span-frame fn2-fields))',
                     '(eq gt :truncated)', '(= mtn gtn)', '(= menext genext)',
                     "'(t :truncated 9 :truncated 9 t)", "'(t :more 10 :more 10 t)"]:
            self.assertIn(text,fixture)


if __name__=='__main__':unittest.main()
