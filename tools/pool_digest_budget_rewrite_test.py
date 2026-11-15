import hashlib
from pathlib import Path
import unittest
import lisp_rewrite as lr
import pool_digest_budget_rewrite as rw
ROOT=Path(__file__).resolve().parents[1]


def form(source,head,name):
    n=lr.match(f'({head} {name} ?*body)',lr.parse(source).forms,deep=False)[0].node
    return source[n.start:n.end]


class Fetch(unittest.TestCase):
    def test_exact_current_provider_and_original_logic_effect_claim(self):
        before=(ROOT/'tools/fixtures/pool-digest-budget-before.lisp').read_text()
        self.assertEqual(hashlib.sha256(before.encode()).hexdigest(),
                         'f7d2dd9f1687703d8df34e771925515c32998325d844bbc05d316e63191c1096')
        after=rw.rewrite(before);self.assertEqual(after,(ROOT/'books/pool-digest.lisp').read_text())
        self.assertEqual(after,rw.rewrite(after))
        for head,name in [('defun','fn2-rec-byte-at'),('defthm','fn2-rec-byte-at-bound'),
                          ('defthm','fn2-rec-byte-at-natp'),('defthm','fn2-rec-fetch-shape')]:
            self.assertEqual(form(before,head,name),form(after,head,name),name)
        old=lr.match('(defun fn2-rec-fetch ?*body)',lr.parse(before).forms)[0].node.items[-1]
        new=lr.match('(defun fn2-rec-fetch ?*body)',lr.parse(after).forms)[0].node.items[-1]
        self.assertEqual(before[old.start:old.end],after[new.items[2].start:new.items[2].end])
        self.assertIn('(equal (mv-list 2 (fn2-rec-fetch ',after)
        self.assertIn('(include-book "std/util/bstar" :dir :system)',after)

    def test_shared_u32_transition_and_whole_word_commit(self):
        source=(ROOT/'books/pool-digest.lisp').read_text()
        worker=form(source,'defun','fn2-rec-fetch-bytes')
        self.assertIn('(fn2-layout-byte :u32 pos acc 0 0 0 byte)',worker)
        self.assertIn('(fn2-rec-byte-at slot gen (+ off next)',worker)
        self.assertNotIn('16777216',worker)
        self.assertLess(worker.index('(fn2-rec-fetch-state-p after partial)'),worker.index('(fn2-digest-set-word'))
        self.assertIn('(if complete (fn2-digest-set-word',worker)
        self.assertIn('(min budget (- 32 next))',form(source,'defun','fn2-rec-fetch-step'))

    def test_actual_encoder_budget_one_refusal_and_partial_effect_controls(self):
        fixture=(ROOT/'tests/pool-digest-budget-unit.lisp').read_text()
        for text in ['(fn2-rec-budget-words-encode ', '(fn2-rec-fetch-step 1 next acc ',
                     '(= after (+ 1 next))', '(fn2-rdb-words 0 0 (floor after 4)',
                     '(fn2-rec-fetch-step 0 0 0 ', '(eq wrong :owner)', '(eq stale :stale)',
                     '(fn2-rec-fetch 8 ', '(eq short :bounds)', '(fn2-rdb-words 0 0 2 ',
                     '(equal source (fn2-pool-copy fn2-pool))']:
            self.assertIn(text,fixture)


    def test_fixed_fixture_recursion_has_total_logical_successors(self):
        before=(ROOT/'tools/fixtures/pool-digest-budget-unit-before-totalize.lisp').read_text()
        after=rw.fixture_totalize(before)
        self.assertEqual(after,(ROOT/'tests/pool-digest-budget-unit.lisp').read_text())
        self.assertEqual(after,rw.fixture_totalize(after))
        for name,index in [('fn2-rdb-seed','i'),('fn2-rdb-words','i'),('fn2-rdb-full','k')]:
            function=form(after,'defun',name)
            n=lr.match('('+name+' ?index ?*rest)',lr.parse(function).forms[0].items[-1:])[0].captures['index']
            self.assertTrue(lr.match('(+ 1 (nfix '+index+'))',[n],deep=False))


if __name__=='__main__':unittest.main()
