"""Actual consumer/source extraction controls; not ACL2 qualification."""
from pathlib import Path
import hashlib
import json
import unittest
import lisp_rewrite as lr

class CreditConsumers(unittest.TestCase):
    def test_anchor_tail_is_same_consumer(self):
        source = Path('tests/checkpoint-anchor-future-unit.lisp').read_text()
        receipt = json.loads(Path('tools/fixtures/checkpoint-anchor-consumer-extraction.json').read_text())
        parsed = lr.parse(source)
        form = next(source[n.start:n.end] for n in parsed.forms
                    if source[n.start:n.end].startswith('(defun fn2-cafu-consumer-body '))
        tail = form[form.index('((mv journal '):]
        for old, new in receipt['normalizations'].items():
            tail = tail.replace(new, old)
        original = '      '+tail
        self.assertEqual(hashlib.sha256(original.encode()).hexdigest(), receipt['original_consumer_tail_sha256'])
        self.assertEqual(form.count('(fn2-checkpoint-publication-harvest '), 2)
        self.assertNotIn('(fn2-pool-reserve', form)
        self.assertNotIn('(fn2-pool-release', form)

    def test_configured_actual_producer_and_same_consumers(self):
        s = Path('tests/checkpoint-configured-borrow-unit.lisp').read_text()
        lr.parse(s)
        for call in ['fn2-cwc-body', 'fn2-checkpoint-root1-credit-abort-empty',
                     'fn2-checkpoint-root1-reserve', 'fn2-checkpoint-future-bind',
                     'fn2-cafu-consumer-body']:
            self.assertIn('('+call+' ', s)
        self.assertIn('(equal before (fn2-pcu-view fn2-pool))', s)
        self.assertIn('(equal provenance-before (fn2-ccbc-provenance', s)
        self.assertIn('(fn2-pool-credit-fullp 1 0 fn2-pool)', s)
        self.assertNotIn('(fn2-pool-set-', s)
        self.assertNotIn('(fn2-checkpoint-future-windows-set-', s)

    def test_actual_b_order_and_join_refusal_frames(self):
        s = Path('books/commit.lisp').read_text()
        start = s[s.index('(defun fn2-commit-start '):]
        self.assertLess(start.index('(fn2-commit-reserve-ordinary-pools '), start.index('(fn2-commit-reserve-extent '))
        self.assertLess(start.index('(fn2-commit-reserve-extent '), start.index('(fn2-commit-close-ordinary-credit id owner-gen batch nil'))
        self.assertLess(start.index('(fn2-commit-close-ordinary-credit id owner-gen batch nil'), start.index('(phase *fn2-commit-state-collect*)'))
        end_failure = start[start.index('((unless (eq ended :ok))'):start.index('(phase *fn2-commit-state-collect*)')]
        self.assertIn('(mv :uncertain fn2-core)', end_failure)
        self.assertNotIn('release-pools', end_failure)
        fixture = Path('tests/ordinary-drain-credit-unit.lisp').read_text()
        lr.parse(fixture)
        self.assertIn('(eq pick :join)', fixture)
        for call in ['(fn2-commit-txn-join ', '(fn2-commit-admit-txn slot (+ 1 gen)',
                     '(equal queued-before (fn2-odc-noio fn2-core))',
                     '(equal leases-before (fn2-odc-pool fn2-core))']:
            self.assertIn(call, fixture)

if __name__ == '__main__':
    unittest.main()
