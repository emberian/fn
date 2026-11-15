"""Producer extraction and receipt ordering; ACL2 execution is a separate gate."""
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'tools'))
import lisp_rewrite as lr
import boot_bootstrap_extract as p
import checkpoint_boot_input_extract as e


def norm(n):
    if isinstance(n, lr.Lst):
        return tuple(norm(x) for x in n.items)
    if isinstance(n, lr.Pre):
        return n.prefix, norm(n.node)
    return n.low


class BootstrapProducer(unittest.TestCase):
    def setUp(self):
        self.before = json.loads((ROOT/'tools/fixtures/boot-bootstrap-producer-before.json').read_text())['source']
        self.pack = (ROOT/'books/boot-bootstrap-pack.lisp').read_text()
        self.verify = (ROOT/'books/boot-bootstrap-verify.lisp').read_text()

    def test_generated_source_and_owner_instantiation(self):
        self.assertEqual(p.producer(self.before), self.pack)
        generic = p.generic_owner(self.before)
        for name in p.GENERIC:
            original, changed = e.unique(self.before, name), e.unique(generic, name)
            # Instantiate the new explicit owner kind with the old constant.
            edits = []
            formal = next(x for x in changed.items[2].items if x.low == 'kind')
            edits.append((formal.start, formal.end, ''))
            removed = {formal.start}
            for node in p.nodes(changed):
                if isinstance(node, lr.Lst) and node.items and getattr(node.items[0], 'low', None) == name:
                    at = next(x for x in node.items[1:] if getattr(x, 'low', None) == 'kind')
                    removed.add(at.start)
                    edits.append((at.start, at.end, ''))
            for node in p.nodes(changed):
                if isinstance(node, lr.Atom) and node.low == 'kind' and node.start not in removed:
                    edits.append((node.start, node.end, '*fn2-boot-kind*'))
            restored = lr.write(generic, edits)
            self.assertEqual(norm(original), norm(e.unique(restored, name)), name)

    def test_bootstrap_body_uses_same_encoder_and_tail_without_reset(self):
        generated = e.unique(self.pack, 'fn2-boot-bootstrap-encode-pool')
        body = self.pack[generated.start:generated.end]
        self.assertNotIn('fn2-pool-reset', body)
        self.assertEqual(len(lr.match('(fn2-format-bootstrap-encode ?*args)', [generated])), 1)
        self.assertEqual(len(lr.match('(fn2-boot-pad ?*args)', [generated])), 1)
        # Exact extraction mutation is only moving the original reset pair to
        # the caller; no field, decoder or hash body has been copied by hand.
        original = e.unique(p.generic_owner(self.before), 'fn2-boot-bootstrap-pool')
        oldbindings = lr.match('(b* ?bindings ?*result)', [original])[0].captures['bindings']
        newbindings = lr.match('(b* ?bindings ?*result)', [generated])[0].captures['bindings']
        self.assertEqual(tuple(norm(x) for x in oldbindings.items[2:]), norm(newbindings))

    def test_expected_construction_cannot_mint_authority(self):
        node = e.unique(self.verify, 'fn2-boot-bootstrap-pack-pool')
        body = self.verify[node.start:node.end]
        self.assertNotIn('update-fn2-boot-config', body)
        self.assertIn('(fn2-boot-pack-geometry', body)
        self.assertIn('(fn2-boot-bootstrap-encode-pool', body)
        self.assertIn('(<= (+ *fn2-format-sector-size* 32) (fn2-pool-cap page fn2-pool))', body)
        self.assertNotIn('scratch', body)

    def test_mint_is_after_actual_whole_sector_compare(self):
        node = e.unique(self.verify, 'fn2-boot-bootstrap-verify-pool')
        body = self.verify[node.start:node.end]
        self.assertIn('(not (equal page rx))', body)
        self.assertIn('(equal (fn2-boot-config-bootstrap-owner-gen fn2-boot-config) 0)', body)
        compared = body.index('(fn2-pool-compare')
        self.assertLess(body.index('(fn2-layout-range-code rx'), compared)
        self.assertLess(body.index('(fn2-boot-bootstrap-pack-pool'), compared)
        self.assertLess(compared, body.index('(fn2-boot-save-geometry'))
        self.assertIn('(eq result :equal) (equal at *fn2-format-sector-size*)', body)
        for field in ('domain', 'lineage', 'incarnation', 'history', 'history-incarnation'):
            self.assertLess(compared, body.index('(update-fn2-boot-config-bootstrap-'+field))
        final = body.index('(update-fn2-boot-config-bootstrap-owner-gen ogen')
        self.assertGreater(final, body.index('(update-fn2-boot-config-bootstrap-history-incarnation'))
        self.assertNotIn('checkpoint-layout-ready', body)

    def test_full_receipt_is_one_shared_owner_namespace_predicate(self):
        receipt = (ROOT/'books/boot-bootstrap-receipt.lisp').read_text()
        for field in ('domain', 'lineage', 'incarnation', 'history', 'history-incarnation'):
            self.assertIn('(fn2-boot-config-bootstrap-'+field+' fn2-boot-config)', receipt)
        descriptor = (ROOT/'books/checkpoint-boot-descriptor.lisp').read_text()
        self.assertIn('(fn2-boot-bootstrap-receipt-p kind id ogen fn2-boot-config fn2-origin)', descriptor)


if __name__ == '__main__':
    unittest.main()
