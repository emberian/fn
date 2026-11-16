"""Sole BOOT schema extraction and exact qualified lower component inputs."""
from pathlib import Path
import hashlib
import json
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import lisp_rewrite as lr
from boot_config_root_rewrite import project


class BootSchemaProjection(unittest.TestCase):
    def test_exact_named_extraction_and_idempotence(self):
        before = (ROOT / 'tools/fixtures/boot-kind-root-before.lisp').read_text()
        after = (ROOT / 'books/boot-kind.lisp').read_text()
        self.assertEqual(project(before), after)
        self.assertEqual(project(after), after)
        self.assertNotIn('(defcolumns fn2-boot-config ', after)
        self.assertEqual(after.count('(include-book "boot-config-state")'), 1)

    def test_original_config_fields_preserved(self):
        def fields(path):
            nodes = lr.match('(defcolumns fn2-boot-config ?*body)',
                             lr.parse(path.read_text()).forms, deep=False)
            self.assertEqual(len(nodes), 1)
            items = nodes[0].node.items
            index = next(i for i, x in enumerate(items)
                         if getattr(x, 'low', '') == ':extra-fields')
            return {x.items[0].low: lr.flat(x) for x in items[index + 1].items}
        old = fields(ROOT / 'tools/fixtures/boot-config-root-before.lisp')
        new = fields(ROOT / 'books/boot-config-state.lisp')
        self.assertEqual(len(old), 7)
        for name, value in old.items():
            self.assertEqual(new[name], value)

    def test_exact_recorded_component_inputs(self):
        receipt = json.loads((ROOT / 'docs/design/receipts/boot-bootstrap-lower-forty-record.json').read_text())
        self.assertEqual(receipt['count'], 40)
        for book, row in receipt['books'].items():
            self.assertEqual(hashlib.sha256((ROOT / (book + '.lisp')).read_bytes()).hexdigest(),
                             row['raw_sha256'], book)
        self.assertTrue(receipt['cleanup']['handles_gone'])
        self.assertTrue(receipt['cleanup']['scope_absent'])

    def test_component_assertions_remain_registered(self):
        source = (ROOT / 'tests/boot-bootstrap-producer-unit.lisp').read_text()
        for mode in (':positive', ':corrupt', ':tail', ':alias', ':owner', ':short'):
            self.assertIn('(assert-event (fn2-bbp-check ' + mode + '))', source)
        self.assertIn('tests/boot-bootstrap-producer-unit', (ROOT / 'Makefile').read_text().split())


if __name__ == '__main__':
    unittest.main()
