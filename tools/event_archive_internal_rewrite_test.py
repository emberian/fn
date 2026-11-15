"""Actual declaration/admission projections preserve unrelated qualified forms."""
import json
from pathlib import Path
import unittest
import lisp_rewrite as lr
import event_archive_internal_rewrite as rw

ROOT=Path(__file__).resolve().parents[1]
BEFORE=json.loads((ROOT/'tools/fixtures/event-archive-internal-before.json').read_text())['forms']


def form(source, name, head='defun'):
    n=lr.match(f'({head} {name} ?*body)',lr.parse(source).forms,deep=False)[0].node
    return source[n.start:n.end]


class Internal(unittest.TestCase):
    def test_declaration_changes_only_named_schema_seams(self):
        source='\n'.join(BEFORE[n] for n in ['fn2-rs-int-valuesp','fn2-defrunschema',
                                            'defrunschema','fn2-rf-events','fn2-rf-logic-events'])
        after=rw.schema(source)
        self.assertEqual(after,rw.schema(after))
        for n in ['fn2-rf-events','fn2-rf-logic-events']:
            self.assertEqual(form(source,n),form(after,n))
        self.assertIn('(booleanp internal) (or (not internal) (null fold))',after)
        self.assertIn(':fold fold :internal internal',after)
        self.assertEqual(form(after,'fn2-rs-int-valuesp'),rw.INTEGER_VALUES)
        # The same recipe preserves a newer fold-owned refusal inserted by its owner.
        enriched=source.replace('(cond ((not (and (symbolp name)',
            '(cond ((and fold (not (fn2-rf-valuesp value))) :owned-fold-refusal)\n'
            '        ((not (and (symbolp name)')
        self.assertIn(':owned-fold-refusal',rw.schema(enriched))

    def test_actual_put_and_replay_refuse_before_mutation_or_decode(self):
        for name,recipe,consumer in [
            ('fn2-succ-put',rw.put,'(fn2-succ-slots-put'),
            ('fn2-succ-replay-records',rw.replay,'(fn2-run-layout-decode')]:
            after=recipe(BEFORE[name])
            self.assertEqual(after,recipe(after))
            self.assertLess(after.index('(fn2-run-layout-internal-p sid)'),after.index(consumer))
            current=(ROOT/('books/machines-c-successor.lisp' if name=='fn2-succ-put'
                           else 'books/machines-c-bind.lisp')).read_text()
            self.assertIn('(fn2-run-layout-internal-p sid)',form(current,name))

    def test_exact_scalar_classifier_excludes_all_reference_octets(self):
        after=rw.schema('\n'.join(BEFORE[n] for n in ['fn2-rs-int-valuesp','fn2-defrunschema','defrunschema']))
        current=(ROOT/'books/runs-schema.lisp').read_text()
        self.assertEqual(form(after,'fn2-rs-scalar-value-kindp'),form(current,'fn2-rs-scalar-value-kindp'))
        self.assertEqual(form(after,'fn2-rs-int-valuesp'),form(current,'fn2-rs-int-valuesp'))


if __name__=='__main__': unittest.main()
