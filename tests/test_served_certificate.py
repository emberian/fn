"""Controls for the generated coverage boundary; proof gates run separately."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT=Path(__file__).parents[1]
def module(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'meta/emit'/(name+'.py'))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
c=module('check_served_certificate')
e=module('emit_served_certificate')

class CoverageControls(unittest.TestCase):
    def test_proposals_never_count(self):
        report={'functions':[{'name':'F','canonical_export':'proposed'}],
          'roots':[{'name':'ARM','status':'unvalidated','reason':'not checked'}], 'unresolved':['MISSING']}
        text=c.summary(report)
        self.assertIn('0/1 validated',text)
        for name in ['F:','ARM:','MISSING:']: self.assertIn(name,text)

    def test_census_is_named_and_rejects_extra_axioms(self):
        self.assertTrue(c.census("'N.validated' depends on axioms: [propext, Quot.sound]",'N.validated'))
        self.assertFalse(c.census("'Other.validated' does not depend on any axioms",'N.validated'))
        for extra in ['sorryAx','UnprovedContract']:
            self.assertFalse(c.census("'N.validated' depends on axioms: ["+extra+"]",'N.validated'))

    def test_stale_body_and_package_invalidate_coverage(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);p=root/'package';p.write_text('package')
            b=root/'proof';b.write_text('checked body')
            report={'package':'package','package_sha256':e.digest(p),'inputs':{'proof':e.digest(b)},
              'roots':[],'functions':[]}
            c.current(report,root)
            b.write_text('altered body')
            with self.assertRaisesRegex(ValueError,'input changed'):c.current(report,root)
            b.write_text('checked body');p.write_text('different attachment')
            with self.assertRaisesRegex(ValueError,'package changed'):c.current(report,root)

    def test_duplicate_root_cannot_inflate_denominator(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);p=root/'package';p.write_text('package')
            report={'package':'package','package_sha256':e.digest(p),'inputs':{},
              'roots':[{'name':'F'},{'name':'F'}],'functions':[]}
            with self.assertRaisesRegex(ValueError,'duplicate roots'):c.current(report,root)

    def test_missing_function_record_is_not_ignored(self):
        with self.assertRaisesRegex(ValueError,'function count'):
            list(e.function_records([],1))

    def test_packed_symbol_keeps_package_and_name(self):
        obj=e.read_canonical('(:SYMBOL (65 67 76 50) (70 79 79))')
        self.assertEqual(e.packed_text(obj),'(:PACKED-SYMBOL "ACL2" "FOO")')
        obj=e.read_canonical('(:SYMBOL (65) (34 92))')
        self.assertEqual(e.packed_text(obj),'(:PACKED-SYMBOL "A" "\\"\\\\")')

    def test_list_constant_keeps_every_element(self):
        value=e.alist_value(e.List([e.Atom('K'),e.Atom('1'),e.Atom('2'),e.Atom('3')]))
        self.assertEqual(value,e.List([e.Atom('1'),e.Atom('2'),e.Atom('3')]))

if __name__=='__main__':unittest.main()
