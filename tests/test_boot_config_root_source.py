"""State extraction controls only; bootstrap producer/runtime is still owed."""
from pathlib import Path
import sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as lr
from boot_config_root_rewrite import project
def columns(text):
    fs=lr.match('(defcolumns fn2-boot-config ?*body)',lr.parse(text).forms,deep=False)
    if len(fs)!=1:raise ValueError('one actual config')
    f=fs[0].node
    for i,x in enumerate(f.items):
        if getattr(x,'low','')==':extra-fields':
            return {x.items[0].low:lr.flat(x) for x in f.items[i+1].items}
    raise ValueError('fields')
class BootConfig(unittest.TestCase):
    def test_all_original_fields_identical(self):
        before=columns((ROOT/'tools/fixtures/boot-config-root-before.lisp').read_text())
        after=columns((ROOT/'books/boot-config-state.lisp').read_text())
        self.assertEqual(len(before),7)
        for key,value in before.items():self.assertEqual(after[key],value)
    def test_one_lower_declaration_and_old_boot_functions_preserved(self):
        kind=(ROOT/'books/boot-kind.lisp').read_text()
        self.assertEqual(project(kind),kind)
        self.assertNotIn('(defcolumns fn2-boot-config ',kind)
        self.assertIn('(include-book "boot-config-state")',kind)
        before=(ROOT/'tools/fixtures/boot-config-root-before.lisp').read_text()
        synthetic='(in-package "ACL2")\n(fn2-book-layer :b)\n'+before+'\n(defun retained (x) x)\n'
        moved=project(synthetic)
        self.assertIn('(defun retained (x) x)',moved)
        self.assertNotIn('(defcolumns fn2-boot-config ',moved)
    def test_unminted_receipt_defaults_and_namespace_fields(self):
        fields=columns((ROOT/'books/boot-config-state.lisp').read_text())
        for key in ('owner-kind','owner-slot','owner-gen','domain','lineage',
                    'incarnation','history','history-incarnation'):
            self.assertIn(':initially 0',fields['fn2-boot-config-bootstrap-'+key])
        geometry=(ROOT/'books/boot-geometry-state.lisp').read_text()
        self.assertIn('(fn2-checkpoint-boot-geometry-copy 0 row',geometry)
        self.assertNotIn('update-fn2-boot-config-bootstrap-',geometry)
if __name__=='__main__':unittest.main()
