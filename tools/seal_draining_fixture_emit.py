"""Emit fixture carrier class from the actual served sealer ABI."""
from pathlib import Path
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
def emit():
 source=(ROOT/'books/sealer.lisp').read_text()
 found=lr.match('(defun fn2-seal-step ?*args)',lr.parse(source).forms,deep=False)
 if len(found)!=1:raise ValueError('actual sealer step ABI')
 args=found[0].node.items[2].items
 if args[0].low!='budget':raise ValueError('sealer budget changed')
 carriers=[x.low for x in args[1:]]
 if len(carriers)!=len(set(carriers)) or len(carriers)+1>32:raise ValueError('sealer return ABI')
 range_source=(ROOT/'books/range.lisp').read_text()
 adapter=lr.match('(defconst *fn2-rga-stobjs* ?value)',lr.parse(range_source).forms,deep=False)
 if len(adapter)!=1:raise ValueError('actual range adapter ABI')
 adapter_names=[x.low for x in adapter[0].node.items[2].node.items]
 if not set(adapter_names)<=set(carriers):raise ValueError('range input absent from sealer carrier class')
 template=(ROOT/'tools/fixtures/seal-draining-sources-template.lisp').read_text()
 if template.count('@CARRIERS@')<6:raise ValueError('fixture carrier class changed')
 result=template.replace('@CARRIERS@',' '.join(carriers));lr.parse(result)
 return result
if __name__=='__main__':(ROOT/'tests/seal-draining-sources-unit.lisp').write_text(emit())
