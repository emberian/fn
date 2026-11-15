"""Emit one original carrier-contract event per actual index operation."""
from pathlib import Path
import lisp_rewrite as lr
PATTERN="(make-event (cons 'progn (fn2-alloc-identity-shape-events '?signatures)))"
def rewrite(source):
 parsed=lr.parse(source)
 matches=lr.match(PATTERN,parsed.forms,deep=False)
 if not matches:
  return source
 if len(matches)>1:
  if all(len(m.node.items[1].items[2].items[1].node.items)==1 for m in matches):return source
  raise ValueError('ambiguous identity shape package')
 match=matches[0]
 # The sole signature list is literal source; no Lisp evaluation occurs.
 form=match.node
 quote=form.items[1].items[2].items[1]
 signatures=quote.node
 if not isinstance(signatures,lr.Lst) or not signatures.items:raise ValueError('expected literal signatures')
 pieces=["(make-event (cons 'progn (fn2-alloc-identity-shape-events '("+lr.flat(sig)+"))))" for sig in signatures.items]
 return source[:form.start]+'\n'.join(pieces)+source[form.end:]
if __name__=='__main__':
 p=Path('books/alloc-identity-index.lisp');p.write_text(rewrite(p.read_text()))
