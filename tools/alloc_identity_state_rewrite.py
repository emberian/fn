"""Rename the reserved ACL2 STATE variable in the isolated identity leaf.

All STATE atoms in this named source are reviewed local/formal parameters,
including the corresponding quoted signature data. Not a general alpha-renamer.
"""
from pathlib import Path
import lisp_rewrite as lr

def rewrite(source):
    parsed=lr.parse(source)
    edits=[]
    def walk(node):
        if isinstance(node,lr.Atom):
            if node.low=='state': edits.append((node.start,node.end,'row-state'))
        elif isinstance(node,lr.Lst):
            for child in node.items: walk(child)
        elif hasattr(node,'value'): walk(node.value)
        elif hasattr(node,'node'): walk(node.node)
    for form in parsed.forms:walk(form)
    for start,end,value in reversed(sorted(edits)):source=source[:start]+value+source[end:]
    lr.parse(source)
    return source
if __name__=='__main__':
    p=Path('books/alloc-identity-index.lisp');p.write_text(rewrite(p.read_text()))


def rewrite_projection(source):
    """Rename lexical STATE in the two actual projection functions only.

    Extent PUT field names are schema keys, never lexical variables.
    """
    parsed=lr.parse(source)
    edits=[]
    names={'fn2-checkpoint-projection-identity-step','fn2-checkpoint-projection-step'}
    def walk(node):
        if isinstance(node,lr.Atom):
            if node.low=='state': edits.append((node.start,node.end,'row-state'))
        elif isinstance(node,lr.Lst):
            if node.items and isinstance(node.items[0],lr.Atom) and node.items[0].low=='fn2-extents-put':
                for child in node.items[:2]: walk(child)
                for field in node.items[2:]:
                    if not isinstance(field,lr.Lst): raise ValueError('changed extent PUT field')
                    for value in field.items[1:]: walk(value)
            else:
                for child in node.items: walk(child)
        elif hasattr(node,'value'): walk(node.value)
        elif hasattr(node,'node'): walk(node.node)
    for form in parsed.forms:
        if isinstance(form,lr.Lst) and len(form.items)>1 and isinstance(form.items[0],lr.Atom) and form.items[0].low=='defun' and isinstance(form.items[1],lr.Atom) and form.items[1].low in names:
            walk(form)
    for start,end,value in reversed(sorted(edits)):source=source[:start]+value+source[end:]
    lr.parse(source)
    return source
