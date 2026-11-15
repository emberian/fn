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
