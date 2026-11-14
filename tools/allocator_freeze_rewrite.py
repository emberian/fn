"""Wrap actual allocator lifecycle entries with the shared physical freeze gate."""
from pathlib import Path
import lisp_rewrite as lr

REFUSALS = {
    'fn2-alloc-begin-epoch': '(mv :frozen fn2-extents)',
    'fn2-alloc-reserve': '(mv :frozen nil 0 0 0 fn2-extents)',
    'fn2-alloc-adopt': '(mv :frozen fn2-extents)',
    'fn2-alloc-commit-allocation': '(mv :frozen fn2-extents)',
    'fn2-alloc-retire': '(mv :frozen fn2-extents)',
    'fn2-alloc-release-code': ':frozen',
    'fn2-alloc-cancel-reservation': '(mv :frozen fn2-extents)',
    'fn2-alloc-checkpoint-drain': '(mv :frozen fn2-extents)',
}

def rewrite(text):
    edits = []
    for match in lr.match('(defun ?name ?args ?*body)', lr.parse(text).forms):
        name = match.captures['name']
        if not isinstance(name, lr.Atom) or name.text.lower() not in REFUSALS:
            continue
        body = match.captures['body'][-1]
        original = text[body.start:body.end]
        if original.startswith('(if (fn2-alloc-frozenp fn2-extents)'):
            continue
        edits.append((body.start, body.end,
                      '(if (fn2-alloc-frozenp fn2-extents)\n      ' + REFUSALS[name.text.lower()] + '\n    ' + original + ')'))
    return lr.write(text, edits)

if __name__ == '__main__':
    path = Path('books/alloc.lisp')
    path.write_text(rewrite(path.read_text()))
