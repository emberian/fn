#!/usr/bin/env python3
"""Alpha-rename the two feed predicates' forbidden Common Lisp FILL locals."""
from pathlib import Path
import re
import lisp_rewrite as lr

NAMES = ('fn2-feed-header-end-p', 'fn2-feed-header-complete-p')
TOKEN = re.compile(r'(?<![\w-])fill(?![\w-])')
BACK = re.compile(r'(?<![\w-])filled(?![\w-])')

def transform(text):
    edits = []
    parsed = lr.parse(text)
    for name in NAMES:
        matches = lr.match('(defun '+name+' ?*body)', parsed.forms)
        assert len(matches) == 1, name
        node = matches[0]
        old = text[node.start:node.end]
        if not TOKEN.search(old):
            assert '(let ((filled ' in old, name
            continue
        assert '(let ((fill ' in old and not BACK.search(old), name
        new = TOKEN.sub('filled', old)
        assert BACK.sub('fill', new) == old
        edits.append((node.start, node.end, new))
    for start, end, replacement in reversed(edits):
        text = text[:start]+replacement+text[end:]
    return text

if __name__ == '__main__':
    path = Path(__file__).resolve().parents[1]/'books/upload-feed.lisp'
    before = path.read_text()
    after = transform(before)
    assert transform(after) == after
    path.write_text(after)
