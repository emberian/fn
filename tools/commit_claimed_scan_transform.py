"""One structural transformation for the actual scanner declaration/call class."""
import lisp_rewrite as lr


def transform(source):
    edits = []
    def walk(n):
        if isinstance(n, lr.Lst):
            if n.items:
                h = getattr(n.items[0], 'text', '')
                if h == 'defun' and len(n.items)>2 and getattr(n.items[1], 'text', '') == 'fn2-commit-txn-scan':
                    edits.append((n.items[1].start,n.items[1].end,'fn2-commit-txn-scan-claimed'))
                    last = n.items[2].items[-1]
                    assert last.text == 'fn2-core'
                    edits.append((last.start,last.start,'tx txgen '))
                elif h == 'fn2-commit-txn-scan':
                    edits.append((n.items[0].start,n.items[0].end,'fn2-commit-txn-scan-claimed'))
                    last = n.items[-1]
                    assert last.text == 'fn2-core'
                    edits.append((last.start,last.start,'tx txgen '))
            for child in n.items: walk(child)
        elif isinstance(n, lr.Pre): walk(n.node)
    for form in lr.parse(source).forms: walk(form)
    for start,end,value in sorted(edits,reverse=True): source=source[:start]+value+source[end:]
    return source
