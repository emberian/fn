"""Cache actual machine readers before borrowing release continuation children."""
import lisp_rewrite as lr
READERS = ('rc-base', 'rc-base-tag', 'rc-commit', 'rc-pos', 'rc-roff', 'rc-rend',
           'pool-slot', 'pool-gen', 'rc-wslot', 'rc-wgen')
def local(field):
    return 'actual-' + field
def rewrite(source):
    parsed = lr.parse(source)
    edits = []
    for field in READERS:
        for match in lr.match(f'(fn2-machine-{field} id fn2-core)', parsed.forms):
            n = match.node
            edits.append((n.start, n.end, local(field)))
    return lr.write(source, edits)
def bindings():
    return '\n'.join(f'({local(field)} (fn2-machine-{field} id fn2-core))' for field in READERS)
