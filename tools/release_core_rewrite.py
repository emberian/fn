"""Apply release-owned core registration to the exact existing B declarations."""
from pathlib import Path
import lisp_rewrite as lr

def one(source, head, name):
    matches = lr.match(f'({head} {name} ?*body)', lr.parse(source).forms, deep=False)
    if len(matches) != 1:
        raise ValueError(f'expected one {head} {name}')
    return matches[0].node

def transform(source, exports):
    if '(include-book "release-allocation-state")' in source:
        raise ValueError('release registration already present')
    anchor = '(include-book "checkpoint-lifecycle-coordinator")'
    if source.count(anchor) != 1:
        raise ValueError('expected lifecycle include')
    source = source.replace(anchor, anchor + '\n(include-book "release-allocation-state")\n(include-book "release-evidence-state")')
    edits = []
    for head, name in [('defun', 'fn2-b-alloc-edge-floor'), ('defcorechild', 'fn2-core-alloc-edges')]:
        old, new = one(source, head, name), one(exports, head, name)
        edits.append((old.start, old.end, exports[new.start:new.end]))
    old = one(source, 'defcorechild', 'fn2-core-retirement-control')
    new = one(exports, 'defcorechild', 'fn2-core-allocation-release')
    edits.append((old.end, old.end, '\n' + exports[new.start:new.end]))
    old = one(source, 'defcorechild', 'fn2-core-alloc-edges')
    additions = []
    for name in ['fn2-core-release-evidence', 'fn2-core-release-evidence-candidates']:
        n = one(exports, 'defcorechild', name)
        additions.append(exports[n.start:n.end])
    edits.append((old.end, old.end, '\n' + '\n'.join(additions)))
    source = lr.write(source, edits)
    return source.replace('; of the same derived size. These are dedicated resident resources.',
        '; of the same derived size, then two release-evidence obligations per journal\n; extent. The shared layout checks profile overflow. These are resident resources.')

if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    path = root / 'books/machines-b.lisp'
    path.write_text(transform(path.read_text(), (root / 'tools/fixtures/release-core-registration.lisp').read_text()))
