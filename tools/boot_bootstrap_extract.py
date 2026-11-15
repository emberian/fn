"""Extract the existing bootstrap codec producer with an explicit owner kind.

Instantiating KIND with the original BOOT constant restores each original
function body/guard. No second encoding or hash implementation is introduced.
"""
from pathlib import Path
import json
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[1]
GENERIC = ('fn2-boot-pack-geometry', 'fn2-boot-bootstrap-pool', 'fn2-boot-save-geometry')


def nodes(n):
    yield n
    if isinstance(n, lr.Lst):
        for child in n.items:
            yield from nodes(child)
    elif isinstance(n, lr.Pre):
        yield from nodes(n.node)


def generic_owner(source):
    edits = []
    for form in lr.parse(source).forms:
        if not isinstance(form, lr.Lst) or getattr(form.items[0], 'low', None) != 'defun':
            continue
        name = form.items[1].low
        if name not in GENERIC:
            continue
        args = form.items[2].items
        i = next(n for n in args if getattr(n, 'low', None) == 'id')
        edits.append((i.start, i.start, 'kind '))
        for n in nodes(form):
            if isinstance(n, lr.Atom) and n.low == '*fn2-boot-kind*':
                edits.append((n.start, n.end, 'kind'))
            if isinstance(n, lr.Lst) and n.items and getattr(n.items[0], 'low', None) == name:
                # The only recursive helper is save-geometry, whose owner
                # position is the same as its actual declared formal.
                at = n.items[1 + args.index(i)]
                edits.append((at.start, at.start, 'kind '))
    return lr.write(source, edits)


def producer(source):
    generic = generic_owner(source)
    bootstrap = lr.match('(defun fn2-boot-bootstrap-pool ?*body)', lr.parse(generic).forms)[0].node
    body = lr.match('(b* ?bindings ?*result)', [bootstrap])[0].captures['bindings']
    assert len(body.items) >= 2
    a, b = body.items[:2]
    assert 'fn2-pool-reset' in generic[a.start:a.end]
    assert '(unless (eq code :ok))' in generic[b.start:b.end]
    # Reset is owned by the image producer. The encoder must preserve its
    # geometry source at sector+0 in the same 64KiB owned page.
    generic = lr.write(generic, [(bootstrap.items[1].start, bootstrap.items[1].end,
                                 'fn2-boot-bootstrap-encode-pool'),
                                (a.start, b.end, '')])
    return '''; Canonical bootstrap construction, independent of BOOT registration.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "boot-pack")
(include-book "checkpoint-geometry")
(include-book "boot-config-state")
(include-book "pool-ranges")
(fn2-book-layer :b)

'''+generic


if __name__ == '__main__':
    before = json.loads((ROOT/'tools/fixtures/boot-bootstrap-producer-before.json').read_text())
    (ROOT/'books/boot-bootstrap-pack.lisp').write_text(producer(before['source']))
