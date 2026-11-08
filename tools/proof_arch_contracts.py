"""Remove view-by-callee proof traversal; consume producer footprints in hints.

The shared Lisp reader owns spans. Theorem statements are never edited.
Legacy generated statements are checked separately against the new contracts.
"""
from pathlib import Path
import argparse
import re
import lisp_rewrite as lr
from proof_arch_views import walk

REL = re.compile(r'.+-fn2-env-(ek|rk|tk|sk|ok|fk|dk)$')
KEPT = {'-keeps-commit-io': 'fn2-env-io-view',
        '-keeps-commit-root': 'fn2-env-root-table-view',
        '-keeps-commit-table': 'fn2-env-commit-table-view',
        '-keeps-directory': 'fn2-env-directory-view'}
DROP = {'fn2-env-rel-callee-runes', 'fn2-env-rel-nth-uses', 'fn2-env-rel-event',
        'fn2-env-rel-forms', 'fn2-env-keep-name', 'fn2-env-keep-callee-runes',
        'fn2-env-keep-event', 'fn2-env-keep-forms'}


def head(node):
    return node.items[0].low if isinstance(node, lr.Lst) and node.items and isinstance(node.items[0], lr.Atom) else None


def legacy_view(name):
    match = REL.fullmatch(name)
    if match:
        return 'fn2-env-' + match[1]
    if not name.startswith('fn2-env-'):
        return next((view for suffix, view in KEPT.items() if name.endswith(suffix)), None)
    return None


def dynamic_views(node):
    n = node.node if isinstance(node, lr.Pre) else node
    if head(n) not in ('fn2-env-rel-name', 'fn2-env-rel-callee-runes'):
        return set()
    return {x.low for x in walk(n) if isinstance(x, lr.Atom) and x.low in
            {'fn2-env-' + s for s in ('ek', 'rk', 'tk', 'sk', 'ok', 'fk', 'dk')}}


def filter_hints(source, node, views):
    if isinstance(node, lr.Atom) and legacy_view(node.low):
        views.add(legacy_view(node.low))
        return None
    dynamic = dynamic_views(node)
    if dynamic:
        views.update(dynamic)
        return None
    if head(node) == ':instance' and len(node.items) > 1 and isinstance(node.items[1], lr.Atom):
        view = legacy_view(node.items[1].low)
        if view:
            views.add(view)
            return None
    children = node.items if isinstance(node, lr.Lst) else [node.node] if isinstance(node, lr.Pre) else []
    edits = []
    for index, child in enumerate(children):
        replacement = filter_hints(source, child, views)
        if replacement is None and index and isinstance(children[index-1], lr.Atom):
            keyword = children[index-1].low
            if keyword == ':use':
                replacement = 'nil'
            elif keyword == ':by':
                raise ValueError('A legacy :by proof needs an explicit replacement')
        old = source[child.start:child.end]
        if replacement != old:
            edits.append((child.start-node.start, child.end-node.start, replacement or ''))
    return lr.write(source[node.start:node.end], edits)


def add_projection_hint(hints, views, *, direct=False):
    names = ' '.join(sorted(views))
    computed = f"(and stable-under-simplificationp (fn2-column-view-hint '({names}) clause world))"
    opened = ' '.join(sorted(views & set(KEPT.values())))
    base = (f"(union-theories '({opened}) (theory 'fn2-column-projection-base))"
            if opened else "(theory 'fn2-column-projection-base)")
    if direct:
        return f'(("Goal" :do-not-induct t :in-theory {base})\n         {computed})'
    form = lr.parse(hints).forms[0]
    if not isinstance(form, lr.Lst):
        raise ValueError('Expected a literal hint list')
    edits = []
    for n in walk(form):
        if not isinstance(n, lr.Lst):
            continue
        for left, right in zip(n.items, n.items[1:]):
            if isinstance(left, lr.Atom) and left.low == ':in-theory':
                old = hints[right.start:right.end]
                edits.append((right.start, right.end, f'(union-theories {base} {old})'))
    if not edits:
        # Do not introduce a second common Goal hint: extend the existing one.
        goal = next((n for n in form.items if isinstance(n, lr.Lst) and n.items
                     and isinstance(n.items[0], lr.Str) and n.items[0].text.lower() == '"goal"'), None)
        if goal is None:
            raise ValueError('No common Goal hint to extend')
        edits.append((goal.end-1, goal.end-1, f' :in-theory {base}'))
    edits.append((form.end-1, form.end-1, '\n         '+computed))
    return lr.write(hints, edits)


def clean_layout(source):
    strings = [(n.start,n.end) for top in lr.parse(source).forms for n in walk(top) if isinstance(n,lr.Str)]
    edits = [(m.start(),m.end(),'') for m in re.finditer(r'[ \t]+(?=\n)',source)
             if not any(a <= m.start() < b for a,b in strings)]
    return lr.write(source,edits)


def seed_consumers(source):
    """Give each consumer its visible producer facts before reader splitting."""
    edits = []
    def visit(node):
        if head(node) == 'fn2-with-column-projections':
            return
        if head(node) == 'defthm':
            views = set()
            for hint in walk(node):
                if head(hint) == 'fn2-column-view-hint':
                    views.update(n.low for n in walk(hint.items[1])
                                 if isinstance(n, lr.Atom) and n.low.startswith('fn2-env-'))
            if views:
                text = source[node.start:node.end]
                edits.append((node.start, node.end,
                              '(fn2-with-column-projections (' + ' '.join(sorted(views)) + ')\n' + text + ')'))
            return
        for child in node.items if isinstance(node, lr.Lst) else [node.node] if isinstance(node, lr.Pre) else []:
            visit(child)
    for form in lr.parse(source).forms:
        visit(form)
    return lr.write(source, edits)


def migrate(source):
    # First remove producer/view traversal itself, including nested generated events.
    parsed = lr.parse(source)
    edits = []
    def visit(node):
        h = head(node)
        if h == 'defun' and len(node.items) > 1 and node.items[1].low in DROP:
            edits.append((node.start, node.end, ''))
            return
        if h == 'table' and len(node.items) > 1 and node.items[1].low == 'fn2-env-rel-cols':
            edits.append((node.start, node.end, ''))
            return
        if h == 'make-event' and any(head(n) in ('fn2-env-rel-forms', 'fn2-env-keep-forms') for n in walk(node)):
            edits.append((node.start, node.end, ''))
            return
        for child in node.items if isinstance(node, lr.Lst) else [node.node] if isinstance(node, lr.Pre) else []:
            visit(child)
    for form in parsed.forms:
        visit(form)
    source = lr.write(source, edits)
    edits = []
    for top in lr.parse(source).forms:
        for theorem in walk(top):
            if head(theorem) != 'defthm':
                continue
            hints = next((b for a,b in zip(theorem.items, theorem.items[1:])
                          if isinstance(a, lr.Atom) and a.low == ':hints'), None)
            if hints is None:
                continue
            name = theorem.items[1]
            direct_view = legacy_view(name.low) if isinstance(name, lr.Atom) and REL.fullmatch(name.low) else None
            views = {direct_view} if direct_view else set()
            filtered = filter_hints(source, hints, views)
            if views:
                replacement = add_projection_hint(filtered, views, direct=bool(direct_view))
                edits.append((hints.start, hints.end, replacement))
    source = lr.write(source, edits)
    # The quiet-arm traversal carried a callee list used only by its old hints.
    edits = []
    for top in lr.parse(source).forms:
        if head(top) != 'defun':
            continue
        for name in ('glue', 'arm'):
            atoms = [n for n in walk(top) if isinstance(n, lr.Atom) and n.low == name]
            if len(atoms) == 1:
                binding = next((n for n in walk(top) if head(n) == name), None)
                if binding is not None:
                    edits.append((binding.start, binding.end, ''))
    return seed_consumers(clean_layout(lr.write(source, edits)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('path', type=Path)
    args = parser.parse_args()
    source = args.path.read_text()
    args.path.write_text(migrate(source))
