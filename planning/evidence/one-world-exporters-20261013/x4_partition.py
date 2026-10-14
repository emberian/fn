"""Derive shared imports from ordered include graphs and structural export masks.

Book-level ownership projection only: this script does not calculate ACL2
enabled rune sets. Certified rune measurements remain the acceptance test.
LOCAL includes/events are excluded, as in r5_paths.py's edge reader.
"""
from pathlib import Path
import argparse
import hashlib
import json
import posixpath
import subprocess
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'tools'))
import lisp_rewrite as lr

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent

def head(node):
    return getattr(node.items[0], 'text', '').lower() if hasattr(node, 'items') and node.items else ''

def quoted(node):
    return getattr(getattr(node, 'node', None), 'text', '').lower()

def reference_names(node, kind):
    found = set()
    def walk(n):
        if head(n) == kind and len(n.items) == 2:
            found.add(quoted(n.items[1]))
        if hasattr(n, 'items'):
            for c in n.items:
                walk(c)
    walk(node)
    return found - {''}

def stream(book, source):
    events = []
    def walk(n):
        h = head(n)
        line = source[:n.start].count('\n') + 1
        if h == 'local':
            return
        if h == 'encapsulate':
            for c in n.items[2:]:
                walk(c)
        elif h == 'include-book':
            arg = getattr(n.items[1], 'text', '')
            if arg.startswith('"') and ':dir' not in source[n.start:n.end].lower():
                dest = posixpath.normpath(str(Path(book).parent / (arg[1:-1] + '.lisp')))
                events.append(('include', dest, line))
        elif h == 'deftheory' and head(n.items[2]) == 'current-theory':
            events.append(('snapshot', n.items[1].text.lower(), line))
        elif h == 'in-theory':
            before = reference_names(n, 'theory')
            after = reference_names(n, 'universal-theory')
            if before and after:
                events.append(('mask', (sorted(before), sorted(after)), line))
    for n in lr.parse(source).forms:
        walk(n)
    return events

def closure(roots, graph, cut=()):
    seen, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in seen or n in cut:
            continue
        seen.add(n)
        todo.extend(graph.get(n, []))
    return seen

def first_path(start, target, graph, cut):
    seen = set()
    def visit(book, path):
        if book in cut or book in seen:
            return None
        if book == target:
            return path
        seen.add(book)
        for child in graph.get(book, []):
            result = visit(child, path + [(book, child)])
            if result is not None:
                return result
        return None
    return visit(start, [])

def projection(root, streams, cut, boundaries):
    """Preserve first-load ordering and named before/after export boundaries."""
    loaded, visible = set(), set()
    def visit(book):
        nonlocal visible
        if book in cut or book in loaded:
            return
        loaded.add(book)
        visible.add(book)
        snapshots = {}
        for kind, arg, line in streams.get(book, []):
            if kind == 'include':
                visit(arg)
            elif kind == 'snapshot':
                snapshots[arg] = (set(loaded), set(visible))
            elif kind == 'mask':
                befores, afters = arg
                pairs = [(b,a) for b in befores for a in afters
                         if b in snapshots and a in snapshots and snapshots[b][0] <= snapshots[a][0]]
                if len(pairs) != 1:
                    raise ValueError((book, line, 'ambiguous structural mask', pairs))
                before, after = pairs[0]
                old_loaded, old_visible = snapshots[before]
                end_loaded, _ = snapshots[after]
                hidden = end_loaded - old_loaded
                visible = old_visible | (visible - end_loaded)
                boundaries[(book, line)] = {'book': book, 'line': line,
                    'before': before, 'after': after, 'hidden_books': sorted(hidden)}
    visit(root)
    return loaded, visible

def fixtures():
    sources = {
        'books/exporter.lisp': '(include-book "shared") (deftheory before (current-theory :here)) (include-book "private") (deftheory after (current-theory :here)) (in-theory (union-theories (theory \'before) (set-difference-theories (current-theory :here) (universal-theory \'after))))',
        'books/client.lisp': '(include-book "exporter") (include-book "private")',
        'books/first.lisp': '(include-book "private") (include-book "exporter")',
        'books/shared.lisp': '', 'books/private.lisp': ''}
    streams = {b: stream(b,s) for b,s in sources.items()}
    loaded, visible = projection('books/client.lisp', streams, (), {})
    assert 'books/private.lisp' in loaded and 'books/private.lisp' not in visible
    assert 'books/shared.lisp' in visible
    assert 'books/private.lisp' in projection('books/first.lisp', streams, (), {})[1]
    assert not stream('books/local.lisp', '(local (include-book "private"))')

def main(apply=False):
    fixtures()
    revision = subprocess.check_output(['git','-C',str(ROOT),'rev-parse','origin/dev'], text=True).strip()
    names = subprocess.check_output(['git','-C',str(ROOT),'ls-tree','-r','--name-only',revision,'books'],text=True).splitlines()
    sources, streams, dev_graph = {}, {}, {}
    for name in names:
        if not name.endswith('.lisp'):
            continue
        source = subprocess.check_output(['git','-C',str(ROOT),'show',revision+':'+name],text=True)
        sources[name] = source
        streams[name] = stream(name,source)
        dev_graph[name] = [arg for kind,arg,line in streams[name] if kind == 'include']
    graph = {}
    def lane_closure(book):
        if book in graph:
            return
        source = (ROOT/book).read_text()
        graph[book] = [arg for kind,arg,line in stream(book,source) if kind == 'include']
        for child in graph[book]:
            lane_closure(child)
    implementation, generic, foundation = 'books/history-paged.lisp', 'books/history-columns.lisp', 'books/history-columns-foundation.lisp'
    lane_closure(implementation)
    impl = closure([implementation], graph)
    baseline = closure([foundation], graph)
    ancestors = {generic}
    while True:
        more = {b for b,cs in dev_graph.items() if any(c in ancestors for c in cs)} - ancestors
        if not more:
            break
        ancestors |= more
    consumers = sorted(ancestors - {generic})
    boundaries, visible_any, witnesses = {}, set(), {}
    for consumer in consumers:
        _, visible = projection(consumer, streams, (generic,implementation), boundaries)
        visible_any |= visible
        for book in sorted(visible & (impl-baseline)):
            witnesses.setdefault(book, consumer)
    shared = (impl-baseline) & closure(consumers,dev_graph,(generic,implementation))
    projected_shared = (impl-baseline) & visible_any
    assert shared == projected_shared, ("literal and export-boundary graphs disagree", sorted(shared ^ projected_shared))
    private = impl - baseline - shared
    # Maximal shared books cover their shared children without importing a private book.
    eligible = {b for b in shared if not (closure([b],graph) & private)}
    covered_by_parent = set()
    for book in eligible:
        covered_by_parent |= (closure([book],graph)-{book}) & eligible
    imports = sorted(eligible - covered_by_parent)
    covered = closure(imports, graph)
    assert shared <= covered, ('shared books lack a private-free include frontier',sorted(shared-covered))
    assert not (covered & private), 'frontier imports private implementation books'
    literal = (impl-baseline) & closure(consumers,dev_graph,(generic,implementation))
    paths = {}
    for book in sorted(shared):
        path = first_path(witnesses[book], book, dev_graph, (generic,implementation))
        assert path is not None, (book, 'missing independent witness path')
        paths[book] = [{'from': parent, 'line': next(line for kind,arg,line in streams[parent] if kind == 'include' and arg == child), 'to': child}
                       for parent, child in path]
    result = {'dev_revision': revision, 'method': 'non-LOCAL include graph; independent dev-consumer reachability after cutting the generic and implementation roots; export-boundary projection is a matching cross-check, not rune evidence',
        'implementation_root': implementation, 'generic_boundary': generic,
        'existing_foundation_baseline': sorted(baseline), 'implementation_closure': sorted(impl),
        'dev_consumers': consumers, 'shared': sorted(shared), 'private': sorted(private),
        'include_frontier': imports, 'shared_consumer_witness': witnesses,
        'independent_include_path_for_shared': paths,
        'source_detected_export_masks': list(boundaries.values()),
        'literal_graph_shared_without_masks': sorted(literal), 'partition_matches_literal_graph': shared == literal,
        'fixtures': 'PASS: masked include, redundant include after mask, dependency before mask, LOCAL exclusion'}
    (OUT/'x4-partition.json').write_text(json.dumps(result,indent=2)+'\n')
    lines = ['X4 source-derived partition', 'origin/dev: '+revision,
        'book-level ownership projection; certified enabled-rune measurements remain owed',
        'existing baseline: '+str(len(baseline)), 'implementation closure: '+str(len(impl)),
        'SHARED: '+str(len(shared)), *sorted(shared), 'PRIVATE: '+str(len(private)), *sorted(private),
        'GENERATED INCLUDE FRONTIER: '+str(len(imports)), *imports,
        'SOURCE-DETECTED EXPORT MASKS: '+str(len(boundaries))]
    for mask in boundaries.values():
        lines.append(mask['book']+':'+str(mask['line'])+' '+mask['before']+' / '+mask['after'])
    (OUT/'x4-partition.txt').write_text('\n'.join(lines)+'\n')
    include_text = ''.join('(include-book "'+book[len('books/'):-len('.lisp')]+'")\n' for book in imports)
    (OUT/'x4-shared-includes.lisp').write_text(include_text)
    if apply:
        path = ROOT/generic
        source = path.read_text()
        marker = '(deftheory fn-hist-theory-before-paged (current-theory :here))'
        assert source.count(marker) == 1
        block = '; Shared dependency frontier generated by build/vertical-runs/one-world/x4_partition.py.\n'+include_text+'\n'
        label = '; Shared dependency frontier generated by build/vertical-runs/one-world/x4_partition.py.\n'
        if label in source:
            start, end = source.index(label), source.index(marker)
            old = source[start+len(label):end]
            assert all(head(n) == 'include-book' for n in lr.parse(old).forms)
            path.write_text(source[:start] + block + source[end:])
        elif block not in source:
            path.write_text(source.replace(marker,block+marker))
    print('fixtures PASS; closure '+str(len(impl))+', baseline '+str(len(baseline))+', shared '+str(len(shared))+', private '+str(len(private)))
    print('generated include frontier: '+', '.join(imports))
    print('export masks: '+', '.join(m['book']+':'+str(m['line']) for m in boundaries.values()))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--apply', action='store_true')
    main(parser.parse_args().apply)
