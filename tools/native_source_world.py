#!/usr/bin/env python3
"""Emit the current native logical world as ordinary, resumable ACL2 source.

A matching certificate is an input optimization, never the verdict for source
admission. Changed books keep their local proof scope. Generic books own
their implementation include and preceding attachment in every source world.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path
import certs
import proof_repl
from proof_repl import encapsulated, forms, head_and_name

EARLY = ('books/codec-attach', 'books/records-attach-concrete',
         'books/payload-arena', 'books/history-columns')


def event_head(form):
    # head_and_name intentionally unwraps LOCAL for event selection, which is
    # inappropriate for deciding whether proof inputs escape their scope.
    match = re.match(r'\(\s*([^\s()]+)', form.strip())
    return match.group(1).lower() if match else ''


def exported_includes(text, directory):
    """Literal nonlocal dependencies; LOCAL proof inputs are not exports."""
    found = []
    def event(form):
        head = event_head(form)
        target = proof_repl.include_target(form, directory) if head == 'include-book' else None
        if target is not None:
            found.append(target)
            return
        if head == 'local':
            return
        if head in {'encapsulate', 'progn', 'progn!', 'with-prover-step-limit', 'with-prover-time-limit'}:
            children = forms(form.strip()[1:-1])
            start = 2 if head in {'encapsulate', 'with-prover-step-limit', 'with-prover-time-limit'} else 1
            for child in children[start:]: event(child)
    for form in forms(text): event(form)
    return found


def selected_defthms(text, deferred, removed, theory_deferred=None, pruned=None):
    theory_deferred = theory_deferred or set()
    pruned = pruned if pruned is not None else {}
    result = []
    for form in forms(text):
        head, name = head_and_name(form)
        if head == 'defthm' and name in deferred:
            if any(part in name for part in ('{', 'guard-thm', 'correspondence')):
                raise ValueError('required guard/abstract obligation cannot be deferred: ' + name)
            removed.add(name)
            continue
        if head == 'deftheory' and theory_deferred:
            # A theory catalog cannot name omitted rules. Only a literal
            # quoted catalog is adjusted; definitions and guard events stay.
            match = re.fullmatch(r"(\(deftheory\s+\S+\s+)'(\([\s\S]*\))\s*\)", form, re.I)
            if match:
                kept, omitted = [], []
                for entry in forms(match[2][1:-1]):
                    atoms = forms(entry[1:-1]) if entry.startswith('(') else []
                    target = atoms[1].lower() if len(atoms) > 1 else entry.lower()
                    if target in theory_deferred: omitted.append(target)
                    else: kept.append(entry)
                if omitted:
                    form = match[1] + "'(" + ' '.join(kept) + '))'
                    pruned[name] = sorted(set(omitted))
        if head in {'local', 'encapsulate', 'progn', 'with-prover-step-limit', 'with-prover-time-limit'}:
            inner = form.strip()[1:-1]
            spans = proof_repl.spans(inner)
            start = 2 if head in {'encapsulate', 'with-prover-step-limit', 'with-prover-time-limit'} else 1
            changes = []
            for begin, end in spans[start:]:
                replacement = selected_defthms(inner[begin:end], deferred, removed, theory_deferred, pruned)
                if replacement != inner[begin:end]: changes.append((begin, end, replacement))
            for begin, end, replacement in reversed(changes):
                inner = inner[:begin] + replacement + inner[end:]
            if head == 'local' and len(spans) == 2 and not forms(inner[spans[1][0]:]):
                continue
            form = '(' + inner + ')'
        result.append(form)
    return '\n'.join(result)


def bounded_body(body, steps):
    if not body or not steps: return body
    inner = body.strip()[1:-1]
    spans = proof_repl.spans(inner)
    prefix = inner[:spans[1][1]]
    events = [inner[begin:end] for begin, end in spans[2:]]
    # Ordinary with-prover-step-limit is an embedded event; the ! form is not.
    return '(' + prefix + '\n' + '\n'.join(
        '(with-prover-step-limit ' + str(steps) + ' ' + event + ')' 
        for event in events) + '\n)'


def admission_forms(text, directory, available, limit):
    """Preserve LOCAL scope without replaying a generic under later type rules.

    ACL2's extra ENCAPSULATE pass can recompute an abstract export's type
    using the generic's later theorems and fail a type-prescription assertion.
    If its preceding attachment/introduction prefix has no LOCAL events,
    admit that prefix once, then encapsulate the remaining proof events.
    Prefixes with LOCAL witnesses retain their original common scope.
    """
    original = forms(text)
    attached = set()
    boundary = None
    for index, form in enumerate(original):
        head, name = head_and_name(form)
        if head == 'attach-stobj':
            # head_and_name names defining events only; ATTACH-STOBJ is a
            # table event, so read its generic argument from the source form.
            arguments = forms(form.strip()[1:-1])
            if len(arguments) == 3:
                attached.add(arguments[1].lower())
        elif head in {'defabsstobj', 'def-generic'} and name in attached:
            boundary = index + 1
            break
    if boundary is not None and not any(event_head(f) == 'local' for f in original[:boundary]):
        before, after = original[:boundary], original[boundary:]
        hoisted, prefix = [], []
        for form in before:
            if event_head(form) == 'in-package': continue
            if event_head(form) in proof_repl.HOISTED_HEADS: hoisted.append(form)
            else: prefix.append(proof_repl.wrap_limit(form, limit))
        tail_hoisted, tail = encapsulated('\n'.join(after), directory, available, limit)
        # Source includes were already expanded in order by scoped_events.
        return hoisted + tail_hoisted, prefix + ([tail] if tail else [])
    hoisted, body = encapsulated(text, directory, available, limit)
    return hoisted, [body] if body else []


def generate(source: Path, caches: list[Path], output: Path, limit=25.0,
             revision=None, deferred=None, steps=200000, world_book='books/image-world',
             installed_books=None):
    source = source.resolve()
    world_book = proof_repl.normalize_book(world_book)
    deferred = deferred or {}
    removed = {}
    theory_pruned = {}
    all_deferred = {name for names in deferred.values() for name in names}
    caches = [p.resolve() for p in caches]
    proof_repl.ROOT = source
    graph = certs.include_graph(source, [world_book, *EARLY])
    # Explicit source-session admission: the caller has installed exact
    # certificates in the execution tree without loading them. ACL2 still
    # checks each include; this does not claim a local certificate exists.
    installed_books = None if installed_books is None else set(installed_books)
    if installed_books is not None:
        if not installed_books <= set(graph):
            raise ValueError('installed books are outside the requested closure')
        if any(child not in installed_books for name in installed_books for child in graph[name]):
            raise ValueError('installed books must be closed under local includes')
    fingerprints = {name: certs.book_facts(source / (name + '.lisp'))[0]
                    for name in graph}
    exports = {name: exported_includes((source / (name + '.lisp')).read_text(),
                                      (source / (name + '.lisp')).parent)
               for name in graph}
    match_memo = {}
    def matches(cache, name):
        key = (str(cache), name)
        if key not in match_memo:
            path = cache / (name + '.lisp')
            match_memo[key] = False
            if path.is_file() and hashlib.sha256(path.read_bytes()).hexdigest() == fingerprints[name]:
                match_memo[key] = all(matches(cache, child) for child in graph[name])
        return match_memo[key]

    loaded = set()
    events = ['(in-package "ACL2")', '(set-cbd ' + json.dumps(str(source / 'books') + '/') + ')']
    coordinate = []
    inputs = {}
    def remember(path):
        if str(path) not in inputs:
            inputs[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    def cache_for(name):
        if installed_books is not None and name in installed_books:
            return source
        return next((cache for cache in caches
                     if (cache / (name + '.cert')).is_file()
                     and (cache / (name + '.port')).is_file()
                     and not any(deferred.get(child) for child in certs.closure(source, name))
                     and matches(cache, name)), None)
    def exported_closure(name):
        result = {name}
        for child in exports[name]: result.update(exported_closure(child))
        return result
    def cache_inputs(cache, name):
        for child in certs.closure(source, name):
            remember(cache / (child + '.lisp'))
            for suffix in ('.cert', '.port', '.fasl'):
                path = cache / (child + suffix)
                if path.is_file(): remember(path)
    def scoped_book(name, available):
        """An absent local dependency stays in its enclosing proof scope."""
        if name in available: return ''
        cache = cache_for(name)
        if cache is not None:
            cache_inputs(cache, name)
            available.update(exported_closure(name))
            return '(include-book ' + json.dumps(str(cache / name)) + ')'
        path = source / (name + '.lisp')
        remember(path)
        # Replaying dependencies inside LOCAL exports them only to that LOCAL
        # scope. Child-local rules still disappear at each child encapsulate.
        omitted, pruned = set(), {}
        text = selected_defthms(path.read_text(), deferred.get(name, set()),
                                omitted, all_deferred, pruned) if all_deferred else path.read_text()
        if omitted != deferred.get(name, set()):
            raise ValueError('named DEFTHM not found: ' + name)
        if omitted: removed[name] = sorted(omitted)
        if pruned: theory_pruned[name] = pruned
        transformed = scoped_events(text, path.parent, available)
        hoisted, bodies = admission_forms(transformed, path.parent, set(), limit or None)
        available.update(exported_closure(name))
        parts = [*hoisted, *[bounded_body(body, steps) if body.startswith('(encapsulate ') else body for body in bodies]]
        return '(progn\n' + '\n'.join(p for p in parts if p) + '\n)' if any(parts) else ''
    def scoped_events(text, directory, available):
        result = []
        for form in forms(text):
            head = event_head(form)
            target = proof_repl.include_target(form, directory) if head == 'include-book' else None
            if target is not None:
                form = scoped_book(target, available)
            else:
                if head in {'local', 'encapsulate', 'progn', 'progn!', 'with-prover-step-limit', 'with-prover-time-limit'}:
                    children = forms(form.strip()[1:-1])
                    start = 2 if head in {'encapsulate', 'with-prover-step-limit', 'with-prover-time-limit'} else 1
                    scope = set(available) if head == 'local' else available
                    body = scoped_events('\n'.join(children[start:]), directory, scope)
                    form = '(' + '\n'.join(children[:start]) + '\n' + body + ')' if body else ''
            if form: result.append(form)
        return '\n'.join(result)
    def visit(name):
        if name in loaded:
            return
        selected = cache_for(name)
        if selected is not None:
            # ACL2 still checks the certificate; matching source does not waive
            # compatibility or toolchain checks during the actual include.
            events.append('(include-book ' + json.dumps(str(selected / name)) + ')')
            loaded.update(exported_closure(name))
            cache_inputs(selected, name)
            coordinate.append({'book': name, 'kind': 'certificate-input', 'root': str(selected)})
            return
        for child in exports[name]:
            visit(child)
        path = source / (name + '.lisp')
        remember(path)
        original = path.read_text()
        omitted = set()
        pruned = {}
        body_text = selected_defthms(original, deferred.get(name, set()), omitted,
                                    all_deferred, pruned) if all_deferred else original
        if pruned: theory_pruned[name] = pruned
        if omitted != deferred.get(name, set()):
            raise ValueError('named DEFTHM not found: ' + name)
        if omitted: removed[name] = sorted(omitted)
        body_text = scoped_events(body_text, path.parent, set(loaded))
        hoisted, bodies = admission_forms(body_text, path.parent, set(loaded), limit or None)
        bodies = [bounded_body(body, steps) if body.startswith('(encapsulate ') else body for body in bodies]
        # All local fn include events were resolved above. Only system books
        # or package declarations may remain hoisted.
        events.extend(hoisted)
        events.append('(value-triple (cw "FN_SOURCE_BOOK ' + name + '~%"))')
        events.extend(bodies)
        events.append('(value-triple (cw "FN_SOURCE_END ' + name + '~%"))')
        loaded.add(name)
        coordinate.append({'book': name, 'kind': 'source-admission'})

    # Match the build prefix. Each generic now owns its attachment, so the
    # ordinary source-order walk also handles implementation selection.
    for name in EARLY: visit(name)
    output.parent.mkdir(parents=True, exist_ok=True)
    early = output.with_name(output.stem + '.early.lisp')
    early.write_text('\n\n'.join(events) + '\n')
    visit(world_book)
    events.append('(value-triple (cw "FN_SOURCE_LOGICAL_WORLD_READY~%"))')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('\n\n'.join(events) + '\n')
    manifest = output.with_suffix('.json')
    manifest.write_text(json.dumps({'kind': 'current logical source admission, not certification',
        'source': str(source), 'world_book': world_book,
        'source_revision': revision or subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip() if revision or (source / '.git').exists() else None,
        'source_sha256': fingerprints,
        'repository_sha256': {name + '.lisp': fingerprints[name] for name in sorted(graph)},
        'repository_books': sorted(name + '.lisp' for name in graph),
        'exported_books': sorted(name + '.lisp' for name in loaded),
        'logical_prefix': str(output.resolve()), 'cache_roots': [str(p) for p in caches],
        'installed_books': sorted(installed_books) if installed_books is not None else None,
        'inputs_sha256': inputs, 'output_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
        'books': coordinate, 'deferred_defthms': removed,
        'deferred_theory_references': theory_pruned,
        'per_event_prover_steps': steps, 'per_event_prover_seconds': limit}, indent=2) + '\n')
    return manifest


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-root', type=Path, required=True)
    p.add_argument('--world-book', default='books/image-world',
                   help='actual default or DTN logical umbrella; attachment order is unchanged')
    p.add_argument('--cache-root', type=Path, action='append', default=[])
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--limit', type=float, default=25.0)
    p.add_argument('--source-revision', help='immutable archive source identity')
    p.add_argument('--step-limit', type=int, default=200000)
    p.add_argument('--defer-defthm', action='append', default=[], metavar='BOOK:NAME',
                   help='explicitly omit an unrelated theorem, never a definition or guard/correspondence obligation')
    a = p.parse_args()
    deferred = {}
    for selection in a.defer_defthm:
        book, name = selection.rsplit(':', 1)
        deferred.setdefault(book.removesuffix('.lisp'), set()).add(name.lower())
    print(generate(a.source_root, a.cache_root, a.output, a.limit, a.source_revision,
                   deferred, a.step_limit, a.world_book))

if __name__ == '__main__': main()
