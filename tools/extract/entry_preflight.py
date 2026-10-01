#!/usr/bin/env python3
"""Read-only native entry/selected extraction inventory preflight.

Follow syntactic native function calls from explicit entries, not every token
in the host. Report literal core dispatch demands and unresolved dynamic ones.
This is a conservative all-branches graph, not execution/reachability evidence.
No Lisp is evaluated; no exported definition, receipt or runtime state is made.
Exit 0 only for a complete static selection with all counterpart demands present;
exit 1 means missing/unresolved interfaces; exit 2 means invalid input.
"""
from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from ledger import Reader, Sym, head  # noqa: E402

BRIDGES = frozenset(('fnn-core', 'fnn-core-state', 'fnn-core-arena-state',
                     'fnn-core-buffer-arena-state', 'fnn-core-buffer-state',
                     'fnn-call'))
DATA = frozenset(('quote', 'declare', 'quasiquote'))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def name(value):
    if not isinstance(value, Sym):
        return None
    text = str(value).lower()
    for prefix in ('acl2::', 'cl-user::'):
        if text.startswith(prefix):
            return text[len(prefix):]
    return text


def quoted_symbol(form):
    if isinstance(form, list) and len(form) == 2 and head(form) in ('quote', 'function'):
        return name(form[1])
    return None


def expressions(form):
    if not isinstance(form, list) or not form:
        return
    yield form
    if head(form) in DATA:
        return
    for child in form:
        yield from expressions(child)


def definitions(paths):
    result, inputs = {}, {}
    for path in paths:
        path = Path(path).resolve()
        raw = path.read_bytes()
        source = raw.decode()
        inputs[str(path)] = hashlib.sha256(raw).hexdigest()
        for form, line in Reader(source).top_level():
            # Top-level load blocks can wrap definitions; never evaluate them.
            for candidate in expressions(form):
                if head(candidate) not in ('defun', 'defmacro') or len(candidate) < 3:
                    continue
                n = name(candidate[1])
                if n in result:
                    raise ValueError(f'duplicate native definition {n}: {path}:{line}')
                result[n] = {'form': candidate, 'file': str(path), 'line': line,
                             'kind': head(candidate)}
    return result, inputs


def classify(subject, entries, counterparts, require_counterpart=True):
    key = 'ACL2::' + subject.upper()
    item = entries.get(key)
    if item is None:
        return 'missing-definition'
    kind = item.get('kind')
    if kind in ('host-defined', 'hole'):
        return 'external-implementation-required'
    if require_counterpart and key not in counterparts:
        return 'missing-counterpart'
    if kind == 'alias':
        target = item.get('via')
        if not isinstance(target, str) or target not in entries:
            return 'unresolved-alias'
    return 'present-in-selected-inventory'


def inspect(paths, ir_path, inventory_path, roots):
    defs, inputs = definitions(paths)
    ir_raw = Path(ir_path).read_bytes()
    inventory_raw = Path(inventory_path).read_bytes()
    ir = json.loads(ir_raw)
    inventory = json.loads(inventory_raw)
    entries = {}
    for item in ir['functions']:
        if item['name'] in entries:
            raise ValueError('duplicate IR function: ' + item['name'])
        entries[item['name']] = item
    counterparts = set(inventory['star1_names'])
    inputs[str(Path(ir_path).resolve())] = hashlib.sha256(ir_raw).hexdigest()
    inputs[str(Path(inventory_path).resolve())] = hashlib.sha256(inventory_raw).hexdigest()
    queue = deque((r.lower(), [r.lower()]) for r in roots)
    seen, demands, unresolved = set(), [], []
    while queue:
        n, route = queue.popleft()
        if n in seen:
            continue
        seen.add(n)
        if n not in defs:
            unresolved.append({'kind': 'missing-native-definition', 'route': route})
            continue
        definition = defs[n]
        if definition['kind'] == 'defmacro':
            unresolved.append({'kind': 'macro-expansion-required', 'route': route})
            continue
        # Skip lambda list; only inspect executable body forms.
        for body in definition['form'][3:]:
            for expr in expressions(body):
                callee = name(expr[0])
                if callee in BRIDGES:
                    subject = quoted_symbol(expr[1]) if len(expr) > 1 else None
                    if subject:
                        demands.append({'subject': subject, 'caller': n, 'route': route,
                                        'file': definition['file'], 'definition_line': definition['line'],
                                        'status': classify(subject, entries, counterparts)})
                    else:
                        unresolved.append({'kind': 'dynamic-core-dispatch', 'route': route,
                                           'bridge': callee})
                elif callee in ('funcall', 'apply'):
                    target = quoted_symbol(expr[1]) if len(expr) > 1 else None
                    if target in BRIDGES:
                        subject = quoted_symbol(expr[2]) if len(expr) > 2 else None
                        if subject:
                            demands.append({'subject': subject, 'caller': n, 'route': route,
                                            'status': classify(subject, entries, counterparts)})
                        else:
                            unresolved.append({'kind': 'dynamic-core-dispatch', 'route': route,
                                               'bridge': target})
                    elif target and target in defs:
                        queue.append((target, route + [target]))
                    else:
                        unresolved.append({'kind': 'dynamic-function-call', 'route': route})
                elif callee == 'function':
                    target = quoted_symbol(expr)
                    if target in defs:
                        queue.append((target, route + [target]))
                    elif target and target.startswith('fnn-'):
                        unresolved.append({'kind': 'missing-native-callback', 'route': route,
                                           'target': target})
                elif callee and callee.startswith('fn-') and callee not in defs:
                    demands.append({'subject': callee, 'caller': n, 'route': route,
                                    'mode': 'direct-definition',
                                    'status': classify(callee, entries, counterparts, False)})
                elif callee and callee.startswith('fnn-'):
                    queue.append((callee, route + [callee]))
                elif callee and callee in defs:
                    queue.append((callee, route + [callee]))
    # Preserve call sites but collapse repeated identical syntactic demands.
    demands = list({json.dumps(x, sort_keys=True): x for x in demands}.values())
    unresolved = list({json.dumps(x, sort_keys=True): x for x in unresolved}.values())
    missing = [d for d in demands if d['status'] != 'present-in-selected-inventory']
    for path, expected in inputs.items():
        if digest(path) != expected:
            raise ValueError('input changed during preflight: ' + path)
    return {'status': 'incomplete' if missing or unresolved else 'static-selection-present',
            'scope': 'Conservative syntactic graph; inventory presence is not loaded execution, semantic proof, funding or qualification.',
            'entries': roots, 'inputs_sha256': inputs, 'native_functions_visited': sorted(seen),
            'demands': demands, 'missing_demands': missing, 'unresolved': unresolved}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native', type=Path, nargs='+', required=True)
    parser.add_argument('--ir', type=Path, required=True)
    parser.add_argument('--inventory', type=Path, required=True)
    parser.add_argument('--entry', action='append', required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    try:
        report = inspect(args.native, args.ir, args.inventory, args.entry)
    except (ValueError, OSError, KeyError, TypeError) as error:
        parser.exit(2, f'entry-preflight: invalid input: {error}\n')
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(f"entry-preflight: {report['status']}; {len(report['demands'])} literal demands, "
          f"{len(report['missing_demands'])} missing, {len(report['unresolved'])} unresolved; {args.out}")
    return int(report['status'] != 'static-selection-present')


if __name__ == '__main__':
    sys.exit(main())
