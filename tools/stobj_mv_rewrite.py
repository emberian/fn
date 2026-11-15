#!/usr/bin/env python3
"""Bind known stobj-valued MV expressions with the shared structural reader.

A carrier allowlist identifies generated PUT/SET-* and UPDATE-* writers;
read accessors are never inferred to be writers. Each replacement preserves
left-to-right argument evaluation and is checked by capture-aware LET* beta
normalization before any file is written. No ACL2 admission is claimed.
"""
from __future__ import annotations
import argparse
from pathlib import Path
from lisp_rewrite import Atom, Lst, Pre, parse, match, write

PATHS = (
 'checkpoint-allocation-coordinator', 'checkpoint-commit-leases',
 'checkpoint-future-working', 'checkpoint-installation-coordinator',
 'checkpoint-lifecycle', 'checkpoint-maintenance-staging',
 'checkpoint-recovery-census', 'checkpoint-recovery-evidence-boot',
 'checkpoint-restore-arena', 'checkpoint-restore-boot', 'checkpoint-restore-map',
 'checkpoint-restore-reach', 'checkpoint-restore-semantic-work',
)
CARRIERS = (
 'fn2-retirement-control', 'fn2-commit-io', 'fn2-checkpoint-future',
 'fn2-checkpoint-lifecycle', 'fn2-checkpoint-future-windows',
 'fn2-checkpoint-recovery-census', 'fn2-checkpoint-recovery-evidence',
 'fn2-checkpoint-restore-arena-control', 'fn2-boot-config',
 'fn2-checkpoint-restore-map-control', 'fn2-checkpoint-restore-reach',
 'fn2-checkpoint-restore-semantic',
)

def writer(node, carriers):
    if not isinstance(node, Lst) or not node.items or not isinstance(node.items[0], Atom):
        return None
    head = node.items[0].low
    for carrier in sorted(carriers, key=len, reverse=True):
        if head == carrier+'-put' or head.startswith(carrier+'-set-') or head.startswith('update-'+carrier+'-'):
            return carrier
        if carrier == 'fn2-core' and head == 'fn2-core-stop':
            return carrier
    if head == 'if' and len(node.items) == 4:
        branches = node.items[2:]
        found = [writer(branch, carriers) for branch in branches]
        target = next((x for x in found if x), None)
        if target and all(w == target or (isinstance(b, Atom) and b.low == target)
                          for b, w in zip(branches, found)):
            return target
    return None

def beta(node, env=None):
    """Snapshot substitution: a prior scalar binding retains the old carrier."""
    env = {} if env is None else env
    if isinstance(node, Atom):
        return env.get(node.low, ('atom', node.text))
    if isinstance(node, Pre):
        # Reader quotation is data, so do not substitute inside it.
        return ('prefix', node.prefix, beta(node.node, {}))
    if not isinstance(node, Lst):
        raise ValueError('unsupported node')
    items = node.items
    if items and isinstance(items[0], Atom) and items[0].low in ('quote', 'function'):
        return tuple(beta(x, {}) for x in items)
    if items and isinstance(items[0], Atom) and items[0].low == 'let*':
        if len(items) != 3 or not isinstance(items[1], Lst):
            raise ValueError('only one-body LET* belongs to this rewrite')
        local = dict(env)
        for binding in items[1].items:
            if not isinstance(binding, Lst) or len(binding.items) != 2 or not isinstance(binding.items[0], Atom):
                raise ValueError('bad binding')
            local[binding.items[0].low] = beta(binding.items[1], local)
        return beta(items[2], local)
    return tuple(beta(x, env) for x in items)

def rewrite(source, carriers=CARRIERS):
    tree = parse(source)
    used = set()
    def names(node):
        if isinstance(node, Atom): used.add(node.low)
        elif isinstance(node, Pre): names(node.node)
        elif isinstance(node, Lst):
            for item in node.items: names(item)
    for node in tree.forms: names(node)
    serial = 0
    edits = []
    for found in match('(mv ?*args)', tree.forms):
        args = found.captures['args']
        targets = [writer(arg, carriers) for arg in args]
        if not any(targets): continue
        if len([x for x in targets if x]) != len(set(x for x in targets if x)):
            raise ValueError('duplicate stobj outputs')
        # Source slices preserve all comments inside individual arguments.
        # Refuse comments between arguments rather than silently dropping them.
        for at, comment in tree.comments:
            if found.start <= at < found.end and not any(arg.start <= at < arg.end for arg in args):
                raise ValueError('comment between MV arguments')
        bindings, values = [], []
        for arg, target in zip(args, targets):
            raw = tree.text[arg.start:arg.end]
            if target:
                bindings.append((target, raw)); values.append(target)
            elif isinstance(arg, Atom):
                values.append(raw)
            else:
                while True:
                    serial += 1; fresh = f'fn2-mv-scalar-{serial}'
                    if fresh not in used: break
                used.add(fresh)
                bindings.append((fresh, raw)); values.append(fresh)
        indent = ' ' * (found.start - tree.text.rfind('\n', 0, found.start) - 1)
        replacement = '(let* (' + ('\n'+indent+'        ').join('('+n+' '+v+')' for n,v in bindings) + ')\n'+indent+' (mv '+' '.join(values)+'))'
        original = parse(tree.text[found.start:found.end]).forms[0]
        changed = parse(replacement).forms[0]
        if beta(original) != beta(changed):
            raise ValueError('LET* normalization differs from original MV formula')
        edits.append((found.start, found.end, replacement))
    return write(tree.text, edits), len(edits)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('paths', nargs='*', type=Path)
    parser.add_argument('--write', action='store_true')
    args=parser.parse_args()
    paths=args.paths or [Path('books')/(name+'.lisp') for name in PATHS]
    total=0
    for path in paths:
        old=path.read_text(); new,count=rewrite(old); total+=count
        if args.write and count: path.write_text(new)
        print(f'{path}: {count}')
    print(f'{total} MV forms; beta-normalization checked for each replacement')
if __name__ == '__main__': main()
