#!/usr/bin/env python3
"""Source-only whole-table controls and ACL2 fixture emitter for CNS enum noops.

Reads actual old/new PUT expressions and the actual defcolumns declaration.
The evaluator is a deliberately closed test interpreter, never host/runtime code.
Unknown forms fail closed. ACL2 output is an unadmitted logical control artifact.
"""
import argparse
import copy
import itertools
from pathlib import Path
import subprocess
from lisp_rewrite import Atom, Lst, parse, match

TABLE = 'fn2-cns-sources'
PUT = TABLE + '-put'
TARGETS = ['fn2-cns-source-issue-children', 'fn2-cns-source-harvest',
           'fn2-cns-source-next-children']


def tree(n):
    if isinstance(n, Atom):
        try:
            return int(n.text)
        except ValueError:
            return n.low
    if isinstance(n, Lst):
        return [tree(x) for x in n.items]
    raise ValueError(f'unsupported reader node {n}')


def sexp(x):
    return '(' + ' '.join(map(sexp, x)) + ')' if isinstance(x, list) else str(x)


def snippets(text, repaired):
    out = []
    for name in TARGETS:
        fn = next(m.node for m in match(None, parse(text), deep=False, head='defun')
                  if m.node.items[1].low == name)
        candidates = []
        for m in match(None, [fn], deep=True, head='let*' if repaired else PUT):
            t = tree(m.node)
            if repaired:
                # The repair wraps exactly one original PUT in a LET* whose
                # returned carrier is the whole sources table.
                if t[-1] == TABLE and isinstance(t[1], list) and t[1] and t[1][0][0] == TABLE:
                    candidates.append(t)
            elif any(a[0] == 'manifest-stage' for a in t[2:]):
                candidates.append(t)
        if len(candidates) != 1:
            raise ValueError((name, len(candidates)))
        out.append(candidates[0])
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-root', type=Path, required=True)
    ap.add_argument('--old-ref', default='4c46607449f33dc604d944d81ea614661eba04e3')
    ap.add_argument('--emit', type=Path, required=True)
    args = ap.parse_args()
    root = args.source_root
    old = subprocess.check_output(['git', 'show', args.old_ref + ':books/cns-source-raw.lisp'], cwd=root, text=True)
    new = (root / 'books/cns-source-raw.lisp').read_text()
    decl = next(tree(m.node) for m in match(None, parse(root / 'books/cns-source-state.lisp'), deep=False, head='defcolumns'))
    assert decl[1] == TABLE and len(decl) == 3
    cols = decl[2]
    indexes = {c[0]: i for i, c in enumerate(cols)}
    constants = {}
    for _, typ in cols:
        if isinstance(typ, list):
            assert typ[0] == ':enum'
            constants.update({f'*{typ[1]}-{v[1:]}*': i for i, v in enumerate(typ[2])})
    phases = next(c[1][2] for c in cols if c[0] == 'phase')
    stages = next(c[1][2] for c in cols if c[0] == 'manifest-stage')
    oldforms, newforms = snippets(old, False), snippets(new, True)

    def nth(i, xs):
        return xs[i] if i < len(xs) else None

    def update(i, value, xs):
        ys = copy.deepcopy(xs)
        ys.extend([None] * max(0, i + 1 - len(ys)))
        ys[i] = value
        return ys

    def ev(x, env):
        if not isinstance(x, list):
            if isinstance(x, int):
                return x
            if x == 't':
                return True
            if x == 'nil':
                return False
            return constants[x] if x in constants else env[x]
        op, *a = x
        if op == 'if':
            return ev(a[1] if ev(a[0], env) else a[2], env)
        if op == 'cond':
            return next(ev(body, env) for test, body in a if ev(test, env))
        if op == 'let*':
            local = env.copy()
            for var, value in a[0]:
                local[var] = ev(value, local)
            return ev(a[1], local)
        if op == 'and':
            return all(ev(v, env) for v in a)
        if op == 'not':
            return not ev(a[0], env)
        if op == 'equal':
            return ev(a[0], env) == ev(a[1], env)
        if op == '+':
            return sum(ev(v, env) for v in a)
        if op == PUT:
            local = env.copy()
            for field, value in a[1:]:
                i = indexes[field]
                local[TABLE] = update(i, update(ev(a[0], local), ev(value, local), local[TABLE][i]), local[TABLE])
            return local[TABLE]
        if op.startswith(TABLE + '-') and op[len(TABLE) + 1:] in indexes:
            return nth(ev(a[0], env), ev(a[1], env)[indexes[op[len(TABLE) + 1:]]])
        raise ValueError(f'unsupported form {x}')

    mutants = []
    def mutations(node, path=()):
        if not isinstance(node, list):
            return
        if node and node[0] in ('if', 'cond'):
            tail = node[-1] if node[0] == 'if' else node[-1][-1]
            if tail == TABLE:
                yield path
        for i, child in enumerate(node):
            yield from mutations(child, path + (i,))
    for case, form in enumerate(newforms):
        for path in mutations(form):
            mutant = copy.deepcopy(form)
            parent = mutant
            for i in path[:-1]:
                parent = parent[i]
            parent[path[-1]] = TABLE
            mutants.append([case, mutant, False])
    assert len(mutants) == 4

    # Full concrete logical carrier: every declared column has two rows,
    # plus the generated rows scalar. Distinct sentinels expose collateral writes.
    initial = [[i % 2, (i + 1) % 2] for i in range(len(cols))] + [2]
    fixtures = ['; Generated by tools/cns_enum_controls.py; ACL2 ADMISSION NOT RUN.',
                '(in-package "ACL2")', '(include-book "../books/cns-source-state")']
    count = 0
    for case, (before, after) in enumerate(zip(oldforms, newforms)):
        for phase, stage, flag, data, raw, same in itertools.product(range(len(phases) + 1), range(len(stages) + 1), [False, True], [False, True], [False, True], [False, True]):
            # Exhaust every named enum plus the unnamed storage value 255.
            p = phase if phase < len(phases) else 255
            s = stage if stage < len(stages) else 255
            table = copy.deepcopy(initial)
            table[indexes['phase']][0] = p
            table[indexes['manifest-stage']][0] = s
            env = dict(constants, **{TABLE: table, 's': 0, 'phase': p, 'stage': s,
                'raw': raw, 'manifest': flag, 'data': data, 'done': flag,
                'next-index': 1 if same else 0, 'op': 3, 'opgen': 5, 'len': 7,
                'event': 2, 'outcome': 3, 'reason': 4, 'count': 5,
                'offset': 8, 'copied': 2, 'n': 3})
            assert ev(before, env) == ev(after, env), (case, p, s, flag, raw, same)
            count += 1
            for mutant in mutants:
                if mutant[0] == case and not mutant[2]:
                    mutant[2] = ev(before, env) != ev(mutant[1], env)
            # Keep ACL2 closed witnesses compact: all named transitions plus
            # 255, with each flag combination, using matching phase/stage cycles.
            if not ((stage == 0 and not flag and not data and raw and same)
                    or (phase == 0 and not flag and not data and raw and same)
                    or (p == 255 and s == 255)
                    or (p == constants['*fn2-cns-source-phase-raw-wait*']
                        and s in (constants['*fn2-cns-source-manifest-stage-wait*'],
                                  constants['*fn2-cns-source-manifest-stage-data-wait*']))):
                continue
            bindings = ' '.join(f'({k} {sexp(v) if isinstance(v, list) else ("t" if v is True else "nil" if v is False else v)})'
                                if k != TABLE else f'({TABLE} (quote {sexp(v)}))'
                                for k, v in env.items() if k not in constants)
            hyp = f'(and ({TABLE}p {TABLE}) ({TABLE}-wfp {TABLE}) (natp s) (< s ({TABLE}-rows {TABLE})))'
            fixtures.append(f'(defthm fn2-cns-enum-control-{case}-{phase}-{stage}-{int(flag)}-{int(data)}-{int(raw)}-{int(same)}\n (let* ({bindings}) (and {hyp} (equal {sexp(before)} {sexp(after)})))\n :rule-classes nil)')
    assert all(m[2] for m in mutants), "a removed named transition escaped controls"
    # Removing valid-row alone breaks no-op elimination: existing WFP zero-row
    # table, setter UPDATE-NTH extends the enum array, skipped write does not.
    empty = [[] for _ in cols] + [0]
    j = indexes['manifest-stage']
    old_missing = update(j, update(0, nth(0, empty[j]), empty[j]), empty)
    assert old_missing != empty
    fixtures.append(f'(defthm fn2-cns-enum-missing-row-control\n (let ((xs (quote {sexp(empty)})))\n (and ({TABLE}p xs) ({TABLE}-wfp xs)\n (not (< 0 ({TABLE}-rows xs)))\n (not (equal (update-nth {j} (update-nth 0 (nth 0 (nth {j} xs)) (nth {j} xs)) xs) xs))))\n :rule-classes nil)')
    args.emit.write_text('\n'.join(fixtures) + '\n')
    print(f'{count} full-table AST comparisons passed; 4 dropped-transition mutants rejected; missing-row negative passed; emitted {len(fixtures)-3} unadmitted ACL2 witnesses to {args.emit}')


if __name__ == '__main__':
    main()
