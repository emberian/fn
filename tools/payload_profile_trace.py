#!/usr/bin/env python3
"""Closed trusted-source profile observer, not compiler allocation adequacy.

Adapted from the repository's legacy_parser_trace.py observer pattern. Each
arithmetic event is an ACL2-style binary add/multiply or unary negation;
source subtraction is never silently equated to one target allocation.
Observer list allocations are not allocations of the original implementation.
"""
from pathlib import Path
import argparse
import hashlib
from ledger import Sym, read_forms

ROOT = Path(__file__).resolve().parents[1]
SOURCES = ('books/deflate-inflate.lisp', 'books/payload-deflate.lisp',
           'books/payload-window.lisp')
SELECTED = ('fn-zin-bomb-limit', 'fn-zin-stored-allowance', 'fn-pzd-budget',
            'fn-pzw-quantum', 'fn-pzw-room', 'fn-pzw-budget-left',
            'fn-pzw-select', 'fn-pzw-stored-allowance',
            'fn-pzw-stored-admissiblep')


def sexp(x):
    if isinstance(x, list):
        return '(' + ' '.join(map(sexp, x)) + ')'
    if isinstance(x, Sym):
        return str(x)
    if isinstance(x, str):
        return '"' + x.replace('\\', '\\\\').replace('"', '\\"') + '"'
    return str(x)


class Instrument:
    def __init__(self, names):
        self.names = names
        self.serial = 0

    def fresh(self):
        self.serial += 1
        return f'pzt-tmp-{self.serial}'

    def combine(self, traces):
        if not traces:
            return 'nil'
        if len(traces) == 1:
            return traces[0]
        return '(append ' + ' '.join(traces) + ')'

    def bind(self, expressions, continuation):
        def walk(i, values, traces):
            if i == len(expressions):
                return continuation(values, traces)
            var = self.fresh()
            return (f'(let (({var} {self.expr(expressions[i])})) '
                    f'{walk(i + 1, values + [f"(car {var})"], traces + [f"(cdr {var})"])})')
        return walk(0, [], [])

    def expr(self, x):
        if not isinstance(x, list) or not x:
            return f'(cons {sexp(x)} nil)'
        op, *args = x
        op = str(op).lower()
        if op == 'quote':
            return f'(cons {sexp(x)} nil)'
        # ACL2's source macros normalize to binary arithmetic. Preserve the
        # order of argument evaluation and record every distinct negation.
        if op in ('1+', '1-'):
            return self.expr([Sym('+'), args[0], 1 if op == '1+' else -1])
        if op == '-':
            if len(args) == 1:
                return self.expr([Sym('unary--'), args[0]])
            if len(args) == 2:
                return self.expr([Sym('binary-+'), args[0], [Sym('unary--'), args[1]]])
            raise ValueError('unreviewed subtraction arity')
        if op in ('+', '*'):
            if not args:
                return self.expr(0 if op == '+' else 1)
            if len(args) == 1:
                return self.expr([Sym('fix'), args[0]])
            binary = Sym('binary-+' if op == '+' else 'binary-*')
            rhs = args[-1]
            for arg in reversed(args[:-1]):
                rhs = [binary, arg, rhs]
            return self.expr(rhs)
        if op == 'if':
            cond, branch = self.fresh(), self.fresh()
            return (f'(let* (({cond} {self.expr(args[0])}) '
                    f'({branch} (if (car {cond}) {self.expr(args[1])} {self.expr(args[2])}))) '
                    f'(cons (car {branch}) (append (cdr {cond}) (cdr {branch}))))')
        if op in ('and', 'or'):
            if not args:
                return self.expr(Sym('t' if op == 'and' else 'nil'))
            if len(args) == 1:
                return self.expr(args[0])
            cond, branch = self.fresh(), self.fresh()
            rest = self.expr([Sym(op), *args[1:]])
            choice = (f'(if (car {cond}) {rest} (cons nil nil))' if op == 'and'
                      else f'(if (car {cond}) (cons (car {cond}) nil) {rest})')
            return (f'(let* (({cond} {self.expr(args[0])}) ({branch} {choice})) '
                    f'(cons (car {branch}) (append (cdr {cond}) (cdr {branch}))))')
        if op in ('let', 'let*'):
            bindings, body = args
            if op == 'let':
                def done(values, traces):
                    var = self.fresh()
                    pairs = ' '.join(f'({sexp(pair[0])} {value})'
                                     for pair, value in zip(bindings, values))
                    return (f'(let ({pairs}) (let (({var} {self.expr(body)})) '
                            f'(cons (car {var}) {self.combine(traces + [f"(cdr {var})"])})))')
                return self.bind([p[1] for p in bindings], done)
            if not bindings:
                return self.expr(body)
            first, *rest = bindings
            value, branch = self.fresh(), self.fresh()
            tail = self.expr([Sym('let*'), rest, body])
            return (f'(let* (({value} {self.expr(first[1])}) '
                    f'({sexp(first[0])} (car {value})) ({branch} {tail})) '
                    f'(cons (car {branch}) (append (cdr {value}) (cdr {branch}))))')
        def done(values, traces):
            if op in self.names:
                var = self.fresh()
                return (f'(let (({var} ({self.names[op]} {" ".join(values)}))) '
                        f'(cons (car {var}) {self.combine(traces + [f"(cdr {var})"])}))')
            arithmetic = {'binary-+': ':add', 'binary-*': ':multiply', 'unary--': ':negate'}
            borrow = {'nfix', 'fix', 'natp', 'min', 'max', '<', '<=', 'equal',
                      'not', 'fn-zin-tin', 'fn-zin-tout'}
            if op not in arithmetic and op not in borrow and op != 'mv':
                raise ValueError(f'unclassified trusted source operation: {op}')
            site = self.fresh()
            call = f'({"list" if op == "mv" else op} {" ".join(values)})'
            if op in arithmetic:
                event = f'(list (list {arithmetic[op]} (list {" ".join(values)}) \'{site}))'
            elif op == 'mv':
                event = f'(list (list :multiple-value {len(values)} \'{site}))'
            else:
                event = f'(list (list :borrow \'{op} \'{site}))'
            return f'(cons {call} {self.combine(traces + [event])})'
        return self.bind(args, done)


def generate():
    definitions = {}
    headers = ['; GENERATED by tools/payload_profile_trace.py. Source events, not target allocation.']
    for path in SOURCES:
        source = ROOT / path
        headers.append(f'; {path} SHA256 {hashlib.sha256(source.read_bytes()).hexdigest()}')
        for form in read_forms(source.read_text()):
            if isinstance(form, list) and form and str(form[0]).lower() == 'defun':
                definitions[str(form[1]).lower()] = form
    names = {name: 'fn-pzt-' + name.removeprefix('fn-') for name in SELECTED}
    gen = Instrument(names)
    out = headers + ['(in-package "ACL2")', '(include-book "payload-window-profile-width")',
        '''(defun fn-pzt-count (family trace)
 (if (consp trace)
     (+ (if (equal (caar trace) family) 1 0)
        (fn-pzt-count family (cdr trace)))
   0))''',
        '''(defthm fn-pzt-count-append
 (equal (fn-pzt-count family (append left right))
        (+ (fn-pzt-count family left) (fn-pzt-count family right))))''']
    for original in SELECTED:
        form = definitions[original]
        name = names[original]
        params = sexp(form[2])
        args = ' '.join(map(sexp, form[2]))
        out.append(f'(defun-nx {name} {params}\n {gen.expr(form[-1])})')
        disabled = ' '.join(n for n in SELECTED if n != original) + ' binary-append'
        projection = '-by-definition' if original == 'fn-pzw-quantum' else '-value-projection'
        out.append(f'(defthm {name}{projection}\n'
                   f' (equal (car ({name} {args})) ({original} {args}))\n'
                   f' :hints (("Goal" :do-not \'(preprocess)\n'
                   f'                 :in-theory (e/d ({name} {original}) ({disabled})))))')
        # Keep a previously proved observer opaque: its value projection,
        # rather than eager expansion of its private trace, composes callers.
        out.append(f'(in-theory (disable {name}))')
    counts = ((1, 1, 0), (1, 1, 0), (2, 2, 0), (0, 0, 0),
              (2, 0, 1), (2, 0, 2), (5, 0, 3), (1, 1, 0), (1, 1, 0))
    for original, limits in zip(SELECTED, counts):
        name = names[original]
        args = ' '.join(map(sexp, definitions[original][2]))
        relation = '<=' if original in ('fn-pzw-select', 'fn-pzw-stored-admissiblep') else 'equal'
        clauses = '\n'.join(f'  ({relation} (fn-pzt-count {family} (cdr ({name} {args}))) {limit})'
                            for family, limit in zip((':add', ':multiply', ':negate'), limits))
        # All already defined helper observers must expand here: this proves
        # actual dynamic source counts, rather than pricing opaque calls.
        enabled = ' '.join(names.values())
        out.append(f'(defthm {name}-source-counts\n (and\n{clauses})\n'
                   f' :rule-classes nil\n :hints (("Goal" :in-theory (e/d ({enabled}) (nfix min max)))))')
    return '\n\n'.join(out) + '\n'


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--check', action='store_true')
    arguments = parser.parse_args()
    output = generate()
    target = ROOT / 'books/payload-profile-source-trace.lisp'
    if arguments.write:
        target.write_text(output)
    elif arguments.check:
        if not target.exists() or target.read_text() != output:
            raise SystemExit('payload profile source observer is stale')
        print('payload profile source observer matches trusted source')
    else:
        print(output, end='')
