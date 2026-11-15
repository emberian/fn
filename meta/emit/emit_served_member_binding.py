#!/usr/bin/env python3
"""Propose live-world CNS selector/record checks; not a semantic certificate.

The attachment edge is checked as a selection, never substituted for a logical
body. Subsequent canonical/body and primitive proofs must consume these same
records. Python selection is only a proposal; the generated ACL2 checks replay
against the admitted world including the actual attachment property.
"""
from pathlib import Path
import argparse
import os
from emit_certificate import (Atom, List, fields, read_canonical, canonical_text,
                              decode, fn_of, calls_of, show, as_list, shallow, ident, lean_object, term)

STUB = 'FN2-CNS-RUN-STUB'
RUN = 'FN2-CNS-RUN'
ITEM = 'FN2-CNS-PUT-ITEM'
ANSWER = 'FN2-CNS-PUT-ANSWER'


def symbol(name):
    return List([Atom(':SYMBOL'), List(map(Atom, map(str, map(ord, 'ACL2')))),
                 List(map(Atom, map(str, map(ord, name))))])


def inspect(snapshot):
    packet = read_canonical(snapshot)
    if not packet or packet[0] != ':FN2-CERTIFICATE':
        raise ValueError('requires canonical certificate')
    p = fields(packet[1:])
    if str(p.get(':VERSION')) != '1' or as_list(p[':REFUSED']):
        raise ValueError('unsupported or refused certificate')
    if p[':ROOTS'] != List([symbol(STUB)]):
        raise ValueError('requires exact CNS run-stub root census')
    for key in (':MANIFEST', ':NATIVES'):
        if key not in p:
            raise ValueError('missing ' + key)
    rows = {}
    for row in p[':FUNCTIONS']:
        f, d = fn_of(row)
        if f.name in rows:
            raise ValueError('duplicate decoded function subject')
        rows[f.name] = (f, d)
    for name in (STUB, RUN, ITEM, ANSWER):
        if name not in rows or rows[name][1][':FUNCTION'] != symbol(name):
            raise ValueError('missing exact ACL2 subject ' + name)
    stub, sd = rows[STUB]
    run, rd = rows[RUN]
    # Canonical cons, not a decoded spelling: package identity matters.
    if sd[':ATTACHMENT'] != List([Atom(':CONS'), symbol(STUB), symbol(RUN)]):
        raise ValueError('actual CNS selector differs')
    for key in (':FORMALS', ':STOBJS-IN', ':STOBJS-OUT'):
        if key not in sd or key not in rd or sd[key] != rd[key]:
            raise ValueError('selected CNS ABI differs: ' + key)
    for name, (_, d) in rows.items():
        if name != STUB and decode(d[':ATTACHMENT']) != Atom('NIL'):
            raise ValueError('unaccounted attachment ' + name)
    graph = {name: calls_of(f.body, set()) for name, (f, _) in rows.items()}

    def path(start, target):
        pending = [(start, [start])]
        seen = set()
        while pending:
            name, route = pending.pop(0)
            if name == target:
                return route
            if name in seen:
                continue
            seen.add(name)
            pending.extend((child, route + [child]) for child in sorted(graph.get(name, ()))
                           if child in rows and child not in seen)
        raise ValueError('missing logical call path ' + start + ' -> ' + target)

    route = path(RUN, ITEM) + path(ITEM, ANSWER)[1:]
    # A helper with this name but a different ABI cannot silently inherit the
    # body bridge. Its full actual body/guard is checked below, not inferred here.
    if rows[ANSWER][0].formals != ['LIVE', 'OK0', 'RC', 'CODE', 'FITS', 'CC']:
        raise ValueError('reply helper ABI differs')
    return p, rows, route


def qualification_book(snapshot, output):
    p, rows, route = inspect(snapshot)
    base = Path(__file__).resolve().parents[2]
    def include(book):
        rel = os.path.relpath(base / 'books' / book, Path(output).resolve().parent)
        return '(include-book "' + rel.replace('\\', '/') + '")'
    lines = ['; PROPOSAL: current-world certification is required.',
             '; Selection/body identity only: no guard, primitive, or served-behavior discharge.',
             '; Logical body path: ' + ' -> '.join(route),
             '(in-package "ACL2")', include('assembly-attach'),
             include('translation-validation'),
             "(fn2-tv-check-manifest '" + canonical_text(p[':MANIFEST']) + ')']
    for row in p[':FUNCTIONS']:
        d = fields(row)
        lines.append("(fn2-tv-check-function '" + canonical_text(row) + " '" +
                     show(decode(d[':FUNCTION'])) + ')')
    names = '(' + ' '.join(rows) + ')'
    natives = '(' + ' '.join(show(decode(x)) for x in p[':NATIVES']) + ')'
    lines.append("""(make-event
 (if (and (equal (fn2-tv-attachment 'fn2-cns-run-stub (w state))
                 '(fn2-cns-run-stub . fn2-cns-run))
          (no-duplicatesp-eq '%s)
          (subsetp-eq '%s *fn2-tv-native-boundary*)
          (subsetp-eq *fn2-tv-native-boundary* '%s)
          (fn2-tv-closed-functions '%s (append '%s '%s) (w state)))
     (value '(value-triple :cns-selected-records-bound))
   (er soft 'cns-selected-records "Selector or canonical closure differs.")))""" %
                 (natives, natives, natives, names, names, natives))
    return '\n\n'.join(lines) + '\n'


def member_context_source(snapshot):
    """Generate the actual helper's MEMBER execution/logical context equation.

    This uses the existing unconditional all-Val MEMBER adequacy theorem. It
    does not invent a symbol-key guard, canonical primitive correspondence, or
    an equivalence between attached and constrained functions.
    """
    _, rows, _ = inspect(snapshot)
    function, row = rows[ANSWER]
    count = 0
    def replace(tree):
        nonlocal count
        if not isinstance(tree, List) or not tree or tree[0] == 'QUOTE':
            return tree
        result = List([replace(x) for x in tree])
        if tree[0] == 'MEMBER-EQUAL':
            if len(tree) != 3:
                raise ValueError('MEMBER-EQUAL ABI differs')
            result[0] = Atom('MEMBER-EQ-EXEC')
            count += 1
        return result
    executed = replace(function.body)
    if count != 1:
        raise ValueError('reply helper must contain exactly one logical MEMBER site')
    binders = ' '.join('(' + ident(x) + ' : Val)' for x in function.formals)
    arguments = ' '.join(ident(x) for x in function.formals)
    return '\n'.join([
        'module',
        'public import Fn2.ACL2.MemberBodyCorrect',
        'public import Fn2.Instances.LayerAEqns4',
        'import all Fn2.Instances.LayerAWorld.KCns_d0to12',
        'import all Init.Data.String.Basic',
        'import all Init.Data.String.Slice',
        'import all Init.Data.String.TakeDrop',
        'import all Init.Data.String.Pattern.Basic',
        'import all Init.Data.String.Pattern.String',
        '@[expose] public section',
        'namespace Fn2.ACL2.CnsSelectedMember',
        'open Fn2.ACL2.Translation Fn2.Instances.LayerAWorld',
        '-- Generated from the same packet as the selected-record qualification book.',
        '-- No current-world, reachability, guard, or primitive discharge is implied.',
        'def canonicalAnswer : Object := ' + lean_object(row[':LOGICAL-BODY']),
        'theorem answer_decoded : readTerm 512 canonicalAnswer = some ' +
            term(function.body) + ' := by rfl',
        'theorem member_context ' + binders + ' :',
        '    ' + ident(ANSWER) + ' ' + arguments + ' =',
        '    ' + shallow(executed, set(rows) | {'MEMBER-EQ-EXEC'}) + ' := by',
        '  simp only [MemberBodyCorrect.emitted_eq_native]',
        '  rfl',
        '#print axioms member_context',
        'end Fn2.ACL2.CnsSelectedMember', ''])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('packet', type=Path)
    ap.add_argument('output', type=Path)
    ap.add_argument('--lean-output', type=Path)
    args = ap.parse_args()
    snapshot = args.packet.read_text()
    proposed = qualification_book(snapshot, args.output)
    lean = member_context_source(snapshot) if args.lean_output else None
    args.output.write_text(proposed)
    if lean is not None:
        args.lean_output.write_text(lean)
    print('CNS selected-record proposal; ACL2 and semantic gates remain required')


if __name__ == '__main__':
    main()
