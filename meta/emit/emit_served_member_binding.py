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
                              decode, fn_of, calls_of, show, as_list, shallow, ident, lean_object, term, canonical_nil, is_lambda, val, canonical_list,
                              NATIVE, SPECIAL, lean_str, expression_value, expression_proof,
                              evaluator_certificate, body_certificate)

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
        if name != STUB and not canonical_nil(d[':ATTACHMENT']):
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
          (equal (fn2-tv-object *fn2-tv-native-boundary*) '%s)
          (subsetp-eq '%s *fn2-tv-native-boundary*)
          (subsetp-eq *fn2-tv-native-boundary* '%s)
          (fn2-tv-closed-functions '%s (append '%s '%s) (w state)))
     (value '(value-triple :cns-selected-records-bound))
   (er soft 'cns-selected-records "Selector or canonical closure differs.")))""" %
                 (natives, canonical_text(canonical_list(p[':NATIVES'])), natives, natives, names, names, natives))
    # An actual ACL2 evaluator equation for the whole helper, checked after
    # exact live-record validation. This is a by-definition interpretation
    # theorem, not primitive correspondence or an attachment substitution.
    answer, answer_row = rows[ANSWER]
    evaluator = 'FN2-CNS-SELECTED-EXPORT-EVAL'
    lines.append(evaluator_certificate([(answer, answer_row)], rows).replace('FN2-EXPORT-EVAL', evaluator))
    for event in body_certificate(answer, answer_row, rows)[1:]:
        lines.append(event.replace('FN2-EXPORT-EVAL', evaluator).replace(
            ANSWER + '-EXPORT-BODY', ANSWER + '-EXPORT-BODY-BY-DEFINITION'))
    return '\n\n'.join(lines) + '\n'


def member_literal_site(body):
    """Read the actual simple MEMBER lambda expansion, retaining quote data.

    This is a syntactic selector for a domain proof, never an evaluator or a
    replacement formula. Unsupported call shapes are refused.
    """
    sites = []
    def substitute(value, env):
        if isinstance(value, Atom):
            return env.get(str(value), value)
        if not isinstance(value, List) or not value or value[0] == 'QUOTE':
            return value
        if is_lambda(value[0]):
            raise ValueError('nested lambda actual outside MEMBER selector')
        return List([substitute(item, env) for item in value])
    def walk(value, env):
        if not isinstance(value, List) or not value or value[0] == 'QUOTE':
            return
        if is_lambda(value[0]):
            formals = list(map(str, value[0][1]))
            if len(formals) != len(value) - 1 or len(set(formals)) != len(formals):
                raise ValueError('MEMBER lambda ABI differs')
            actuals = [substitute(item, env) for item in value[1:]]
            walk(value[0][2], dict(zip(formals, actuals)))
            return
        if value[0] == 'MEMBER-EQUAL':
            sites.append([substitute(item, env) for item in value[1:]])
        for item in value[1:]:
            walk(item, env)
    walk(body, {})
    if len(sites) != 1 or len(sites[0]) != 2:
        raise ValueError('requires one exact MEMBER comparison site')
    key, quoted = sites[0]
    if not isinstance(key, Atom) or str(key) != 'RC':
        raise ValueError('MEMBER key is not actual RC argument')
    if not isinstance(quoted, List) or len(quoted) != 2 or quoted[0] != 'QUOTE':
        raise ValueError('MEMBER list is not literal')
    elements = quoted[1]
    if (not isinstance(elements, List) or not elements or
            any(not isinstance(item, Atom) or not hasattr(item, 'symbol_package')
                for item in elements)):
        raise ValueError('MEMBER literal elements are not canonical symbols')
    return elements


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
    elements = member_literal_site(function.body)
    domain_proofs = ['⟨rfl, rc, ' + val(item) + ', rfl, Or.inr ⟨_, rfl⟩⟩' for item in elements]
    domain_proof = domain_proofs[-1]
    for proof in reversed(domain_proofs[:-1]):
        domain_proof = '⟨' + proof + ', ' + domain_proof + '⟩'
    domain_lines = [
        'theorem reached_comparison_domains (rc : Val) :',
        '    ' + ' ∧\n    '.join('PrimitiveSymbols.symbolEqualDomain "EQUAL" [rc, ' + val(item) + ']' for item in elements) + ' := by',
        '  exact ' + domain_proof,
        '#print axioms reached_comparison_domains']
    # Bind canonical operands, not only their decoded spellings. The RC
    # representation premise must be supplied by the actual caller certificate.
    pair_lines = []
    for index, item in enumerate(elements):
        literal = List([Atom(':SYMBOL'),
                        List([Atom(str(ord(c))) for c in item.symbol_package]),
                        List([Atom(str(ord(c))) for c in item.symbol_name])])
        name = 'memberLiteral' + str(index)
        pair_lines.extend([
            'def ' + name + ' : Object := ' + lean_object(literal),
            'theorem ' + name + '_represented : ' + name + '.value? = some ' + val(item) + ' := by rfl',
            'theorem reached_pair_' + str(index) + ' (rcObject : Object) (rc : Val)',
            '    (rcRepresented : rcObject.value? = some rc) :',
            '    ∃ resultObject,',
            '      PrimitiveSymbols.equalObjects "EQUAL" [rcObject, ' + name + '] = some resultObject ∧',
            '      resultObject.value? = some (Prim.equal rc ' + val(item) + ') := by',
            '  exact PrimitiveSymbols.symbol_equal_correspondence',
            '    "EQUAL" [rcObject, ' + name + '] [rc, ' + val(item) + ']',
            '    (.cons rcRepresented (.cons ' + name + '_represented .nil))',
            '    ⟨rfl, rc, ' + val(item) + ', rfl, Or.inr ⟨_, rfl⟩⟩',
            '    (Prim.equal rc ' + val(item) + ') rfl',
            '#print axioms reached_pair_' + str(index)])
    literals = '[' + ', '.join(val(item) for item in elements) + ']'
    literal_objects = '[' + ', '.join('memberLiteral' + str(i) for i in range(len(elements))) + ']'
    represented_literals = '.nil'
    for i in reversed(range(len(elements))):
        represented_literals = '(.cons memberLiteral' + str(i) + '_represented ' + represented_literals + ')'
    suffix_lines = [
        'theorem reached_member_suffix (rcObject : Object) (rc : Val)',
        '    (rcRepresented : rcObject.value? = some rc) :',
        '    (PrimitiveMemberSymbols.memberObject rcObject',
        '      (MemberExecEvaluation.objects ' + literal_objects + ')).value? =',
        '      some («MEMBER-EQ-EXEC» rc (Val.ofList ' + literals + ')) ∧',
        '    nativeCall "MEMBER-EQUAL" [rc, Val.ofList ' + literals + '] =',
        '      some («MEMBER-EQ-EXEC» rc (Val.ofList ' + literals + ')) := by',
        '  exact PrimitiveMemberSymbols.canonical_member_emitted rcRepresented ' + represented_literals,
        '#print axioms reached_member_suffix']
    # Only direct calls in this exact helper need dispatch equations. A
    # missing non-native canonical callee must refuse rather than inherit an ABI.
    callees = calls_of(function.body, set()) - set(NATIVE) - set(SPECIAL)
    dispatch_lines = []
    for name in sorted(callees):
        if name not in rows:
            raise ValueError('missing helper dispatch record ' + name)
        callee = rows[name][0]
        bs = ' '.join('(' + ident(x) + ' : Val)' for x in callee.formals)
        av = ', '.join(ident(x) for x in callee.formals)
        args = ' '.join(ident(x) for x in callee.formals)
        dispatch_lines.extend([
            'private theorem ' + ident(name) + '.dispatched {err : String} ' + bs + ' :',
            '    (match nativeCall ' + lean_str(name) + ' [' + av + '] with',
            '     | some x => Except.ok x',
            '     | none => match fns ' + lean_str(name) + ' [' + av + '] with',
            '       | some x => Except.ok x | none => Except.error err) =',
            '      .ok (' + ident(name) + ' ' + args + ') := by',
            '  simp only [nativeCall_none ' + lean_str(name) + ' [' + av + '] (by decide +kernel),',
            '    Fn2.Instances.LayerAWorld.' + ident(name) + '.fns_eq]'])
    binders = ' '.join('(' + ident(x) + ' : Val)' for x in function.formals)
    arguments = ' '.join(ident(x) for x in function.formals)
    env = '[' + ', '.join('(' + lean_str(x) + ', ' + ident(x) + ')' for x in function.formals) + ']'
    evaluated = expression_value(function.body, set(rows), {x: ident(x) for x in function.formals})
    body_lines = [
        'theorem answer_eval_export ' + binders + ' :',
        '    evalExport 512 canonicalAnswer fns ' + env + ' =',
        '      .ok (' + ident(ANSWER) + ' ' + arguments + ') := by',
        '  apply evalExport_of_decoded_by_definition answer_decoded',
        '  change eval fns ' + env + ' ' + term(function.body) + ' 512 = .ok ' + evaluated,
        *expression_proof(function.body, set(rows), {x: ident(x) for x in function.formals}, dispatch=callees),
        '#print axioms answer_eval_export']
    composed_lines = [
        'theorem answer_eval_export_member_context ' + binders + ' :',
        '    evalExport 512 canonicalAnswer fns ' + env + ' =',
        '      .ok ' + shallow(executed, set(rows) | {'MEMBER-EQ-EXEC'}) + ' := by',
        '  exact (answer_eval_export ' + arguments + ').trans',
        '    (congrArg Except.ok (member_context ' + arguments + '))',
        '#print axioms answer_eval_export_member_context']
    return '\n'.join([
        'module',
        'public import Fn2.ACL2.MemberBodyCorrect',
        'public import Fn2.ACL2.PrimitiveSymbols',
        'public import Fn2.ACL2.PrimitiveMemberSymbols',
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
        *dispatch_lines,
        *body_lines,
        'theorem member_context ' + binders + ' :',
        '    ' + ident(ANSWER) + ' ' + arguments + ' =',
        '    ' + shallow(executed, set(rows) | {'MEMBER-EQ-EXEC'}) + ' := by',
        '  simp only [MemberBodyCorrect.emitted_eq_native]',
        '  rfl',
        '#print axioms member_context',
        *composed_lines,
        *domain_lines,
        *pair_lines,
        *suffix_lines,
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
