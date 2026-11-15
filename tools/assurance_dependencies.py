#!/usr/bin/env python3
"""Extract source declarations and exact canonical attachment requirements.

This is a boundary report, not extracted theorem/rune support or an assurance
certificate. It cannot close actual proof assumptions, even for an empty graph.
"""
from pathlib import Path
import argparse
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import assurance_completion as completion
import ledger


def tagged(value):
    if isinstance(value, ledger.Sym):
        return ['symbol', str(value)]
    if isinstance(value, list):
        return ['list', [tagged(item) for item in value]]
    return ['literal', value]


def form_digest(value):
    return completion.sha(json.dumps(tagged(value), separators=(',', ':')).encode())


def named_assumptions(root):
    """Read the design-of-record encapsulates and retain missing witnesses."""
    rows = []
    for path in sorted((root / 'books').glob('assumptions*.lisp')):
        raw = path.read_bytes()
        for form in ledger.read_forms(raw.decode('latin-1')):
            if ledger.head(form) != 'encapsulate' or len(form) < 2:
                continue
            declarations = form[1]
            if not isinstance(declarations, list):
                raise ValueError('unsupported assumption signature: ' + str(path))
            witnesses = {}
            constraints = []
            for event in form[2:]:
                if ledger.head(event) == 'local' and len(event) == 2:
                    witness = event[1]
                    if ledger.head(witness) == 'defun' and len(witness) >= 4:
                        witnesses[str(witness[1]).upper()] = witness
                elif ledger.head(event) == 'defthm' and len(event) >= 3:
                    constraints.append({'name': str(event[1]).upper(), 'formula_sha256': form_digest(event[2])})
            for signature in declarations:
                if (not isinstance(signature, list) or not signature or
                    not isinstance(signature[0], list) or not signature[0] or
                    not isinstance(signature[0][0], ledger.Sym)):
                    raise ValueError('unsupported constrained assumption signature: ' + str(path))
                name = str(signature[0][0]).upper()
                witness = witnesses.get(name)
                arity = len(signature[0]) - 1
                problems = []
                if witness is None:
                    problems.append('local witness missing or unsupported')
                elif not isinstance(witness[2], list) or len(witness[2]) != arity:
                    problems.append('local witness arity differs from constrained signature')
                rows.append({'name': name, 'arity': arity, 'source': str(path.relative_to(root)),
                             'source_sha256': completion.sha(raw), 'encapsulate_sha256': form_digest(form),
                             'local_witness_sha256': form_digest(witness) if witness else None,
                             'constraints': constraints, 'declaration_problems': problems})
    if len({row['name'] for row in rows}) != len(rows):
        raise ValueError('duplicate named assumption subject')
    return rows


def boundary_report(root, package):
    from emit_served_certificate import canonical_text
    from served_semantic_inventory import function_semantics, semantic_inventory
    header, records, arm_roots, native = completion.canonical(package)
    functions = [{'name': name, 'record_sha256': completion.sha(canonical_text(row).encode()),
                  'semantic': function_semantics(name, row, fields)} for name, row, fields in records]
    by_name = {f['name']: f for f in functions}
    # The live export closure explicitly includes FN2-TURN. Keep this actual
    # caller in requirements even though legacy candidate roots list only arms.
    roots = list(dict.fromkeys([*arm_roots, 'FN2-TURN']))
    inventory = semantic_inventory(functions, [{'name': name} for name in roots], native)
    reached_by = {}
    for requirement in inventory['roots']:
        for record in requirement['function_records']:
            reached_by.setdefault(record['name'], []).append(requirement['name'])
    assumptions = named_assumptions(root)
    for assumption in assumptions:
        assumption['canonical_callgraph_roots'] = sorted(reached_by.get(assumption['name'], []))
    attachments = []
    for function in functions:
        semantic = function['semantic']
        selected = semantic['selected_attachment']
        if selected is None:
            continue
        name = function['name']
        attachments.append({'subject': name, 'selected': selected,
                            'record_sha256': function['record_sha256'],
                            'attachment_field_sha256': semantic['fields'][':ATTACHMENT'],
                            'selected_record_sha256': by_name.get(selected, {}).get('record_sha256'),
                            'canonical_callgraph_roots': sorted(reached_by.get(name, [])),
                            'required_obligation': 'attachment_refinement:' + name})
    return {'kind': 'source-and-canonical-boundaries-only',
            'package_sha256': completion.sha(package.read_bytes()),
            'named_assumptions': assumptions, 'selected_attachments': attachments,
            'missing_actual_caller': 'FN2-TURN' not in by_name,
            'actual_theorem_constraint_dependency_closure': 'unresolved',
            'unresolved': ['No actual theorem/rune dependency support was extracted.',
                           'Canonical call reachability does not establish theorem assumption use.',
                           'Selected attachments require constraint satisfaction, domains and implementation correspondence.',
                           'Raw/native replacements are a separate runtime boundary.']}


def live_support_snapshot(path):
    """Preserve a live export as partial diagnostic evidence, never authority."""
    raw = path.read_bytes()
    forms = ledger.read_forms(raw.decode('latin-1'))
    if len(forms) != 1 or not isinstance(forms[0], list):
        raise ValueError('expected one live proof-support report')
    row = forms[0]
    if len(row) % 2 or any(not isinstance(k, ledger.Sym) for k in row[::2]):
        raise ValueError('malformed live proof-support report')
    fields = {str(k).upper(): v for k, v in zip(row[::2], row[1::2])}
    if len(fields) != len(row) // 2:
        raise ValueError('duplicate proof-support report field')
    if str(fields.get(':KIND')).upper() != ':LIVE-EVENT-PROOF-SUPPORT-PROJECTION':
        raise ValueError('unsupported proof-support report kind')
    if not isinstance(fields.get(':COMPLETE'), ledger.Sym) or str(fields[':COMPLETE']).upper() != 'NIL':
        raise ValueError('partial proof-support snapshot cannot assert completeness')
    if not all(k in fields for k in (':ROOTS', ':NAMED-ASSUMPTION-SUBJECTS', ':LIMITATIONS', ':NODES')):
        raise ValueError('incomplete proof-support snapshot shape')
    return {'kind': 'unqualified-live-event-support-snapshot',
            'snapshot_sha256': completion.sha(raw), 'payload': tagged(row),
            'actual_theorem_constraint_dependency_closure': 'unresolved',
            'provenance': 'Must be paired with the exact admitted world/source receipt; this reader does not qualify it.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    inputs = parser.add_mutually_exclusive_group(required=True)
    inputs.add_argument('--package', type=Path)
    inputs.add_argument('--source-only', action='store_true')
    parser.add_argument('--proof-support', type=Path, help='optional partial live-world snapshot; never closes the gate')
    args = parser.parse_args()
    report = (boundary_report(completion.BASE, args.package) if args.package else
              {'kind': 'source-declarations-only',
               'named_assumptions': named_assumptions(completion.BASE),
               'selected_attachments': None,
               'actual_theorem_constraint_dependency_closure': 'unresolved',
               'unresolved': ['No canonical packet supplied; selected attachments are unknown.',
                              'Source declarations do not establish actual theorem assumption use.']})
    if args.proof_support:
        report['live_proof_support'] = live_support_snapshot(args.proof_support)
    print(json.dumps(report, indent=2))
    return 1  # A boundary report never closes the outstanding proof dependency gate.


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as error:
        print('ASSURANCE DEPENDENCIES: UNRESOLVED\n  ' + str(error))
        sys.exit(1)
