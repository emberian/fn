#!/usr/bin/env python3
"""Bind current CNS selection/whole constraints and actual caller domains.

Emission is a proposal. Qualification checks its exact source against the
record-toolchain cache. It establishes neither stub/implementation logical
equality nor Lean/body/primitive correspondence or theorem dependency closure.
"""
from pathlib import Path
import argparse
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import assurance_completion as completion
from emit_certificate import Atom, List, canonical_text, decode, fields, object_list, read_canonical, show
from served_semantic_inventory import function_semantics

BOOK = 'meta/emit/cns-attachment-join'
CNS_PAIRS = (
    ('FN2-CNS-RUN-STUB', 'FN2-CNS-RUN'),
    ('FN2-MACHINE-OBSERVE-FN2-CNS-STUB', 'FN2-MACHINE-OBSERVE-FN2-CNS'),
    ('FN2-CNS-ARM-CHARGE-OK-P-STUB', 'FN2-CNS-ARM-CHARGE-OK-P'),
    ('FN2-CNS-ARM-BOUND-STUB', 'FN2-CNS-ARM-BOUND'))
REQUIRED_CALLERS = ('FN2-MACHINE-RUN', 'FN2-MACHINE-OBSERVE-ROUTE-FN2-CNS')


def packet_fields(packet):
    if not isinstance(packet, List) or len(packet) % 2:
        raise ValueError('malformed attachment packet')
    keys = list(map(str, packet[::2]))
    expected = {':SCHEMA', ':PAIRS', ':MEMBERS', ':CONSTRAINT-OWNER', ':CONSTRAINTS', ':ORIGINS', ':PROVED-INSTANCES'}
    if len(keys) != len(set(keys)) or set(keys) != expected:
        raise ValueError('missing/duplicate/unknown attachment packet field')
    result = fields(packet)
    if str(result[':SCHEMA']) != '1':
        raise ValueError('unsupported attachment schema')
    return result


def proposal(records, packet):
    """Consume the existing canonical function inventory; create no second graph."""
    data = packet_fields(packet)
    pairs = decode(data[':PAIRS'])
    expected = List([List([Atom(a), Atom('.'), Atom(b)]) for a, b in CNS_PAIRS])
    if pairs != expected:
        raise ValueError('selected CNS joint tuple differs')
    constraints = object_list(data[':CONSTRAINTS'])
    if not constraints or len(constraints) != len(object_list(data[':ORIGINS'])):
        raise ValueError('missing whole constraints/origins')
    if not object_list(data[':PROVED-INSTANCES']):
        raise ValueError('missing admitted functional instance record')
    by_name = {name: row for name, row, _ in records}
    if len(by_name) != len(records):
        raise ValueError('duplicate canonical function')
    members = decode(data[':MEMBERS'])
    if not isinstance(members, List) or len(members) != len(CNS_PAIRS):
        raise ValueError('missing joint tuple member records')
    for (stub, impl), member in zip(CNS_PAIRS, members):
        if len(member) != 4 or tuple(map(str, member[2:])) != (':COMMON-LISP-COMPLIANT',)*2:
            raise ValueError('unverified attachment member guards')
        for name, exported in zip((stub, impl), member[:2]):
            if name not in by_name or exported != by_name[name]:
                raise ValueError('attachment function record differs: '+name)
        sf, gf = fields(member[0]), fields(member[1])
        semantic = function_semantics(stub, member[0], sf)
        if semantic['selected_attachment'] != impl:
            raise ValueError('canonical selection differs: '+stub)
        if any(sf[key] != gf[key] for key in (':STOBJS-IN', ':STOBJS-OUT')):
            raise ValueError('attachment stobj ABI differs: '+stub)
        if len(decode(sf[':FORMALS'])) != len(decode(gf[':FORMALS'])):
            raise ValueError('attachment arity differs: '+stub)
    callers = []
    subjects = {a for a, _ in CNS_PAIRS}
    for name, row, decoded_fields in records:
        semantic = function_semantics(name, row, decoded_fields)
        if subjects.intersection(semantic['calls']['body']):
            callers.append((name, row))
    if not set(REQUIRED_CALLERS).issubset(name for name, _ in callers):
        raise ValueError('actual served CNS callers missing')
    # The same live canonical checks used by the rest of the bridge bind
    # function selection and the actual caller body/guard before proof emission.
    lines = ['(in-package "ACL2")',
             '(include-book "../../books/cns-attachment-evidence")',
             "(fn2-av-check-packet '"+canonical_text(packet)+' *fn2-av-cns-pairs*)']
    selected = {n for pair in CNS_PAIRS for n in pair}
    checked = sorted(selected | {name for name, _ in callers})
    for name in checked:
        completion.symbol(name)
        lines.append("(fn2-tv-check-function '"+canonical_text(by_name[name])+" '"+name+')')
    for name, _ in sorted(callers):
        theorem = 'FN2-AV-CURRENT-'+completion.symbol(name)+'-DOMAIN'
        lines.append("(make-event (value (fn2-av-caller-event '"+name+
                     " *fn2-av-cns-pairs* '"+theorem+' (w state))))')
    return '\n'.join(lines)+'\n', {
        'kind': 'attachment-constraint-and-caller-domain-proposal',
        'selected_pairs': list(CNS_PAIRS), 'caller_functions': sorted(n for n, _ in callers),
        'constraint_count': len(constraints), 'book': BOOK,
        'proof_status': 'pending-current-record',
        'interpretation': 'selected executable implementations satisfy the joint constraints',
        'not_established': ['stub/implementation logical equality', 'Lean correspondence',
                            'raw/native correspondence', 'actual theorem assumption dependency closure']}


def generate(package, evidence):
    _, records, _, _ = completion.canonical(package)
    packet = read_canonical(evidence.read_text())
    source, report = proposal(records, packet)
    identities = ('(defconst *fn2-av-package-identity* \"' + completion.sha(package.read_bytes()) + '\")\n'
                  '(defconst *fn2-av-evidence-identity* \"' + completion.sha(evidence.read_bytes()) + '\")\n')
    return source + identities, report


def inspect(root, package, evidence, launcher):
    expected, report = generate(package, evidence)
    target = root / (BOOK+'.lisp')
    if not target.is_file() or target.read_text() != expected:
        raise ValueError('current attachment join missing or stale; emit then qualify')
    qualification = completion.qualified_claims(root, launcher, BOOK)
    if generate(package, evidence)[0] != expected or target.read_text() != expected:
        raise ValueError('attachment evidence changed during qualification')
    # Recheck current closure after all content reads; JSON flags never suffice.
    completion.qualified_claims(root, launcher, BOOK)
    return {**report, 'proof_status': 'qualified-acl2-constraints-and-caller-domains',
            'qualification': qualification, 'package_sha256': completion.sha(package.read_bytes()),
            'evidence_sha256': completion.sha(evidence.read_bytes())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--evidence', type=Path, required=True)
    parser.add_argument('--emit', action='store_true')
    parser.add_argument('--acl2')
    args = parser.parse_args()
    if args.emit:
        source, report = generate(args.package, args.evidence)
        target = completion.BASE / (BOOK+'.lisp')
        target.write_text(source)
    else:
        report = inspect(completion.BASE, args.package, args.evidence, args.acl2)
    print(json.dumps(report, indent=2))
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print('ATTACHMENT EVIDENCE: UNRESOLVED\n  '+str(error))
        sys.exit(1)
