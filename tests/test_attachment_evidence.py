"""Exact CNS tuple/canonical join controls. No ACL2 or cache work."""
from pathlib import Path
import copy
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import attachment_evidence as evidence
from emit_certificate import Atom, List, fields, canonical_text, read_canonical


def obj(value):
    if isinstance(value, tuple):
        return List([Atom(':CONS'), obj(value[0]), obj(value[1])])
    if isinstance(value, list):
        tail = obj('NIL')
        for item in reversed(value):
            tail = List([Atom(':CONS'), obj(item), tail])
        return tail
    text = str(value)
    if text.lstrip('-').isdigit():
        return List([Atom(':INTEGER'), Atom(text)])
    package = 'KEYWORD' if text.startswith(':') else 'ACL2'
    return List([Atom(':SYMBOL'), List([Atom(str(ord(c))) for c in package]),
                 List([Atom(str(ord(c))) for c in text.lstrip(':')])])


def record(name, selected=None, body=None, formals=('X',)):
    values = {':FUNCTION': obj(name), ':FORMALS': obj(list(formals)),
              ':LOGICAL-BODY': obj(body if body is not None else [':MISSING'] if selected else ['QUOTE', 0]),
              ':GUARD': obj(['QUOTE', 'T']), ':JUSTIFICATION': obj('NIL'),
              ':STOBJS-IN': obj(['NIL'] * len(formals)), ':STOBJS-OUT': obj(['NIL']),
              ':ATTACHMENT': obj((name, selected)) if selected else obj('NIL')}
    row = List([])
    for k, v in values.items():
        row.extend([Atom(k), v])
    return name, row, fields(row)


def fixture():
    records = []
    members = []
    for stub, impl in evidence.CNS_PAIRS:
        s, g = record(stub, selected=impl), record(impl)
        records += [s, g]
        members.append([s[1], g[1], ':COMMON-LISP-COMPLIANT', ':COMMON-LISP-COMPLIANT'])
    records += [record(evidence.REQUIRED_CALLERS[0], body=[evidence.CNS_PAIRS[0][0], 'X']),
                record(evidence.REQUIRED_CALLERS[1], body=[evidence.CNS_PAIRS[1][0], 'X'])]
    data = {':SCHEMA': Atom('1'), ':PAIRS': obj(list(evidence.CNS_PAIRS)),
            ':MEMBERS': obj(members), ':CONSTRAINT-OWNER': obj(evidence.CNS_PAIRS[0][0]),
            ':CONSTRAINTS': obj([['EQUAL', 'X', 'X']]),
            ':ORIGINS': obj([['DEFTHM', 'ACTUAL-CONSTRAINT']]),
            ':PROVED-INSTANCES': obj([['ACTUAL-INSTANCE']])}
    packet = List([])
    for k, v in data.items():
        packet.extend([Atom(k), v])
    return records, packet


def change(packet, key, value):
    packet[packet.index(Atom(key))+1] = value


class AttachmentEvidence(unittest.TestCase):
    def test_proposal_binds_live_full_packet_and_actual_callers(self):
        records, packet = fixture()
        source, report = evidence.proposal(records, packet)
        self.assertIn("(fn2-av-check-packet '"+canonical_text(packet), source)
        self.assertIn("fn2-av-caller-event 'FN2-MACHINE-RUN", source)
        self.assertEqual(report['proof_status'], 'pending-current-record')
        self.assertIn('stub/implementation logical equality', report['not_established'])
        self.assertNotIn('defattach', source.lower())

    def test_changed_selection_rejected_even_with_valid_names(self):
        records, packet = fixture()
        pairs = list(evidence.CNS_PAIRS)
        pairs[0] = (pairs[0][0], 'FN2-CNS-RUN-DEFAULT')
        change(packet, ':PAIRS', obj(pairs))
        with self.assertRaisesRegex(ValueError, 'joint tuple'):
            evidence.proposal(records, packet)

    def test_changed_implementation_bytes_rejected(self):
        records, packet = fixture()
        i = next(i for i, r in enumerate(records) if r[0] == 'FN2-CNS-RUN')
        records[i] = record('FN2-CNS-RUN', body=['QUOTE', 999])
        with self.assertRaisesRegex(ValueError, 'function record differs'):
            evidence.proposal(records, packet)

    def test_omitted_constraints_origins_or_kernel_record_rejected(self):
        for key in (':CONSTRAINTS', ':ORIGINS', ':PROVED-INSTANCES'):
            with self.subTest(key=key):
                records, packet = fixture()
                change(packet, key, obj([]))
                with self.assertRaises(ValueError):
                    evidence.proposal(records, packet)

    def test_no_actual_caller_is_not_vacuous_success(self):
        records, packet = fixture()
        with self.assertRaisesRegex(ValueError, 'callers missing'):
            evidence.proposal(records[:-2], packet)

    def test_duplicate_member_function_or_packet_key_rejected(self):
        records, packet = fixture()
        with self.assertRaisesRegex(ValueError, 'duplicate canonical'):
            evidence.proposal(records+[records[0]], packet)
        packet += [Atom(':SCHEMA'), Atom('1')]
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            evidence.proposal(records, packet)

    def test_constraint_mutation_changes_required_live_check(self):
        records, packet = fixture()
        old, _ = evidence.proposal(records, packet)
        change(packet, ':CONSTRAINTS', obj([['QUOTE', 'T']]))
        new, report = evidence.proposal(records, packet)
        self.assertNotEqual(old, new)
        self.assertIn(canonical_text(packet), new)
        self.assertEqual(report['proof_status'], 'pending-current-record')

    def test_transport_roundtrip(self):
        records, packet = fixture()
        self.assertEqual(evidence.proposal(records, packet),
                         evidence.proposal(records, read_canonical(canonical_text(packet))))


if __name__ == '__main__':
    unittest.main()
