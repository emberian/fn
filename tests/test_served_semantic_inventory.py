"""Canonical semantic requirement inventory controls; no proof/build claims."""
import importlib.util
from pathlib import Path
import sys
import unittest

EMIT = Path(__file__).parents[1] / 'meta/emit'
sys.path.insert(0, str(EMIT))
import emit_certificate as c

SPEC = importlib.util.spec_from_file_location('semantic_inventory', EMIT / 'served_semantic_inventory.py')
s = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(s)


def obj(value):
    """Construct actual canonical transport through the certificate reader."""
    if isinstance(value, int):
        text = f'(:INTEGER {value})'
    elif isinstance(value, list):
        result = obj('NIL')
        for item in reversed(value):
            result = c.List([c.Atom(':CONS'), obj(item), result])
        return result
    else:
        package = 'KEYWORD' if value.startswith(':') else 'ACL2'
        text = '(:SYMBOL (' + ' '.join(str(ord(x)) for x in package) + ') (' + \
               ' '.join(str(ord(x)) for x in value.lstrip(':')) + '))'
    return c.read_canonical(text)


def record(name, body=None, guard=None, attachment=None, justification='NIL', omit=(), overrides=None):
    fields = {':FORMALS': obj(['X']),
              ':LOGICAL-BODY': obj(body if body is not None else ['QUOTE', 0]),
              ':GUARD': obj(guard if guard is not None else ['QUOTE', 'T']),
              ':JUSTIFICATION': obj(justification),
              ':ATTACHMENT': (c.List([c.Atom(':CONS'), obj(name), obj(attachment)])
                              if attachment else obj('NIL')),
              ':STOBJS-IN': obj(['NIL']), ':STOBJS-OUT': obj(['NIL'])}
    fields.update(overrides or {})
    for key in omit:
        del fields[key]
    row = c.List([c.Atom(':FUNCTION'), obj(name)])
    for key, value in fields.items():
        row.extend([c.Atom(key), value])
    # Round-trip the exact transport before inventory construction.
    row = c.read_canonical(c.canonical_text(row))
    fields = c.fields(row)
    semantic = s.function_semantics(name, row, fields)
    return {'name': name, 'record_sha256': s.canonical_digest(row), 'semantic': semantic}


def inventory(records, root='ROOT', boundary=()):
    return s.semantic_inventory(records, [{'name': root}], boundary)['roots'][0]


class ServedSemanticInventory(unittest.TestCase):
    def test_constructor_rejects_mismatched_subject_and_fields(self):
        row = c.List([c.Atom(':FUNCTION'), obj('ROOT'),
                      c.Atom(':LOGICAL-BODY'), obj(['QUOTE', 0])])
        fields = c.fields(row)
        with self.assertRaisesRegex(ValueError, 'subject mismatch'):
            s.function_semantics('OTHER', row, fields)
        with self.assertRaisesRegex(ValueError, 'fields mismatch'):
            s.function_semantics('ROOT', row, dict(fields, **{':GUARD': obj('T')}))

    def test_guard_only_transitive_dependencies(self):
        records = [record('ROOT', guard=['GUARD-HELPER', 'X']),
                   record('GUARD-HELPER', guard=['GUARD-LEAF', 'X']), record('GUARD-LEAF')]
        result = inventory(records)
        self.assertEqual({r['name'] for r in result['function_records']},
                         {'ROOT', 'GUARD-HELPER', 'GUARD-LEAF'})
        self.assertFalse(result['frontiers'])

    def test_attachment_keeps_logical_body_and_selected_edge(self):
        root = record('ROOT', body=['LOGICAL-CALLEE', 'X'], attachment='EXEC-CALLEE')
        semantic = root['semantic']
        self.assertEqual(semantic['calls']['body'], ['LOGICAL-CALLEE'])
        self.assertEqual(semantic['selected_attachment'], 'EXEC-CALLEE')
        result = inventory([root, record('LOGICAL-CALLEE'), record('EXEC-CALLEE')])
        self.assertEqual({r['name'] for r in result['function_records']},
                         {'ROOT', 'LOGICAL-CALLEE', 'EXEC-CALLEE'})
        refinement = [o for o in result['obligations'] if o['layer'] == 'attachment_refinement']
        self.assertEqual(len(refinement), 1)
        self.assertEqual(refinement[0]['source_sha256'], semantic['fields'][':ATTACHMENT'])
        other = record('ROOT', body=['QUOTE', 7], attachment='EXEC-CALLEE')
        self.assertNotEqual(semantic['fields'][':LOGICAL-BODY'], other['semantic']['fields'][':LOGICAL-BODY'])

    def test_repeated_primitive_sites_are_distinct(self):
        plus = ['BINARY-+', 'X', ['QUOTE', 1]]
        root = record('ROOT', body=['CONS', plus, plus])
        sites = [site for site in root['semantic']['primitive_sites'] if site['callee'] == 'BINARY-+']
        self.assertEqual(len(sites), 2)
        self.assertNotEqual(sites[0]['site'], sites[1]['site'])
        self.assertEqual(sites[0]['term_sha256'], sites[1]['term_sha256'])
        result = inventory([root], boundary=['CONS', 'BINARY-+'])
        plus_domains = [o for o in result['obligations']
                        if o['layer'] == 'primitive_domain' and o['subject'].endswith('/BINARY-+')]
        self.assertEqual(len(plus_domains), 2)
        self.assertNotEqual(plus_domains[0]['id'], plus_domains[1]['id'])

    def test_missing_unsupported_unknown_and_boundary_frontiers(self):
        root = record('ROOT', body=['UNKNOWN', ['BINARY-+', 'X', ['QUOTE', 1]]],
                      omit=[':STOBJS-IN'], overrides={':GUARD': c.read_canonical('(:RATIONAL 1 2)')})
        result = inventory([root], boundary=['UNRECOGNIZED-NATIVE'])
        frontiers = '\n'.join(result['frontiers'])
        for expected in ('missing field :STOBJS-IN', 'unsupported :GUARD', 'missing function UNKNOWN',
                         'primitive absent from canonical boundary BINARY-+',
                         'unsupported canonical native UNRECOGNIZED-NATIVE'):
            self.assertIn(expected, frontiers)

    def test_unresolved_metadata_stays_frontier(self):
        for key in (':FORMALS', ':LOGICAL-BODY', ':GUARD', ':ATTACHMENT',
                    ':STOBJS-IN', ':STOBJS-OUT'):
            with self.subTest(field=key):
                root = record('ROOT', overrides={key: obj(':MISSING')})
                self.assertTrue(any(key in f for f in inventory([root])['frontiers']),
                                f'{key} unresolved metadata disappeared')

    def test_missing_justification_state_retained_and_recursion_blocked(self):
        leaf = record('ROOT', overrides={':JUSTIFICATION': obj(':MISSING')})
        self.assertEqual(leaf['semantic']['metadata_states'][':JUSTIFICATION'], 'missing')
        self.assertFalse(inventory([leaf])['frontiers'])
        recursive = record('ROOT', body=['ROOT', 'X'], overrides={':JUSTIFICATION': obj(':MISSING')})
        self.assertTrue(any('justification' in f.lower() for f in inventory([recursive])['frontiers']))

    def test_raw_justification_keeps_frontier_and_known_dependency(self):
        root = record('ROOT', justification=['RAW-JUSTIFICATION', ['MEASURE', 'MEASURE-HELPER']])
        result = inventory([root, record('MEASURE-HELPER')])
        self.assertEqual({r['name'] for r in result['function_records']}, {'ROOT', 'MEASURE-HELPER'})
        self.assertTrue(any('justification/measure binding requires a checked decoder' in f
                            for f in result['frontiers']))

    def test_duplicate_and_conflicting_subjects_rejected(self):
        root = record('ROOT')
        for records in ([root, root], [root, record('ROOT', body=['QUOTE', 8])]):
            with self.subTest(records=records):
                with self.assertRaisesRegex(ValueError, 'duplicate semantic function subject'):
                    inventory(records)
        with self.assertRaisesRegex(ValueError, 'duplicate semantic root subject'):
            s.semantic_inventory([root], [{'name': 'ROOT'}, {'name': 'ROOT'}], [])
        root['semantic']['record_sha256'] = 'forged'
        with self.assertRaisesRegex(ValueError, 'semantic record digest mismatch'):
            inventory([root])

    def test_input_status_cannot_discharge_obligations(self):
        root = record('ROOT')
        root.update(status='proved', passed=True, proof_complete=True)
        root['semantic'].update(status='proved', passed=True, certified=True)
        result = s.semantic_inventory([root],
                                      [{'name': 'ROOT', 'status': 'proved', 'passed': True}], [])
        self.assertEqual(result['kind'], 'required-obligations-only')
        self.assertEqual(result['roots'][0]['status'], 'pending')
        self.assertEqual({o['layer'] for o in result['roots'][0]['obligations']},
                         set(s.FUNCTION_LAYERS + s.ROOT_LAYERS + ('canonical_record',)))
        self.assertTrue(all('passed' not in o and 'status' not in o
                            for o in result['roots'][0]['obligations']))


if __name__ == '__main__':
    unittest.main()
