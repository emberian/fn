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

    def test_recursive_sibling_cross_edge_requires_all_members(self):
        records = [record('ROOT', body=['B', ['C', 'X']]),
                   record('B', body=['ROOT', 'X'], justification=':MISSING'),
                   record('C', body=['B', 'X'], justification=':MISSING')]
        result = inventory(records)
        self.assertEqual({o['subject'] for o in result['obligations']
                          if o['layer'] == 'termination'}, {'ROOT', 'B', 'C'})
        self.assertIn('C: recursive component has unresolved justification', result['frontiers'])

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
        root = record('ROOT', body=['ROOT', 'X'], justification=['RAW-JUSTIFICATION', ['MEASURE', 'MEASURE-HELPER']])
        self.assertEqual(root['semantic']['metadata_states'][':JUSTIFICATION'], 'malformed')
        result = inventory([root, record('MEASURE-HELPER')])
        self.assertEqual({r['name'] for r in result['function_records']}, {'ROOT', 'MEASURE-HELPER'})
        self.assertTrue(any('malformed :JUSTIFICATION:' in f for f in result['frontiers']))
        self.assertIn('ROOT: recursive component has unresolved justification', result['frontiers'])

    def test_valid_justification_decodes_pool_compare_and_member_eq_exec(self):
        cl_syms = {'NIL', 'T', 'QUOTE', 'IF', 'LAMBDA'}

        def csym(pkg, name):
            return c.read_canonical(
                '(:SYMBOL (' + ' '.join(str(ord(ch)) for ch in pkg) + ') (' +
                ' '.join(str(ord(ch)) for ch in name) + '))'
            )

        def canon(val):
            if isinstance(val, int):
                return c.read_canonical(f'(:INTEGER {val})')
            if isinstance(val, tuple) and len(val) == 2 and val[0] in ('ACL2', 'COMMON-LISP', 'KEYWORD'):
                return csym(val[0], val[1])
            if isinstance(val, str):
                if val.startswith(':'):
                    return csym('KEYWORD', val[1:])
                return csym('COMMON-LISP' if val in cl_syms else 'ACL2', val)
            if isinstance(val, list):
                if len(val) >= 3 and val[-2] == '.':
                    out = canon(val[-1])
                    for elem in reversed(val[:-2]):
                        out = c.List([c.Atom(':CONS'), canon(elem), out])
                    return out
                out = csym('COMMON-LISP', 'NIL')
                for elem in reversed(val):
                    out = c.List([c.Atom(':CONS'), canon(elem), out])
                return out
            raise TypeError(val)

        def canon_record(name, formals, body, guard=None, justification='NIL'):
            fmap = {
                ':FORMALS': canon(formals),
                ':LOGICAL-BODY': canon(body),
                ':GUARD': canon(guard if guard is not None else ['QUOTE', 'T']),
                ':JUSTIFICATION': canon(justification),
                ':ATTACHMENT': canon('NIL'),
                ':STOBJS-IN': canon(['NIL'] * len(formals)),
                ':STOBJS-OUT': canon(['NIL']),
            }
            row = c.List([c.Atom(':FUNCTION'), canon(name)])
            for k, v in fmap.items():
                row.extend([c.Atom(k), v])
            row = c.read_canonical(c.canonical_text(row))
            fmap = c.fields(row)
            return {'name': name, 'record_sha256': s.canonical_digest(row),
                    'semantic': s.function_semantics(name, row, fmap)}

        pool_just = [
            'JUSTIFICATION',
            ['I', 'N'],
            ['NIL', 'O-P', '.', 'O<'],
            [['NFIX', ['BINARY-+', ['NFIX', 'N'], ['UNARY--', ['NFIX', 'I']]]],
             'IF', 'MV-LIST', 'RETURN-LAST'],
        ]
        pool_rec = canon_record(
            'FN2-POOL-COMPARE-LOOP',
            ['SLOT1', 'OFF1', 'SLOT2', 'OFF2', 'I', 'N', 'FN2-POOL'],
            ['IF', ['<', ['NFIX', 'I'], ['NFIX', 'N']],
             ['FN2-POOL-COMPARE-LOOP', 'SLOT1', 'OFF1', 'SLOT2', 'OFF2',
              ['BINARY-+', ['QUOTE', 1], ['NFIX', 'I']], 'N', 'FN2-POOL'],
             ['QUOTE', 'T']],
            justification=pool_just,
        )
        nfix_rec = canon_record('NFIX', ['X'], ['IF', ['INTEGERP', 'X'], 'X', ['QUOTE', 0]])
        sem = pool_rec['semantic']
        self.assertEqual(sem['metadata_states'][':JUSTIFICATION'], 'present')
        self.assertEqual(sem['justification_symbols'], [])
        self.assertEqual(sem['calls']['measure'], ['BINARY-+', 'NFIX', 'UNARY--'])
        self.assertEqual(sem['calls']['wfr'], [])
        self.assertEqual(sem['justification']['subset'], ['I', 'N'])
        self.assertEqual(sem['justification']['free_vars'], ['I', 'N'])
        self.assertEqual(sem['justification']['wfr'], {
            'domain': 'O-P', 'domain_package': 'ACL2',
            'relation': 'O<', 'relation_package': 'ACL2',
            'subversive': False,
        })
        self.assertEqual(sem['justification']['ruler_extenders'], ['IF', 'MV-LIST', 'RETURN-LAST'])
        measure_sites = [st['callee'] for st in sem['primitive_sites'] if st['site'].startswith('measure:')]
        self.assertEqual(sorted(measure_sites), ['BINARY-+', 'UNARY--'])
        res = inventory([pool_rec, nfix_rec], root='FN2-POOL-COMPARE-LOOP',
                        boundary=['<', 'BINARY-+', 'UNARY--', 'INTEGERP'])
        self.assertEqual(res['frontiers'], [])
        self.assertIn(('termination', 'FN2-POOL-COMPARE-LOOP'),
                      {(o['layer'], o['subject']) for o in res['obligations']})
        self.assertIn(('measure_domain', 'FN2-POOL-COMPARE-LOOP'),
                      {(o['layer'], o['subject']) for o in res['obligations']})

        # Mutating the measure changes measure_sha256
        alt_just = [
            'JUSTIFICATION',
            ['I', 'N'],
            ['NIL', 'O-P', '.', 'O<'],
            [['NFIX', 'N'], 'IF', 'MV-LIST', 'RETURN-LAST'],
        ]
        alt_rec = canon_record(
            'FN2-POOL-COMPARE-LOOP',
            ['SLOT1', 'OFF1', 'SLOT2', 'OFF2', 'I', 'N', 'FN2-POOL'],
            ['QUOTE', 'T'],
            justification=alt_just,
        )
        self.assertNotEqual(sem['justification']['measure_sha256'],
                            alt_rec['semantic']['justification']['measure_sha256'])

        # MEMBER-EQ-EXEC canonical justification
        mem_just = [
            'JUSTIFICATION',
            ['LST'],
            ['NIL', 'O-P', '.', 'O<'],
            [['ACL2-COUNT', 'LST'], 'IF', 'MV-LIST', 'RETURN-LAST'],
        ]
        mem_rec = canon_record(
            'MEMBER-EQ-EXEC',
            ['X', 'LST'],
            ['IF', ['CONSP', 'LST'], ['MEMBER-EQ-EXEC', 'X', ['CDR', 'LST']], ['QUOTE', 'NIL']],
            justification=mem_just,
        )
        mem_res = inventory([mem_rec], root='MEMBER-EQ-EXEC', boundary=['CONSP', 'CDR', 'ACL2-COUNT'])
        self.assertEqual(mem_res['frontiers'], [])

    def test_justification_measure_and_custom_wfr_edges_drive_closure_and_missing_frontiers(self):
        cl_syms = {'NIL', 'T', 'QUOTE', 'IF', 'LAMBDA'}

        def csym(pkg, name):
            return c.read_canonical(
                '(:SYMBOL (' + ' '.join(str(ord(ch)) for ch in pkg) + ') (' +
                ' '.join(str(ord(ch)) for ch in name) + '))'
            )

        def canon(val):
            if isinstance(val, int):
                return c.read_canonical(f'(:INTEGER {val})')
            if isinstance(val, tuple) and len(val) == 2 and val[0] in ('ACL2', 'COMMON-LISP', 'KEYWORD'):
                return csym(val[0], val[1])
            if isinstance(val, str):
                if val.startswith(':'):
                    return csym('KEYWORD', val[1:])
                return csym('COMMON-LISP' if val in cl_syms else 'ACL2', val)
            if isinstance(val, list):
                if len(val) >= 3 and val[-2] == '.':
                    out = canon(val[-1])
                    for elem in reversed(val[:-2]):
                        out = c.List([c.Atom(':CONS'), canon(elem), out])
                    return out
                out = csym('COMMON-LISP', 'NIL')
                for elem in reversed(val):
                    out = c.List([c.Atom(':CONS'), canon(elem), out])
                return out
            raise TypeError(val)

        def canon_record(name, formals, body=None, justification=':MISSING'):
            fmap = {
                ':FORMALS': canon(formals),
                ':LOGICAL-BODY': canon(body if body is not None else ['QUOTE', 0]),
                ':GUARD': canon(['QUOTE', 'T']),
                ':JUSTIFICATION': canon(justification),
                ':ATTACHMENT': canon('NIL'),
                ':STOBJS-IN': canon(['NIL'] * len(formals)),
                ':STOBJS-OUT': canon(['NIL']),
            }
            row = c.List([c.Atom(':FUNCTION'), canon(name)])
            for k, v in fmap.items():
                row.extend([c.Atom(k), v])
            row = c.read_canonical(c.canonical_text(row))
            fmap = c.fields(row)
            return {'name': name, 'record_sha256': s.canonical_digest(row),
                    'semantic': s.function_semantics(name, row, fmap)}

        custom_just = [
            'JUSTIFICATION',
            ['X'],
            ['NIL', 'CUSTOM-MP', '.', 'CUSTOM-REL'],
            [['BINARY-+', ['MEASURE-HELPER', 'X'], ['QUOTE', 1]], '.', ':ALL'],
        ]
        root = canon_record('ROOT', ['X'], body=['IF', ['CONSP', 'X'], ['ROOT', ['CDR', 'X']], ['QUOTE', 0]],
                            justification=custom_just)
        m_helper = canon_record('MEASURE-HELPER', ['X'], body=['MEASURE-LEAF', 'X'])
        m_leaf = canon_record('MEASURE-LEAF', ['X'])
        c_mp = canon_record('CUSTOM-MP', ['X'])
        c_rel = canon_record('CUSTOM-REL', ['X', 'Y'])

        full = inventory([root, m_helper, m_leaf, c_mp, c_rel], boundary=['CONSP', 'CDR', 'BINARY-+'])
        self.assertEqual({r['name'] for r in full['function_records']},
                         {'ROOT', 'MEASURE-HELPER', 'MEASURE-LEAF', 'CUSTOM-MP', 'CUSTOM-REL'})
        self.assertEqual(full['frontiers'], [])

        # Missing measure callee, missing custom domain/relation, or missing measure native -> explicit frontier
        no_helper = inventory([root, c_mp, c_rel], boundary=['CONSP', 'CDR', 'BINARY-+'])
        self.assertIn('missing function MEASURE-HELPER', no_helper['frontiers'])
        no_rel = inventory([root, m_helper, m_leaf, c_mp], boundary=['CONSP', 'CDR', 'BINARY-+'])
        self.assertIn('missing function CUSTOM-REL', no_rel['frontiers'])
        no_mp = inventory([root, m_helper, m_leaf, c_rel], boundary=['CONSP', 'CDR', 'BINARY-+'])
        self.assertIn('missing function CUSTOM-MP', no_mp['frontiers'])
        no_plus = inventory([root, m_helper, m_leaf, c_mp, c_rel], boundary=['CONSP', 'CDR'])
        self.assertIn('ROOT: primitive absent from canonical boundary BINARY-+', no_plus['frontiers'])

    def test_decode_justification_rejects_malformed_and_subversive_records(self):
        cl_syms = {'NIL', 'T', 'QUOTE', 'IF', 'LAMBDA'}

        def csym(pkg, name):
            return c.read_canonical(
                '(:SYMBOL (' + ' '.join(str(ord(ch)) for ch in pkg) + ') (' +
                ' '.join(str(ord(ch)) for ch in name) + '))'
            )

        def canon(val):
            if isinstance(val, int):
                return c.read_canonical(f'(:INTEGER {val})')
            if isinstance(val, tuple) and len(val) == 2 and val[0] in ('ACL2', 'COMMON-LISP', 'KEYWORD'):
                return csym(val[0], val[1])
            if isinstance(val, str):
                if val.startswith(':'):
                    return csym('KEYWORD', val[1:])
                return csym('COMMON-LISP' if val in cl_syms else 'ACL2', val)
            if isinstance(val, list):
                if len(val) >= 3 and val[-2] == '.':
                    out = canon(val[-1])
                    for elem in reversed(val[:-2]):
                        out = c.List([c.Atom(':CONS'), canon(elem), out])
                    return out
                out = csym('COMMON-LISP', 'NIL')
                for elem in reversed(val):
                    out = c.List([c.Atom(':CONS'), canon(elem), out])
                return out
            raise TypeError(val)

        # Subversive justification (T in wfr car) decodes cleanly as subversive=True and emits frontier
        subv_just = [
            'JUSTIFICATION',
            ['X'],
            ['T', 'O-P', '.', 'O<'],
            [['ACL2-COUNT', 'X'], '.', ':BASIC'],
        ]
        fmap = {
            ':FORMALS': canon(['X']),
            ':LOGICAL-BODY': canon(['QUOTE', 0]),
            ':GUARD': canon(['QUOTE', 'T']),
            ':JUSTIFICATION': canon(subv_just),
            ':ATTACHMENT': canon('NIL'),
            ':STOBJS-IN': canon(['NIL']),
            ':STOBJS-OUT': canon(['NIL']),
        }
        row = c.List([c.Atom(':FUNCTION'), canon('ROOT')])
        for k, v in fmap.items():
            row.extend([c.Atom(k), v])
        row = c.read_canonical(c.canonical_text(row))
        sem = s.function_semantics('ROOT', row, c.fields(row))
        self.assertTrue(sem['justification']['wfr']['subversive'])
        self.assertIn('subversive justification', sem['frontiers'])

        # Valid lambda in measure is accepted
        lam_just = canon([
            'JUSTIFICATION',
            ['X'],
            ['NIL', 'T', '.', 'O<'],
            [[[['LAMBDA', ['Y'], ['ACL2-COUNT', 'Y']], 'X'], ':LAMBDAS'],
             '.', ':ALL'] if False else
            [[['LAMBDA', ['Y'], ['ACL2-COUNT', 'Y']], 'X'], '.', ':LAMBDAS'],
        ])
        parsed_lam = s.decode_justification(lam_just, formals=['X'])
        self.assertEqual(parsed_lam['state'], 'present')
        self.assertEqual(parsed_lam['ruler_extenders'], ':LAMBDAS')

        bad_cases = [
            # Wrong tag package or name
            [('COMMON-LISP', 'JUSTIFICATION'), ['X'], ['NIL', 'O-P', '.', 'O<'], [['ACL2-COUNT', 'X'], '.', ':ALL']],
            ['NOT-JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'O<'], [['ACL2-COUNT', 'X'], '.', ':ALL']],
            # Wrong arity
            ['JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'O<']],
            # Subset outside formals or duplicate or non-variable
            ['JUSTIFICATION', ['Y'], ['NIL', 'O-P', '.', 'O<'], [['ACL2-COUNT', 'Y'], '.', ':ALL']],
            ['JUSTIFICATION', ['X', 'X'], ['NIL', 'O-P', '.', 'O<'], [['ACL2-COUNT', 'X'], '.', ':ALL']],
            ['JUSTIFICATION', [':KW'], ['NIL', 'O-P', '.', 'O<'], [['QUOTE', 0], '.', ':ALL']],
            # Measure variable outside subset
            ['JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'O<'], [['ACL2-COUNT', 'Z'], '.', ':ALL']],
            # Synthetic skipped-proof measure (:? X)
            ['JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'O<'], [[':?', 'X'], '.', ':ALL']],
            # Unquoted integer literal in translated measure term
            ['JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'O<'], [['BINARY-+', 'X', 1], '.', ':ALL']],
            # Bad lambda arity in measure
            ['JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'O<'],
             [[['LAMBDA', ['Y', 'Z'], ['ACL2-COUNT', 'Y']], 'X'], '.', ':ALL']],
            # Bad wfr subversive / mp / rel
            ['JUSTIFICATION', ['X'], [('ACL2', 'NIL'), 'O-P', '.', 'O<'], [['ACL2-COUNT', 'X'], '.', ':ALL']],
            ['JUSTIFICATION', ['X'], ['NIL', 'NIL', '.', 'O<'], [['ACL2-COUNT', 'X'], '.', ':ALL']],
            ['JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'T'], [['ACL2-COUNT', 'X'], '.', ':ALL']],
            # Bad ruler-extenders
            ['JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'O<'], [['ACL2-COUNT', 'X'], '.', ':BOGUS']],
            ['JUSTIFICATION', ['X'], ['NIL', 'O-P', '.', 'O<'], [['ACL2-COUNT', 'X'], 7]],
        ]
        for idx, bad in enumerate(bad_cases):
            with self.subTest(case=idx):
                with self.assertRaises(ValueError):
                    s.decode_justification(canon(bad), formals=['X', 'Z'])

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
