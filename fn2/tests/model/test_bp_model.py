"""BP S: an independent finite carry/obligation store and its route table; mutation controls.

FakeTarget never calls BpModel or its helpers: it owns its works, pins, holds, boundaries and routes
and renders fn1's literal reply shapes. These are model controls, not live fn1/fn2 conformance evidence.
"""
import re
import unittest
from unittest.mock import patch

from .bp_model import BpModel, bp_reason, carry_line, eid_shape
from fn2.tests.surface.bp.test_model_bp import Exercise, machine


class FakeTarget:
    adjudication_target = 'fake'

    def __init__(self, case=None, plant=None):
        self.plant, self.listen, self.dead = plant, 40100, 40101
        self.works, self.order, self.boundaries, self.routes = {}, [], {}, {}

    @staticmethod
    def ok(subject, line=''):
        return dict(exit=0, text=(line + '\n' if line else '') + f'accepted operator {subject}\n')

    @staticmethod
    def refuse(work, reason):
        return dict(exit=1, text=f'refused operator carry carry refused reason={reason} work={work}\n')

    def line(self, name):
        w = self.works[name]
        text = (f"carry {name} message-id={w['msgid']} peer=dtn://fn-b/ status={w['status']} "
                f"pinned={'yes' if w['pinned'] else 'no'} hold={w['hold']}")
        if w['reason']:
            text += ' reason=' + w['reason']
        if w['waiver'] and self.plant != 'list-hides-waiver':
            text += ' waived-by=uid:%d waiver=%s' % (self.uid, w['waiver'])
        if w['attempt']:
            text += f" attempt={w['attempt']} transport=restart-observed"
        return text

    @property
    def uid(self):
        import os
        return os.geteuid()

    def enqueue(self, serial, work, msgid):
        if work in self.works:
            return dict(exit=1, text='store: ACL2 rejected application journal enqueue before publication\n')
        self.works[work] = dict(msgid=msgid, status='outstanding', pinned=False, hold='none', reason=None,
                                waiver=None, attempt=None)
        self.order.insert(0, work)
        return dict(exit=0, text=f'workflow durable work={work} status=outstanding\n')

    def peer_list(self):
        rows = []
        for name, (path, eid, carries, releases) in sorted(self.boundaries.items()):
            row = (f'{name} path-identity={path} address={eid} port=0 security=- inbound=- outbound=- '
                   f'auth=principal:bp-only-no-nntp-principal')
            row += (' carries=' + ' '.join(carries)) if carries else ''
            row += (' releases-for=' + ' '.join(releases)) if releases else ''
            rows.append(row + '\n')
        return dict(exit=0, text=''.join(rows) + 'accepted operator peer\n')

    def call(self, r):
        v, a = r.verb, list(r.args)
        if not v.startswith('bp-obligation') and any(not w for w in a):
            return dict(exit=5, text='usage operator request ARGV-MALFORMED\n')
        if v.startswith('carry '):
            return self.carry(v.split()[1], a)
        if v.startswith('bp-obligation '):
            return self.obligation(v.split()[1], a)
        if v == 'bp-boundary add':
            shaped = a[2].startswith(('dtn://', 'ipn:')) or (a[2] == 'dtn:none' and self.plant == 'eid-unchecked')
            if not shaped:
                return dict(exit=5, text='usage: ...\nusage operator bp-boundary (ADMINISTRATION BP-BOUNDARY)\n')
            words = a[4:]
            contact = words[1] if words[:1] == ['contact'] else None
            words = words[2:] if contact else words
            carries = words[1:words.index('releases-for')] if 'carries' in words and 'releases-for' in words else \
                words[1:] if words[:1] == ['carries'] else []
            releases = words[words.index('releases-for') + 1:] if 'releases-for' in words else []
            self.boundaries[a[0]] = (a[1], a[2], carries, releases)
            return self.ok('bp-boundary', 'configured generation=2 record=00000002.cfg verification=VERIFIED')
        if v == 'bp-route add':
            if ' ' in a[0] or not a[0].startswith(('dtn://', 'ipn:')) or (len(a) == 3 and not a[2].isdigit()):
                return dict(exit=5, text='usage operator bp-route (ADMINISTRATION BP-ROUTE)\n')
            self.routes[(a[0], a[1])] = int(a[2]) if len(a) == 3 else 100
            return self.ok('bp-route')
        if v == 'bp-route remove':
            if (a[0], a[1]) not in self.routes:
                return dict(exit=1, text='refused operator bp-route administrative configuration refused: NO-SUCH-PEER\n')
            del self.routes[(a[0], a[1])]
            return self.ok('bp-route')
        raise AssertionError('fake unsupported ' + v)

    def carry(self, sub, a):
        if sub == 'list':
            return dict(exit=0, text=''.join(self.line(n) + '\n' for n in self.order) + 'accepted operator carry\n')
        if sub in ('drop', 'abandon') and len(a) < 2:
            return dict(exit=5, text='usage operator carry INVALID-CARRY-COMMAND\n')
        if a[0] == '*' and sub in ('pause', 'resume'):
            want = 'none' if sub == 'pause' else 'paused'
            hits = [w for w in self.works.values() if w['hold'] == want]
            if not hits:
                return self.refuse('*', 'already-paused' if sub == 'pause' else 'not-paused')
            for w in hits:
                w['hold'] = 'paused' if sub == 'pause' else 'none'
            return self.ok('carry', f'BP carry durable {sub} work=*')
        w = self.works.get(a[0])
        if w is None:
            return self.refuse(a[0], 'unknown-work')
        if sub == 'inspect':
            return dict(exit=0, text=self.line(a[0]) + '\naccepted operator carry\n')
        closed = w['hold'] in ('dropped', 'waived')
        if sub == 'pause':
            if closed:
                return self.refuse(a[0], 'dropped')
            if w['hold'] == 'paused':
                return self.refuse(a[0], 'already-paused')
            w['hold'] = 'paused'
        elif sub == 'resume':
            if closed and self.plant != 'resume-dropped':
                return self.refuse(a[0], 'dropped')
            if w['hold'] == 'none':
                return self.refuse(a[0], 'not-paused')
            w['hold'] = 'none'
        elif sub == 'drop':
            if closed:
                return self.refuse(a[0], 'already-dropped')
            w.update(hold='dropped', reason=' '.join(a[1:]))
            if self.plant == 'drop-releases-pin':
                w['pinned'] = False
        elif sub == 'abandon':
            if w['hold'] == 'waived' and self.plant != 'abandon-twice':
                return self.refuse(a[0], 'already-waived')
            if not w['pinned'] and self.plant != 'abandon-twice':
                return self.refuse(a[0], 'not-held')
            w.update(hold='waived', waiver=' '.join(a[1:]), pinned=False, reason=w['reason'] or ' '.join(a[1:]))
        return self.ok('carry', f'BP carry durable {sub} work={a[0]}')

    def obligation(self, sub, a):
        w = self.works.get(a[0]) if a else None
        if sub == 'status':
            if w is None:
                return dict(exit=0, text=f'BP obligation owner work={a[0]} status=absent pinned=no\n')
            return dict(exit=0, text=f"BP obligation owner work={a[0]} status={w['status']} pinned={'yes' if w['pinned'] else 'no'}\n")
        if sub == 'undertake':
            if w is None or w['pinned'] or (w['hold'] == 'waived' and self.plant != 'undertake-waived'):
                return dict(exit=1, text='store: workflow forwarding obligation is not admissible\n')
            w['pinned'] = True
            return dict(exit=0, text=f'BP obligation owner durable undertaking work={a[0]} charge={a[1]}\n')
        if sub == 'receipt':
            if self.plant == 'receipt-releases':
                for work in self.works.values():
                    work['pinned'] = False
                return dict(exit=0, text='BP receipt durable\n')
            return dict(exit=1, text='store: workflow receipt authentication profile is unsupported\n')
        if sub == 'request':
            refusal = ('carry-paused' if w['hold'] == 'paused' and self.plant != 'paused-request-attempts' else
                       'carry-dropped' if w['hold'] in ('dropped', 'waived') else
                       'forward-pin-not-durable' if not w['pinned'] else None)
            if refusal:
                return dict(exit=1, text=f'store: ACL2 refused a request for work {a[0]} attempt {a[1]} reason={refusal}\n')
            w.update(attempt=a[1], status='restart-observed')
            head = f'BP obligation request durable attempt work={a[0]} attempt={a[1]} generation=0 destination=dtn://fn-b/ adu=258\n'
            hops = [(p, b) for (p, b) in self.routes if b in self.boundaries and
                    ('dtn://fn-b/' == p or p.endswith('*') and 'dtn://fn-b/'.startswith(p[:-1]))]
            if not hops and self.plant != 'route-ignored':
                return dict(exit=1, text=head + 'BP queue route destination=dtn://fn-b/ decision=no-route (not queued; the obligation stays)\n')
            return dict(exit=7, text=head + f'BP queue accepted work={a[0]} attempt={a[1]} generation=1 status=durable\n'
                                          'BP forwarding retained reason=failed\n')
        raise AssertionError('fake unsupported bp-obligation ' + sub)


class BpTests(unittest.TestCase):
    def test_fixed_witnesses_each_verb_and_refusal(self):
        exercise = Exercise(self, FakeTarget())
        exercise.witnesses()
        self.assertTrue(len(exercise.checked_verbs) >= 2 * len(BpModel.VERBS) - 3)

    def test_generated_composition(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        run_state_machine_as_test(machine(self, FakeTarget), settings=settings(
            max_examples=25, stateful_step_count=30, deadline=None, database=None, derandomize=True))

    def test_mutation_controls(self):
        controls = ('drop-releases-pin', 'abandon-twice', 'paused-request-attempts', 'resume-dropped',
                    'route-ignored', 'receipt-releases', 'list-hides-waiver', 'undertake-waived', 'eid-unchecked')
        for plant in controls:
            with self.subTest(plant=plant):
                exercise = Exercise(self, FakeTarget(plant=plant))
                with patch('fn2.tests.surface.bp.test_model_bp.record_failure') as record:
                    with self.assertRaises(AssertionError):
                        exercise.witnesses()
                    self.assertTrue(record.called)

    def test_reasons_and_lines(self):
        text = ('OWNER-OPEN open=full-replay reason=absent ms=12\n'
                'refused operator carry carry refused reason=already-paused work=work-1\n')
        self.assertEqual(bp_reason(text), 'already-paused')
        self.assertEqual(bp_reason('OWNER-OPEN reason=absent\nstore: ACL2 refused a request for work w attempt a '
                                   'reason=carry-paused\n'), 'carry-paused')
        name, fields = carry_line('carry w message-id=<m@x> peer=dtn://fn-b/ status=outstanding pinned=no '
                                  'hold=waived reason=peer retired waived-by=uid:1000 waiver=peer gone')
        self.assertEqual((name, fields['reason'], fields['waiver'], fields['waived-by']),
                         ('w', 'peer retired', 'peer gone', 'uid:1000'))
        for good in ('dtn://fn-b/', 'ipn:7.1', 'dtn://n/x/y'):
            self.assertTrue(eid_shape(good), good)
        for bad in ('dtn:none', 'DTN://x/', 'not an eid', 'ipn:01.1', 'dtn:///x'):
            self.assertFalse(eid_shape(bad), bad)

    def test_pin_moves_only_at_undertake_and_waiver(self):
        model = BpModel(uid=1000)
        model.enqueued('w', '<m@x>')
        ok = lambda verb, *args, text='accepted operator carry\n', code=0: model.rule(verb, *args).update(
            dict(exit=code, text=text))
        self.assertFalse(model.works['w']['pinned'])
        ok('bp-obligation undertake', 'w', '3', text='BP obligation owner durable undertaking work=w charge=3\n')
        self.assertTrue(model.works['w']['pinned'])
        ok('carry drop', 'w', 'retired')
        self.assertTrue(model.works['w']['pinned'])
        model.rule('bp-obligation receipt').update(dict(exit=1, text='store: unsupported\n'))
        self.assertTrue(model.works['w']['pinned'])
        ok('carry abandon', 'w', 'gone')
        self.assertFalse(model.works['w']['pinned'])
        self.assertEqual(model.works['w']['reason'], 'retired')
