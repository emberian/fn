"""HZ independent finite operator target and wire renderer; mutation controls.

FakeTarget never calls OperatorModel, NntpModel, Expect, wildmat or framing.
It owns its own CLI state and literal protocol bytes. These tests are model
controls, not live fn1/fn2 conformance evidence.
"""
from copy import deepcopy
import fnmatch
import re
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from . import operator_model as oracle
from .operator_model import OperatorModel, Request
from fn2.tests.surface.operator.test_model_operator import Exercise, OperatorTarget, Wire, machine


class FakeTarget:
    def __init__(self, case=None, plant=None):
        self.plant = plant
        self.groups = {g: dict(active=True, desc='(no description)', policy='y', mods=[], queue=None, entries=[], high=0)
                       for g in ('hz.test', 'hz.mod', 'hz.mod.moderation', 'control.cancel')}
        self.file, self.redeemed, self.access, self.held, self.articles = {}, {}, {}, {}, {}
        self.deleted, self.pending, self.motd = set(), [], []
        self.capacity, self.invites, self.retention, self.expiry = 1048576, 0, ('keep-forever',), {}

    def credentials(self):
        return {**deepcopy(self.redeemed), **deepcopy(self.file)}

    def call(self, r):
        v, a = r.verb, r.args
        reason, code = None, 1
        if '' in r.words or any(not x.isascii() for x in r.words):
            reason, code = 'argv-malformed', 5
        elif v == 'group create':
            if '/' in a[0]:
                reason, code = 'syntax', 5
            elif a[0] in self.groups and self.groups[a[0]]['active']:
                reason = 'duplicate-group'
        elif v in ('group retire', 'group describe', 'group policy', 'group moderate'):
            # `retention expire` names a policy for any group or `*` (H7d: fn1 accepts it for an absent one).
            if a[0] not in self.groups or not self.groups[a[0]]['active']:
                reason = 'no-such-group'
            elif v == 'group moderate' and '--off' not in a:
                queue = a[a.index('--queue')+1] if '--queue' in a else a[0] + '.moderation'
                if queue not in self.groups or not self.groups[queue]['active'] or queue == a[0] or self.groups[queue]['mods']:
                    reason = 'moderation-queue'
        elif v == 'capacity':
            if not a[0].isdigit() or int(a[0]) > 4294967295:
                reason, code = 'syntax', 5
            elif int(a[0]) == 0 and self.articles:
                reason = 'capacity-below-reserved'
        elif v == 'account access' and a != ('show',):
            if '[' in a[a.index('--read')+1] or '[' in a[a.index('--post')+1]:
                reason, code = 'access-pattern', 5
        elif v in ('account delete', 'principal delete'):
            if a[0] not in self.file and a[0] not in self.redeemed:
                reason = 'account-unknown'
        elif v in ('moderation approve', 'moderation reject'):
            held = self.held.get(a[0])
            if held is None:
                reason = 'not-held'
            elif a[a.index('--moderator')+1] not in self.groups[held['group']]['mods']:
                reason = 'not-a-moderator'
            elif held['state'] != 'held':
                reason = 'already-' + held['state']
        if self.plant == 'duplicate-create' and reason == 'duplicate-group':
            return dict(exit=0, text='accepted operator ' + v.split()[0] + '\n')
        if reason:
            if self.plant == 'refusal-mutation' and reason == 'duplicate-group':
                self.motd = ['CORRUPTED by refusal']
            word = 'usage' if code == 5 else 'refused'
            return dict(exit=code, text=f'{word} operator {v.split()[0]} (ADMINISTRATION {reason.upper()})\n')
        text = ''
        if v == 'group create':
            self.groups.setdefault(a[0], dict(active=True, desc='(no description)', policy='y', mods=[], queue=None, entries=[], high=0))['active'] = True
        elif v == 'group retire':
            if self.plant != 'retire-visible':
                self.groups[a[0]]['active'] = False
        elif v == 'group describe':
            self.groups[a[0]]['desc'] = ' '.join(a[1:])
        elif v == 'group policy':
            self.groups[a[0]]['policy'] = a[1]
        elif v == 'group moderate':
            g = self.groups[a[0]]
            g['mods'] = [] if '--off' in a else a[a.index('--moderators')+1].split(',')
            g['queue'] = None if '--off' in a else a[a.index('--queue')+1] if '--queue' in a else a[0] + '.moderation'
        elif v in ('motd set', 'motd clear'):
            self.motd = list(a) if v == 'motd set' else []
        elif v == 'capacity':
            self.capacity = int(a[0])
        elif v == 'retention set':
            self.retention = a
        elif v == 'retention expire':
            if a[1:] == ('clear',):
                self.expiry.pop(a[0], None)
            else:
                self.expiry[a[0]] = a[1:]
        elif v == 'account invite':
            self.invites += 1
            token = '%032x' % self.invites
            self.pending.append(token)
            text += token + '\n'
        elif v in ('account set-password', 'principal set-password'):
            self.file[a[0]] = dict(password=r.password, posting='--no-posting' not in a)
        elif v in ('account delete', 'principal delete'):
            if a[0] in self.file:
                del self.file[a[0]]
            else:
                del self.redeemed[a[0]]
                self.deleted.add(a[0])
        elif v == 'account access' and a != ('show',):
            self.access[a[0]] = (a[a.index('--read')+1], a[a.index('--post')+1])
        elif v in ('account list', 'account access'):
            text += ''.join('redeemed ' + login + ' ' + 'a'*64 + '\n' for login in self.redeemed)
            text += ''.join('deleted ' + login + '\n' for login in self.deleted)
            text += ''.join('pending expires 2026-12-31T12:00:00Z\n' for _ in self.pending)
            text += ''.join(f'access {login} read {rd} post {post}\n' for login, (rd, post) in self.access.items())
        elif v == 'principal list':
            text += ''.join(login + ' principal=' + 'b'*64 + ' posting=' + str(row['posting']).lower() + '\n'
                            for login, row in sorted(self.file.items()))
        elif v == 'moderation list' and not self.groups.get(a[0], {}).get('mods'):
            text += f'moderation group={a[0]} moderated=no\n'
        elif v == 'moderation list':
            g = self.groups[a[0]]
            held = [(ident, h) for ident, h in self.held.items() if h['group'] == a[0]]
            text += f'moderation group={a[0]} queue={g["queue"]} held={sum(h["state"] == "held" for _, h in held)}\n'
            text += ''.join(f'{h["state"]} envelope={h["envelope"]} message-id={ident}\n' for ident, h in held)
        elif v in ('moderation approve', 'moderation reject'):
            h = self.held[a[0]]
            h['state'] = 'approved' if v.endswith('approve') else 'rejected'
            if v.endswith('approve'):
                if self.plant != 'approve-unreadable':
                    self.add(a[0], h['source'], h['group'])
            else:
                self.articles[h['envelope']]['withdrawn'] = True
                self.add('<fn-withdraw.' + h['envelope'][1:], b'\r\n', 'control.cancel')
        return dict(exit=0, text=text + 'accepted operator ' + v.split()[0] + '\n')

    def add(self, ident, source, group):
        self.groups[group]['high'] += 1
        self.groups[group]['entries'].append((self.groups[group]['high'], ident))
        self.articles[ident] = dict(source=source, group=group, withdrawn=False)

    def status(self):
        return dict(exit=0, text='charge-capacity=' + str(self.capacity))

    def open(self):
        return FakeWire(self)


class FakeWire:
    greeting = b'200 ready\r\n'

    def __init__(self, target):
        self.t = target
        self.login, self.user, self.redeem, self.current = None, None, None, None
        self.reply_body = b''
        self.creds = target.credentials()

    def allowed(self, group, post=False):
        if self.t.plant == 'access-unenforced':
            return True
        patterns = self.t.access.get(self.login, ('*', '*'))[int(post)]
        allowed = False
        for part in patterns.split(','):
            if fnmatch.fnmatchcase(group, part.lstrip('!')):
                allowed = not part.startswith('!')
        return allowed

    def visible(self, name):
        g = self.t.groups.get(name)
        if not g or not g['active'] or not self.allowed(name):
            return False
        owners = [f for f in self.t.groups.values() if f['queue'] == name]
        return not owners or any(self.login in f['mods'] for f in owners)

    def rows(self, name):
        return [(n, i) for n, i in self.t.groups[name]['entries'] if not self.t.articles[i]['withdrawn']]

    def status_flag(self, name):
        g = self.t.groups[name]
        return 'n' if g['policy'] == 'n' or not self.allowed(name, True) else 'm' if g['mods'] else 'y'

    def command(self, raw):
        words = raw.decode().split()
        cmd, args = words[0], words[1:]
        if cmd == 'QUIT':
            return b'205 closing\r\n'
        if cmd == 'AUTHINFO':
            if args[0] == 'USER':
                self.user = args[1]
                return b'381 password\r\n'
            if self.user in self.creds and self.creds[self.user]['password'] == args[1]:
                self.login = self.user
                return b'281 authenticated\r\n'
            return b'481 rejected\r\n'
        if cmd == 'XREDEEM':
            if args[0] == 'PASS':
                code, login = self.redeem
                self.t.pending.remove(code)
                self.t.redeemed[login] = dict(password=args[1], posting=True)
                return b'281 redeemed\r\n'
            self.redeem = args
            return b'381 password\r\n'
        if cmd == 'LIST':
            if args[0] == 'MOTD':
                lines = self.t.motd
            elif args[0] == 'NEWSGROUPS':
                lines = [g + '\t' + f['desc'] for g, f in self.t.groups.items() if self.visible(g)]
            else:
                lines = []
                for g, f in self.t.groups.items():
                    if self.visible(g):
                        rows = self.rows(g)
                        low, high = (rows[0][0], rows[-1][0]) if rows else (f['high']+1, f['high'])
                        lines.append(f'{g} {high} {low} {self.status_flag(g)}')
            self.reply_body = ''.join(('.' if x.startswith('.') else '') + x + '\r\n' for x in lines).encode() + b'.\r\n'
            return b'215 listing\r\n'
        if cmd == 'GROUP':
            g = args[0]
            if not self.visible(g):
                return b'411 no group\r\n'
            self.current = g
            rows = self.rows(g)
            low, high = (rows[0][0], rows[-1][0]) if rows else (self.t.groups[g]['high']+1, self.t.groups[g]['high'])
            return f'211 {len(rows)} {low} {high} {g}\r\n'.encode()
        if cmd in ('STAT', 'BODY'):
            ident = args[0]
            found = self.t.articles.get(ident)
            if found is None or not self.visible(found['group']):
                return b'430 no article\r\n'
            if found['withdrawn']:
                return b'430 withdrawn\r\n'
            if cmd == 'BODY':
                body = found['source'].partition(b'\r\n\r\n')[2]
                self.reply_body = body + b'.\r\n'
            return f'{223 if cmd == "STAT" else 222} 0 {ident}\r\n'.encode()
        if cmd == 'POST':
            if self.login and not self.creds[self.login]['posting']:
                return b'440 posting not permitted\r\n'
            return b'340 send article\r\n'
        raise AssertionError('fake unsupported wire ' + repr(raw))

    def post_body(self, data):
        source = data[:-3]
        ident = re.search(rb'Message-ID: ([^\r]+)', source)[1].decode()
        group = re.search(rb'Newsgroups: ([^\r]+)', source)[1].decode()
        if not self.visible(group) or not self.allowed(group, True) or self.status_flag(group) == 'n':
            return b'441 group read-only\r\n'
        g = self.t.groups[group]
        if g['mods']:
            envelope = '<fn-moderate.' + ident[1:]
            self.t.add(envelope, source, g['queue'])
            self.t.held[ident] = dict(group=group, envelope=envelope, source=source, state='held')
        else:
            self.t.add(ident, source, group)
        return b'240 accepted\r\n'

    def block(self):
        return self.reply_body

    def close(self):
        pass


class OperatorTests(unittest.TestCase):
    def test_fixed_witnesses_each_verb_and_refusal(self):
        exercise = Exercise(self, FakeTarget())
        exercise.witnesses()
        self.assertEqual(exercise.checked_verbs, {(v, r) for v in OperatorModel.VERBS for r in (False, True)})

    def test_generated_composition(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        run_state_machine_as_test(machine(self, FakeTarget), settings=settings(
            max_examples=30, stateful_step_count=30, deadline=None, database=None, derandomize=True))

    def test_mutation_controls(self):
        controls = ('retire-visible', 'duplicate-create', 'access-unenforced', 'approve-unreadable', 'refusal-mutation')
        for plant in controls:
            with self.subTest(plant=plant):
                exercise = Exercise(self, FakeTarget(plant=plant))
                with patch('fn2.tests.surface.operator.test_model_operator.record_failure') as record:
                    with self.assertRaises(AssertionError):
                        exercise.witnesses()
                    self.assertTrue(record.called)
                    self.assertIsNotNone(record.call_args_list[0].kwargs['reply'])

    def test_adjudication_rows_are_recorded_and_scoped(self):
        for row in oracle.ADJUDICATIONS:
            self.assertIn(row['class'], ('fn1-bug', 'spec-ambiguity'))
            self.assertIn(row['verb'], OperatorModel.VERBS)
            self.assertTrue(row['group'] and row['spec'] and row['fn1_reply'])

    def test_effect_row_follows_fn1_only(self):
        reply = dict(exit=0, text='accepted operator group ACCEPTED\n')
        for target, retired in (('fn1', None), ('fn2', True), ('fake', True)):
            with self.subTest(target=target):
                model = OperatorModel()
                model.groups['hz.test']['description'] = 'kept unless fn1'
                recorded = model.rule('group retire', 'hz.test').update(reply, target)
                self.assertEqual('description' in model.groups['hz.test'], target != 'fn1')
                self.assertEqual(model.groups['hz.test'].get('retired'), retired)
                self.assertEqual(recorded is not None, target == 'fn1')
        # A refused retire never matches the effect row.
        model = OperatorModel()
        self.assertIsNone(model.rule('group retire', 'hz.absent').recorded_difference(
            dict(exit=1, text='refused operator group REFUSED no-such-group\n'), 'fn1'))

    def test_scoped_refusal_match(self):
        model = OperatorModel()
        expected = model.rule('group describe', 'absent', 'text')
        row = dict(group='TEST-ONLY', verb='group describe', argument_class='unknown-group',
                   exit=5, reason='other', **{'class': 'fn1-bug'})
        reply = dict(exit=5, text='usage operator group (ADMINISTRATION OTHER)\n')
        before = deepcopy(model.groups)
        # Synthetic matcher control, never a recorded fn1 observation.
        with patch.object(oracle, 'ADJUDICATIONS', (row,)):
            self.assertIsNotNone(expected.recorded_difference(reply, 'fn1'))
            self.assertIsNone(expected.recorded_difference(reply, 'fn2'))
            self.assertIsNone(expected.recorded_difference(reply, 'fake'))
            expected.update(reply, 'fn1')
            for changed in (dict(reply, exit=4), dict(reply, text='OTHER'),
                            dict(reply, text='usage operator group (ADMINISTRATION OTHER-SUFFIX)\n')):
                self.assertIsNone(expected.recorded_difference(changed, 'fn1'))
            self.assertIsNone(model.rule('group retire', 'absent').recorded_difference(reply, 'fn1'))
            self.assertIsNone(model.rule('group describe', 'hz.test', '').recorded_difference(reply, 'fn1'))
        with patch.object(oracle, 'ADJUDICATIONS', ({**row, 'class': 'spec-ambiguity'},)):
            self.assertIsNotNone(expected.recorded_difference(reply, 'fn2'))
            self.assertIsNone(expected.recorded_difference(reply, 'fake'))
        self.assertEqual(model.groups, before)

    def test_constructor_owns_ports_and_pins_store_init(self):
        from fn2.tests.model.limits_model import STORE_INIT
        calls = []
        class Node:
            def __init__(self, case, image):
                calls.append(('node', image))
            def operator(self, *args, **kwargs):
                calls.append((args, kwargs))
                return SimpleNamespace(returncode=0, stdout=b'ok', stderr=b'')
            def start(self, **kwargs):
                calls.append(('start', kwargs))
        with patch('tests.native_harness.Node', Node), patch('tests.native_harness.native_image', return_value='fake-image'):
            target = OperatorTarget(self)
        args, kwargs = calls[1]
        self.assertEqual(args[:3], ('init', '--profile', 'development'))
        for key, value in STORE_INIT.items():
            self.assertEqual(args[args.index('--' + key)+1], str(value))
        self.assertEqual(kwargs['timeout'], 10)
        self.assertTrue(hasattr(OperatorTarget.__init__, '__wrapped__'))
        self.assertIsInstance(target.node, Node)

    def test_multiline_bounded_even_without_tcp(self):
        sock = SimpleNamespace(settimeout=lambda _: None)
        client = SimpleNamespace(sock=sock, greeting=b'200 ready\r\n', line=lambda **_: b'x\r\n')
        with self.assertRaisesRegex(AssertionError, 'line budget'):
            Wire(client).block()

    def test_capacity_zero_after_durable_post_and_u32_boundary(self):
        model = OperatorModel()
        self.assertEqual(model.rule('capacity', '0').exit, 0)
        model.wire.add_article('<test@surface.invalid>', b'a\r\n\r\nb\r\n', ['hz.test'])
        self.assertEqual(model.rule('capacity', '0').reason, 'capacity-below-reserved')
        self.assertEqual(model.rule('capacity', '4294967296').exit, 5)
        self.assertEqual(model.rule('capacity', '4294967295').exit, 0)

    def test_principal_list_is_not_success_only(self):
        model = OperatorModel()
        model.rule('principal set-password', 'hz-check', '--no-posting', password='hz-test-password').update(dict(exit=0, text='accepted operator principal\n'))  # FAKE-SECRET
        expected = model.rule('principal list')
        for text in ('accepted operator principal\n', 'hz-check principal=' + 'a'*64 + ' posting=true\naccepted operator principal\n'):
            self.assertIsNotNone(expected.check(dict(exit=0, text=text)))
        self.assertIsNone(expected.check(dict(exit=0, text='hz-check principal=' + 'a'*64 + ' posting=false\naccepted operator principal\n')))
