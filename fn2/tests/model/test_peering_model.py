"""Peering S: an independent finite peering node and its scripted peers; mutation controls.

FakeTarget never calls PeeringModel, NntpModel, Expect, wildmat or framing: it owns its peer table,
its literal CLI and wire bytes, and delivers its feed synchronously to its own instruments. These are
model controls, not live fn1/fn2 conformance evidence.
"""
import fnmatch
import re
import time
import unittest
from unittest.mock import patch

from .peering_model import PeeringModel, peer_reason, distribution_fed
from fn2.tests.surface.peering.test_model_peering import SOURCE_OWN, Exercise, machine

def match(pattern, value):
    result = False
    for part in pattern.split(','):
        if fnmatch.fnmatchcase(value, part.lstrip('!')):
            result = not part.startswith('!')
    return result


class Instrument:
    def __init__(self, port, mode_stream, own=None):
        self.port, self.mode_stream, self.own = port, mode_stream, dict(own or {})
        self.received, self.connections = {}, []

    def deliver(self, ident, streaming, login, force_ihave=False):
        start = time.monotonic()
        commands = (['AUTHINFO USER me'] if login else []) + (['MODE STREAM'] if streaming else [])
        streams = streaming and self.mode_stream and not force_ihave
        commands += ['CHECK ' + ident, 'TAKETHIS ' + ident] if streams else ['IHAVE ' + ident]
        self.connections.append(dict(start=start, commands=commands))
        self.received.setdefault(ident, time.monotonic())

    def snapshot(self):
        return dict(self.received), [dict(c) for c in self.connections]

    def close(self):
        pass


class FakeTarget:
    adjudication_target = 'fake'

    def __init__(self, case=None, plant=None):
        self.plant = plant
        self.instruments = dict(fa=Instrument(40001, True), fb=Instrument(40002, False),
                                src=Instrument(40003, True, SOURCE_OWN))
        self.peers, self.groups, self.articles = {}, {g: [] for g in ('hz.peer', 'hz.test', 'hz.other')}, {}
        self.held = {}

    # -- CLI -----------------------------------------------------------------------------------
    def call(self, r):
        words = r.words
        def out(code, tag=None, live=False):
            if code == 0:
                return dict(exit=0, text='accepted operator peer ACCEPTED\n')
            if code == 5:
                return dict(exit=5, text=f'usage: fn operator CONFIG peer ...\nusage operator peer (ADMINISTRATION {tag.upper()})\n')
            if live:
                return dict(exit=1, text=f'refused operator peer REFUSED {tag}\n')
            return dict(exit=1, text=f'refused operator peer administrative configuration refused: {tag.upper()}\n')
        if any(not w or not w.isascii() for w in words):
            return out(5, 'argv-malformed')
        verb, a = words[1], list(words[2:])
        num = lambda w: w.isdigit() and (w == '0' or not w.startswith('0'))
        if verb == 'list':
            if a:
                return out(5, 'syntax')
            rows = []
            for name, p in sorted(self.peers.items()):
                row = (f"{name} path-identity={p['path']} address={p['host']} port={p['port']} security=clear "
                       f"inbound={p['in']} outbound={p['out']} auth={p['kind']}:{p['value']}")
                if p.get('budget'):
                    octets = p['budget'][0] if self.plant == 'budget-unrounded' else p['budget'][0] // 4096 * 4096
                    row += f" budget-octets={octets} budget-count={p['budget'][1]}"
                rows.append(row + '\n')
            return dict(exit=0, text=''.join(rows) + 'accepted operator peer\n')
        if verb == 'add':
            if len(a) != 9 or '_' in a[2] or not num(a[3]) or a[8] not in ('true', 'false') or not (
                    a[6] == 'principal' and re.fullmatch('[0-9a-f]{64}', a[7]) or a[6] == 'source-address'):
                if self.plant == 'refused-add-applies' and len(a) == 9:
                    self.peers[a[0]] = dict(path=a[1], host=a[2], port=a[3], **{'in': a[4], 'out': a[5]},
                                            kind=a[6], value=a[7], streaming=a[8] == 'true', paused=False)
                return out(5, 'syntax')
            self.peers[a[0]] = dict(path=a[1], host=a[2], port=a[3], **{'in': a[4], 'out': a[5]}, kind=a[6],
                                    value=a[7], streaming=a[8] == 'true', paused=False, dist=None, login=None)
            return out(0)
        if not a:
            return out(5, 'syntax')
        checks = dict(feed=len(a) == 2 and a[1] in ('pause', 'resume'),
                      distributions=len(a) == 2 and '[' not in a[1],
                      budget=len(a) == 3 and num(a[1]) and num(a[2]),
                      pull=len(a) in (2, 3) and all(num(w) for w in a[1:]),
                      **{'pull-login': len(a) == 3 and a[2] in ('true', 'false'),
                         'catch-up': len(a) == 2 and num(a[1])})
        if not checks.get(verb, True):
            return out(5, verb)
        if verb == 'set' and (len(a) % 2 == 0 or any(f not in ('--port', '--take', '--send', '--streaming',
                                                                '--host') for f in a[1::2])):
            return out(5, 'unknown-flag')
        if a[0] not in self.peers:
            return out(1, 'no-such-peer')
        p = self.peers[a[0]]
        if verb == 'remove':
            if self.plant != 'remove-keeps-record':
                del self.peers[a[0]]
            return out(0)
        if verb == 'set':
            edit = dict(zip(a[1::2], a[2::2]))
            if edit.get('--port') == '0':
                return out(1, 'port')
            if edit.get('--send', p['out']) == '-' and '--streaming' in edit:
                return out(1, 'needs-send', live=True)
            for flag, value in edit.items():
                key = {'--take': 'in', '--send': 'out'}.get(flag, flag[2:])
                p[key] = value == 'true' if flag == '--streaming' else value
            return out(0)
        if verb == 'login':
            if p['out'] == '-':
                return out(1, 'needs-send', live=True)
            first, second = r.password
            if first != second:
                return dict(exit=1, text='Password: Confirm password: refused operator peer peer login refused: passwords-differ\n')
            p['login'] = a[2]
            return dict(exit=0, text=f'login peer={a[0]} file={a[2]}\nPassword: Confirm password: accepted operator peer ACCEPTED\n')
        if verb == 'feed':
            p['paused'] = a[1] == 'pause'
            if not p['paused']:
                for ident in sorted(self.held.pop(a[0], set())):
                    self.feed_one(a[0], ident)
            return out(0)
        if verb == 'distributions':
            p['dist'] = a[1]
        elif verb == 'budget':
            p['budget'] = (int(a[1]), int(a[2]))
        elif verb == 'pull' and a[1] != '0':
            self.pull(a[0])
        return out(0)

    def pull(self, name):
        p = self.peers[name]
        own = self.instruments['src'].own if int(p['port']) == 40003 else {}
        for ident, data in own.items():
            groups = re.search(rb'Newsgroups: ([^\r]+)', data)[1].decode().split(',')
            scope = groups if self.plant == 'pull-out-of-scope' else [g for g in groups if match(p['in'], g)]
            if scope and ident not in self.articles:
                self.file(ident, data, [g for g in scope if g in self.groups])

    def fed(self, p, groups, data):
        if self.plant == 'feed-wrong-groups':
            return True
        if p['out'] == '-' or not any(match(p['out'], g) for g in groups):
            return False
        if p['dist'] is None or self.plant == 'distribution-ignored':
            return True
        field = re.search(rb'(?im)^Distribution: ([^\r]+)', data)
        return field is None or any(match(p['dist'].lower(), d.strip().lower()) for d in field[1].decode().split(','))

    def feed_one(self, name, ident):
        p = self.peers[name]
        slot = next((s for s, i in self.instruments.items() if str(i.port) == p['port']), None)
        if slot is None:
            return
        self.instruments[slot].deliver(ident, p['streaming'], p['login'], self.plant == 'stream-ihave')

    def file(self, ident, data, groups):
        self.articles[ident] = data
        for g in groups:
            self.groups[g].append(ident)

    def post(self, ident, data, group):
        self.file(ident, data, [group])
        for name, p in self.peers.items():
            if self.fed(p, [group], data):
                if p['paused'] and self.plant != 'pause-ignored':
                    self.held.setdefault(name, set()).add(ident)
                else:
                    self.feed_one(name, ident)
        return dict(exit=0, text='accepted operator post\n')

    def scratch(self, name):
        return '/fake/' + name

    def open(self):
        return FakeWire(self)


class FakeWire:
    greeting = b'200 fake peering node\r\n'

    def __init__(self, t):
        self.t, self.body, self.pending = t, b'', None
        self.peer = next((p for p in t.peers.values() if p['kind'] == 'source-address' and p['in'] != '-'), None)

    def command(self, raw):
        words = raw.decode().split()
        cmd, args = words[0].upper(), words[1:]
        if cmd == 'QUIT':
            return b'205 bye\r\n'
        if cmd == 'GROUP':
            rows = self.t.groups[args[0]]
            return (f'211 {len(rows)} 1 {len(rows)} {args[0]}\r\n' if rows else f'211 0 1 0 {args[0]}\r\n').encode()
        if cmd in ('STAT', 'BODY'):
            data = self.t.articles.get(args[0])
            if data is None:
                return b'430 no article with that message-id\r\n'
            if cmd == 'BODY':
                body = data.partition(b'\r\n\r\n')[2]
                self.body = b''.join(b'.' + r if r.startswith(b'.') else r for r in body.splitlines(True)) + b'.\r\n'
                return f'222 0 {args[0]} body follows\r\n'.encode()
            return f'223 0 {args[0]} retrieved\r\n'.encode()
        if cmd in ('IHAVE', 'CHECK', 'MODE') and self.peer is None:
            return b'501 syntax error\r\n' if cmd == 'MODE' else b'502 transit is not permitted on this connection\r\n'
        if cmd == 'MODE':
            return b'203 streaming permitted\r\n'
        if cmd == 'IHAVE':
            if args[0] in self.t.articles:
                return b'435 duplicate\r\n'
            self.pending = ('IHAVE', args[0])
            return b'335 send it\r\n'
        if cmd == 'CHECK':
            return (b'438 ' if args[0] in self.t.articles else b'238 ') + args[0].encode() + b'\r\n'
        raise AssertionError('fake unsupported wire ' + repr(raw))

    def send(self, data):
        if data.startswith(b'TAKETHIS '):
            head, _, data = data.partition(b'\r\n')
            self.pending = ('TAKETHIS', head.split()[1].decode())
        verb, ident = self.pending
        self.pending = None
        article = data[:-3].replace(b'\r\n..', b'\r\n.')
        groups = re.search(rb'Newsgroups: ([^\r]+)', article)[1].decode().split(',')
        scope = [g for g in groups if g in self.t.groups and
                 (self.t.plant == 'scope-ignored' or match(self.peer['in'], g))]
        ok = scope and ident not in self.t.articles
        if ok:
            self.t.file(ident, article, scope)
        if verb == 'TAKETHIS':
            return (b'239 ' if ok else b'439 ') + ident.encode() + b'\r\n'
        return b'235 transferred\r\n' if ok else b'437 transfer rejected; no newsgroup accepted from this peer\r\n'

    def block(self):
        return self.body

    def close(self):
        pass


class PeeringTests(unittest.TestCase):
    def test_fixed_witnesses_each_verb_and_refusal(self):
        exercise = Exercise(self, FakeTarget())
        with patch('fn2.tests.surface.peering.test_model_peering.SETTLE', 0.05), \
                patch('fn2.tests.surface.peering.test_model_peering.time.sleep'):
            exercise.witnesses()
        self.assertEqual(exercise.checked_verbs, {(v, r) for v in PeeringModel.VERBS for r in (False, True)})

    def test_generated_composition(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        with patch('fn2.tests.surface.peering.test_model_peering.SETTLE', 0.05), \
                patch('fn2.tests.surface.peering.test_model_peering.time.sleep'):
            run_state_machine_as_test(machine(self, FakeTarget), settings=settings(
                max_examples=20, stateful_step_count=25, deadline=None, database=None, derandomize=True))

    def test_mutation_controls(self):
        controls = ('pause-ignored', 'scope-ignored', 'distribution-ignored', 'remove-keeps-record',
                    'budget-unrounded', 'pull-out-of-scope', 'refused-add-applies', 'stream-ihave',
                    'feed-wrong-groups')
        for plant in controls:
            with self.subTest(plant=plant):
                exercise = Exercise(self, FakeTarget(plant=plant))
                with patch('fn2.tests.surface.peering.test_model_peering.record_failure') as record, \
                        patch('fn2.tests.surface.peering.test_model_peering.SETTLE', 0.05), \
                        patch('fn2.tests.surface.peering.test_model_peering.time.sleep'):
                    with self.assertRaises(AssertionError):
                        exercise.witnesses()
                    self.assertTrue(record.called)

    def test_reason_forms(self):
        self.assertEqual(peer_reason('refused operator peer administrative configuration refused: NO-SUCH-PEER\n'),
                         'no-such-peer')
        self.assertEqual(peer_reason('refused operator peer REFUSED needs-send\n'), 'needs-send')
        self.assertEqual(peer_reason('Password: Confirm password: refused operator peer peer login refused: '
                                     'passwords-differ\n'), 'passwords-differ')
        self.assertEqual(peer_reason('usage operator peer (ADMINISTRATION PULL-LOGIN)\n'), 'pull-login')
        self.assertIsNone(peer_reason('accepted operator peer ACCEPTED\n'))

    def test_distribution_rule(self):
        art = lambda h: b'From: a\r\n' + h + b'Subject: s\r\n\r\nbody\r\n'
        self.assertTrue(distribution_fed(None, art(b'Distribution: world\r\n')))
        self.assertTrue(distribution_fed('fn', art(b'')))
        self.assertTrue(distribution_fed('fn', art(b'Distribution: FN\r\n')))
        self.assertFalse(distribution_fed('fn', art(b'Distribution: world\r\n')))
        self.assertTrue(distribution_fed('*,!local', art(b'Distribution: world, local\r\n')))
        self.assertFalse(distribution_fed('fn', art(b'Distribution: bad name\r\n')))

    def test_refusal_leaves_the_table(self):
        model = PeeringModel()
        before = dict(model.peers)
        expected = model.rule('peer set', 'absent', '--streaming', 'false')
        expected.update(dict(exit=1, text='refused operator peer administrative configuration refused: NO-SUCH-PEER\n'))
        self.assertEqual(model.peers, before)
        with self.assertRaises(AssertionError):
            model.rule('peer remove', 'absent').update(dict(exit=0, text='accepted operator peer ACCEPTED\n'))

    def test_pause_window_is_checked(self):
        model = PeeringModel()
        add = ('fa', 'fa.example', '127.0.0.1', '40001', '-', 'hz.test', 'principal', 'ab' * 32, 'true')
        model.rule('peer add', *add).update(dict(exit=0, text='accepted operator peer ACCEPTED\n'))
        model.rule('peer feed', 'fa', 'pause').update(dict(exit=0, text='accepted operator peer ACCEPTED\n'))
        model.local_accept('<p@surface.invalid>', b'Newsgroups: hz.test\r\n\r\nb\r\n', ['hz.test'])
        self.assertIn('paused', model.check_feed(40001, {'<p@surface.invalid>': 5.0}))
        model.rule('peer feed', 'fa', 'resume').update(dict(exit=0, text='accepted operator peer ACCEPTED\n'))
        model.resumed('fa', 10.0)
        self.assertIn('paused', model.check_feed(40001, {'<p@surface.invalid>': 5.0}))
        self.assertIsNone(model.check_feed(40001, {'<p@surface.invalid>': 11.0}))
        self.assertIn('never offered', model.check_feed(40001, {}))

    def test_effect_row_follows_fn1_only(self):
        from .peering_model import ADJUDICATIONS
        self.assertEqual([r['group'] for r in ADJUDICATIONS], ['P01'])
        for target, due in (('fn1', {'<t@surface.invalid>'}), ('fn2', set()), ('fake', set())):
            with self.subTest(target=target):
                model = PeeringModel()
                add = ('fa', 'fa.example', '127.0.0.1', '40001', '-', 'hz.test', 'principal', 'ab' * 32, 'true')
                model.rule('peer add', *add).update(dict(exit=0, text='accepted operator peer ACCEPTED\n'))
                data = b'Newsgroups: hz.peer,hz.test\r\n\r\nb\r\n'
                model.wire.add_article('<t@surface.invalid>', data, ['hz.peer'])
                row = model.transferred('<t@surface.invalid>', data, ['hz.peer'], target)
                self.assertEqual(model.due(40001), due)
                self.assertEqual(row is not None, target == 'fn1')
