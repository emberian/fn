"""HZ independent finite store target and mutation controls (no native process).

FakeTarget owns lists of stored tuples and its own wire protocol. It does not
call StoreOpsModel, NntpModel, Expect or article() to compute a reply. Tests run
exactly the live Exercise, including fixed witnesses before generated steps.
"""
from copy import deepcopy
import re
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from fn2.tests.model.store_ops_model import StoreOpsModel, Request, ADJUDICATIONS, named_reason
from fn2.tests.surface.store_ops.test_model_store_ops import Exercise, StoreTarget, machine


class FakeTarget:
    adjudication_target = 'fake'

    def __init__(self, case=None, plant=None):
        self.plant, self.running, self.current = plant, True, 'source'
        self.stores = {'source': []}
        self.overrides = {'source': {}}
        self.archives = {'nonempty': {'kind': 'nonempty'}}
        self.last_export = None
        self.calls = []

    @property
    def rows(self):
        return self.stores[self.current]

    def call(self, r):
        self.calls.append(r)
        before = deepcopy(self.archives.get(r.argument)) if r.verb == 'export' else None
        text, reason, code = '', None, 0
        if r.malformed:
            return dict(exit=5, text='usage: store ' + r.verb)
        if r.verb == 'export':
            if r.argument in self.archives and self.plant != 'export-nonempty':
                reason = 'archive-exists'
                if self.plant == 'refusal-mutation' and self.rows:
                    self.rows.pop()
            else:
                self.archives[r.argument] = {'kind': 'export', 'rows': deepcopy(self.rows)}
                self.last_export = r.argument
                text = f'exported records={len(self.rows)} archive={r.argument}'
        elif r.verb == 'export-status':
            if not self.running:
                reason = 'no-owner'
            else:
                text = 'exported archive=' + str(self.last_export)
        elif r.verb == 'import':
            saved = self.archives[r.argument]
            if r.destination in self.stores:
                reason = 'store-exists'
            elif saved['kind'] == 'tampered':
                reason = 'manifest-mismatch'
            elif saved['kind'] != 'export':
                reason = 'archive-incomplete'
            elif dict(r.override).get('max-history-octets') == 1000:
                reason = 'profile'
            else:
                self.stores[r.destination] = deepcopy(saved['rows'])
                self.overrides[r.destination] = dict(r.override)
                text = f"imported records={len(saved['rows'])} destination={r.destination}"
                if self.plant == 'import-drop' and self.stores[r.destination]:
                    self.stores[r.destination].pop()
        elif r.verb == 'bless-snapshot':
            saved = self.archives[r.argument]
            if saved['kind'] == 'unmarked':
                reason = 'snapshot-incomplete'
            else:
                text = f"blessed snapshot={r.argument} transactions={len(saved['rows'])}: complete"
        elif r.verb == 'inspect-group':
            if r.argument != 'surface.test':
                reason = 'unknown-group'
            else:
                n = len(self.rows) + (1 if self.plant == 'inspect-count' else 0)
                text = f'inspect group=surface.test members={n}\n' + '\n'.join(
                    f'{number} {ident}' for number, ident, _ in self.rows)
        elif r.verb == 'inspect':
            present = any(ident == r.argument for _, ident, _ in self.rows)
            text = ('accepted ' if present else 'absent ') + r.argument + ' observed'
            code = 0 if present else 1
        elif r.verb == 'status':
            if self.running or r.direct:
                text = f'transactions={len(self.rows)} retained=all'
            else:
                text = f'stopped checkpoint=none journal-octets=4096 transactions-at-most={len(self.rows) + 1}'
            for key, value in self.overrides[self.current].items():
                text += f'\nprofile {key}={value}'
        elif r.verb == 'recover':
            text = 'recover accepted owner=serving' if self.running else 'recovered transactions=' + str(len(self.rows))
            if self.plant == 'recover-last-post' and self.rows:
                self.rows.pop()
        elif r.verb in ('compact', 'checkpoint'):
            text = f'compacted steps=checkpoint,drop records={len(self.rows)}'
            if self.plant == 'compact-renumber' and r.verb == 'compact':
                self.stores[self.current] = [(n + 1, i, b) for n, i, b in self.rows]
        else:
            raise AssertionError('unsupported fake verb ' + r.verb)
        reply = dict(exit=1 if reason else code, text='refused reason=' + reason if reason else text)
        if r.verb == 'export':
            reply.update(archive_before=before, archive_after=deepcopy(self.archives.get(r.argument)))
        if r.verb == 'import':
            reply['destination_exists'] = r.destination in self.stores
        return reply

    def prepare(self, name, kind, source=None):
        rows = self.archives[source]['rows'] if source else self.rows
        self.archives[name] = {'kind': kind, 'rows': deepcopy(rows)}

    def stop(self):
        self.running = False

    def start(self, name=None):
        if name is not None:
            self.current = name
        self.running = True

    def open(self):
        if not self.running:
            raise AssertionError('fake owner stopped')
        return FakeWire(self)


class FakeWire:
    greeting = b'200 HZ fake\r\n'

    def __init__(self, target):
        self.target, self.user, self.logged = target, None, False
        self.pending = None
        self.out = None

    def command(self, command):
        words = command.decode().split()
        verb = words[0]
        rows = self.target.rows
        if verb == 'AUTHINFO':
            if words[1] == 'USER':
                self.user = words[2]
                return b'381 password required\r\n'
            self.logged = self.user == 'hz-store-poster' and words[2] == 'hz-store-fixture-password'  # FAKE-SECRET
            return b'281 authentication accepted\r\n' if self.logged else b'481 rejected\r\n'
        if verb == 'POST':
            self.pending = 'post'
            return b'340 send article\r\n'
        if verb in ('GROUP', 'LISTGROUP'):
            high, low = (rows[-1][0], rows[0][0]) if rows else (0, 1)
            if verb == 'LISTGROUP':
                self.out = b''.join(str(n).encode() + b'\r\n' for n, _, _ in rows) + b'.\r\n'
            return f'211 {len(rows)} {low} {high} surface.test\r\n'.encode()
        if verb in ('STAT', 'BODY'):
            by_id = words[1].startswith('<')
            row = next((row for row in rows if (row[1] == words[1] if by_id else row[0] == int(words[1]))), None)
            if row is None:
                return b'430 no article\r\n' if by_id else b'423 no article\r\n'
            number, ident, data = row
            if verb == 'BODY':
                body = data.split(b'\r\n\r\n', 1)[1]
                self.out = b''.join((b'.' if line.startswith(b'.') else b'') + line + b'\r\n'
                                    for line in body.split(b'\r\n')[:-1]) + b'.\r\n'
            return f'{222 if verb == "BODY" else 223} {number} {ident}\r\n'.encode()
        raise AssertionError('unsupported fake wire ' + repr(command))

    def send(self, data):
        if self.pending != 'post':
            raise AssertionError('body without POST')
        raw = data[:-3]
        ident = re.search(rb'(?m)^Message-ID: (\S+)\r$', raw)[1].decode()
        number = max([n for n, _, _ in self.target.rows] or [0]) + 1
        self.target.rows.append((number, ident, raw))
        self.pending = None
        self.out = b'240 accepted\r\n'

    def line(self):
        answer, self.out = self.out, None
        return answer

    def block(self):
        return self.line()

    def close(self):
        pass


class StoreOpsTests(unittest.TestCase):
    def exercise(self, plant=None):
        return Exercise(self, FakeTarget(plant=plant))

    def test_fixed_witnesses(self):
        exercise = self.exercise()
        exercise.witnesses()
        self.assertEqual(exercise.model.current, 'imported')
        self.assertEqual(len(exercise.model.wire.articles), 2)
        self.assertEqual(exercise.model.overrides, {'max-transactions': 8192})
        observed = {request.verb for request in exercise.target.calls}
        self.assertEqual(observed, {'inspect', 'inspect-group', 'recover', 'status',
                                  'checkpoint', 'compact', 'export', 'export-status', 'import', 'bless-snapshot'})

    def test_generated_interleavings(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        run_state_machine_as_test(machine(self, FakeTarget), settings=settings(
            max_examples=200, stateful_step_count=20, deadline=None, database=None, derandomize=True))

    def test_mutation_import_drops_article(self):
        with self.assertRaises(AssertionError):
            self.exercise('import-drop').witnesses()

    def test_mutation_compact_renumbers(self):
        with self.assertRaises(AssertionError):
            self.exercise('compact-renumber').witnesses()

    def test_mutation_export_accepts_nonempty(self):
        with self.assertRaises(AssertionError):
            self.exercise('export-nonempty').witnesses()

    def test_mutation_recover_loses_acknowledged_post(self):
        with self.assertRaises(AssertionError):
            self.exercise('recover-last-post').witnesses()

    def test_mutation_inspect_misreports_group_count(self):
        with self.assertRaises(AssertionError):
            self.exercise('inspect-count').witnesses()

    def test_mutation_refusal_changes_state(self):
        with self.assertRaises(AssertionError):
            self.exercise('refusal-mutation').witnesses()

    def test_refusal_model_unchanged_and_checked_update(self):
        model = StoreOpsModel()
        before = deepcopy(model.wire.groups)
        expectation = model.rule('inspect-group', 'unknown')
        self.assertIsNone(expectation.check(dict(exit=1, text='refused unknown-group group=unknown')))
        expectation.update(dict(exit=1, text='refused unknown-group group=unknown'))
        self.assertEqual(before, model.wire.groups)
        with self.assertRaises(AssertionError):
            model.rule('export', 'nonempty').update(dict(exit=0, text='exported records=0'))
        self.assertEqual(model.archives['nonempty'], {'kind': 'nonempty', 'valid': False})

    def test_empty_adjudications_and_exact_scoping(self):
        self.assertEqual(ADJUDICATIONS, ())
        row = dict(group='TEST-ONLY', verb='export', argument_class='existing-archive',
                   **{'class': 'fn1-bug'}, fn1_reply=dict(exit=5, reason='other-reason'))
        model = StoreOpsModel()
        expectation = model.rule('export', 'nonempty')
        reply = dict(exit=5, text='refused reason=other-reason')
        with patch('fn2.tests.model.store_ops_model.ADJUDICATIONS', (row,)):
            self.assertIsNotNone(expectation.recorded_difference(reply, 'fn1'))
            self.assertIsNone(expectation.recorded_difference(reply, 'fn2'))
            self.assertIsNone(expectation.recorded_difference(reply, 'fake'))
            for changed in (dict(exit=1, text=reply['text']), dict(exit=5, text='refused reason=other-reason-extra')):
                self.assertIsNone(expectation.recorded_difference(changed, 'fn1'))
            self.assertIsNone(expectation.recorded_difference(dict(exit=5, text='refused reason=other-reason reason=extra'), 'fn1'))
            self.assertIsNone(model.rule('export-status').recorded_difference(reply, 'fn1'))
            self.assertIsNone(model.rule('export', 'fresh').recorded_difference(reply, 'fn1'))
            row['class'] = 'spec-ambiguity'
            self.assertIsNotNone(expectation.recorded_difference(reply, 'fn2'))
            expectation.update(reply, 'fn2')
            self.assertEqual(model.archives['nonempty']['kind'], 'nonempty')
        self.assertEqual(named_reason(dict(text='refused reason=archive-exists-extra')), 'archive-exists-extra')

    def test_adapter_command_shapes_and_import_fixture_files(self):
        with TemporaryDirectory(prefix='hz-store-adapter-') as directory:
            root = Path(directory)
            source = root / 'store'
            (source / 'keys').mkdir(parents=True)
            (source / 'keys' / 'node-secret.key').write_bytes(b'fake-node-key')  # FAKE-SECRET
            (source / 'auth.toml').write_text('fake auth fixture')  # FAKE-SECRET
            calls = []
            def invoke(*words, **kwargs):
                calls.append((words, kwargs))
                if words[0] == 'store' and words[2] == 'import':
                    Path(words[1]).mkdir()
                return SimpleNamespace(returncode=0, stdout=b'accepted', stderr=b'')
            def operator(*words, **kwargs):
                calls.append((('operator', *words), kwargs))
                return SimpleNamespace(returncode=0, stdout=b'accepted', stderr=b'')
            target = object.__new__(StoreTarget)
            target.node = SimpleNamespace(root=root, store_path=source, invoke=invoke, operator=operator)
            target.stores, target.paths = {'source': source}, {}
            target.call(Request('recover'))
            self.assertEqual(calls[-1], (('operator', 'recover'), {'timeout': 3}))
            target.call(Request('inspect-group', 'surface.test'))
            self.assertEqual(calls[-1][0], ('operator', 'store', 'inspect', '--group', 'surface.test'))
            target.call(Request('export-status'))
            self.assertEqual(calls[-1][0], ('operator', 'store', 'export', '--status'))
            target.call(Request('checkpoint', direct=True))
            self.assertEqual(calls[-1][0], ('store', str(source), 'checkpoint'))
            reply = target.call(Request('import', 'archive', 'imported', (('max-transactions', 8192),)))
            imported = root / 'store-imported'
            self.assertEqual(calls[-1], (('store', str(imported), 'import', str(root / 'archive'),
                                         '--max-transactions', '8192'), {'timeout': 10}))
            self.assertTrue(reply['destination_exists'])
            self.assertEqual((imported / 'auth.toml').read_bytes(), (source / 'auth.toml').read_bytes())
            self.assertEqual((imported / 'keys' / 'node-secret.key').read_bytes(), b'fake-node-key')
            target.call(Request('compact', malformed=True))
            self.assertEqual(calls[-1][0], ('operator', 'store', 'compact', 'hz-extra-argument'))
            self.assertTrue(all(options['timeout'] in (3, 10) for _, options in calls))

    def test_raw_failure_recorded_before_assertion(self):
        e = self.exercise()
        e.post()
        e.target.plant = 'inspect-count'
        recorded = []
        def save(*args, **kwargs):
            recorded.append(kwargs)
        class Case(unittest.TestCase):
            def assertTrue(inner, ok, msg=None):
                if not ok:
                    self.assertTrue(recorded, 'assertion preceded raw evidence')
                super().assertTrue(ok, msg)
        e.case = Case()
        with patch('fn2.tests.surface.store_ops.test_model_store_ops.record_failure', side_effect=save):
            with self.assertRaises(AssertionError):
                e.cli('inspect-group', 'surface.test')
        self.assertEqual(recorded[0]['reply']['text'].splitlines()[0], 'inspect group=surface.test members=2')
        self.assertEqual(recorded[0]['request'].verb, 'inspect-group')
        self.assertEqual(recorded[0]['trace'][-1]['reply'], recorded[0]['reply'])

    def test_body_corruption_reaches_nntp_oracle(self):
        e = self.exercise()
        e.post()
        n, ident, raw = e.target.rows[0]
        e.target.rows[0] = (n, ident, raw.replace(b'HZ body', b'BROKEN body'))
        with self.assertRaises(AssertionError):
            e.observe()


if __name__ == '__main__':
    unittest.main()
