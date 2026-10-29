"""HZ live store S: fixed witnesses, then 20 generated interleaved operations.

Only loopback is used. CLI timeouts are 3 s, archive/init/start 10 s; client
reads 3 s and <=64 KiB. Each example owns one Node and its port lease. Import
changes that stopped node's store path; external secrets stay fixture inputs.
See store_ops_model for scope, provisional decisions and nominal work budget.
"""
from contextlib import ExitStack
from copy import deepcopy
import os
import hashlib
import re
import shutil
import unittest

from fn2.tests.model.store_ops_model import GROUP, LOGIN, PASSWORD, StoreOpsModel, article
from fn2.tests.model.limits_model import STORE_INIT
from fn2.tests.surface import SurfaceCase, owned_ports, serving
from fn2.tests.surface.live_evidence import capture_step, json_value, record_failure, run_live_machine


class StoreTarget:
    @owned_ports
    def __init__(self, case):
        from tests.native_harness import Node, native_image
        self.case = case
        self.adjudication_target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
        self.node = Node(case, native_image('FN_NATIVE_HOST'))
        flags = [word for key, value in STORE_INIT.items() for word in ('--' + key, str(value))]
        self.node.operator('init', '--profile', 'development', *flags, GROUP, timeout=10, expect=0)
        self.node.operator('principal', 'set-password', LOGIN, '--posting',
                           input=(PASSWORD + '\n' + PASSWORD + '\n').encode(), timeout=3, expect=0)
        self.stores = {'source': self.node.store_path}
        self.paths = {'nonempty': self.node.root / 'nonempty'}
        self.paths['nonempty'].mkdir()
        (self.paths['nonempty'] / 'marker').write_text('HZ nonempty archive fixture\n')
        self.node.start(timeout=10)
        self.running = True

    def path(self, name):
        return self.paths.setdefault(name, self.node.root / name)

    def store(self, name):
        return self.stores.setdefault(name, self.node.root / ('store-' + name))

    def archive_fingerprint(self, name):
        # Observe only export archives / the nonempty refusal fixture: they
        # contain no authentication or node-secret files.
        path = self.path(name)
        if not path.exists():
            return None
        return {str(p.relative_to(path)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in path.rglob('*') if p.is_file()}

    def call(self, r):
        before = self.archive_fingerprint(r.argument) if r.verb == 'export' else None
        words = {'inspect-group': ('inspect', '--group', r.argument),
                 'export-status': ('export', '--status')}.get(r.verb, (r.verb,))
        if r.verb in ('export', 'import', 'bless-snapshot'):
            words += (str(self.path(r.argument)),)
        elif r.verb == 'inspect':
            words += (r.argument,)
        words += tuple(word for key, value in r.override for word in ('--' + key, str(value)))
        if r.malformed:
            words += ('hz-extra-argument',)
        bound = 10 if r.verb in ('export', 'import') else 3
        if r.verb == 'import':
            result = self.node.invoke('store', str(self.store(r.destination)), *words, timeout=bound)
            if result.returncode == 0:
                # Export excludes these files. Copy only this example's fixtures.
                source, destination = self.node.store_path, self.store(r.destination)
                shutil.copytree(source / 'keys', destination / 'keys')
                shutil.copy2(source / 'auth.toml', destination / 'auth.toml')
        elif r.direct:
            result = self.node.invoke('store', str(self.node.store_path), *words, timeout=bound)
        else:
            prefix = () if r.verb in ('status', 'recover') else ('store',)
            result = self.node.operator(*prefix, *words, timeout=bound)
        reply = {'exit': result.returncode, 'text': (result.stdout + result.stderr).decode('ascii')}
        if r.verb == 'export':
            reply.update(archive_before=before, archive_after=self.archive_fingerprint(r.argument))
        if r.verb == 'import':
            reply['destination_exists'] = self.store(r.destination).exists()
        return reply

    def prepare(self, name, kind, source=None):
        """Explicit fixture construction, no state inferred from server replies."""
        path = self.path(name)
        if kind == 'tampered':
            shutil.copytree(self.path(source), path)
            manifest = bytearray((path / 'MANIFEST').read_bytes())
            manifest[0] = ord('0') if manifest[0] != ord('0') else ord('1')
            (path / 'MANIFEST').write_bytes(manifest)
        elif kind in ('snapshot', 'unmarked'):
            if self.running:
                raise ValueError('snapshot fixture requires stopped owner')
            shutil.copytree(self.node.store_path, path)
            if kind == 'snapshot':
                (path / 'SNAPSHOT').write_bytes(b'fn snapshot 1\nactive-segment=0 frontier=0 files=0\n')
        else:
            raise ValueError(kind)

    def stop(self):
        if self.running:
            self.node.stop(grace=3)
            self.running = False

    def start(self, name=None):
        if name is not None:
            if self.running:
                raise ValueError('switch requires stopped owner')
            self.node.store_path = self.store(name)
            self.node.write_config()
        if not self.running:
            self.node.start(timeout=10)
            self.running = True

    def open(self):
        return Wire(self.node.session(timeout=3, greeting=None))


class Wire:
    def __init__(self, client):
        self.client, self.greeting = client, client.greeting

    def command(self, command):
        return self.client.command(command)

    def send(self, data):
        self.client.send(data)

    def line(self):
        return self.client.line(limit=512)

    def block(self):
        rows, total = [], 0
        for _ in range(512):
            line = self.client.line(limit=512)
            rows.append(line)
            total += len(line)
            if total > 65536:
                raise AssertionError('HZ response exceeds 64 KiB fixture work bound')
            if line == b'.\r\n':
                return b''.join(rows)
        raise AssertionError('HZ response exceeds 512 line fixture work bound')

    def close(self):
        self.client.close(quit=False)


class Exercise:
    def __init__(self, case, target, trace=None):
        self.case, self.target = case, target
        self.trace = trace if trace is not None else []
        self.model = StoreOpsModel()
        self.serial, self.moves = 0, 0

    def assert_ok(self, ok, rule, request, reply, detail):
        if not ok:
            record_failure(self.case, 'store_ops', rule=rule, request=request,
                           reply=reply, verdict=dict(ok=False, detail=detail), trace=self.trace)
        self.case.assertTrue(ok, (rule, request, reply, detail))

    def check_wire(self, expected, status, body=None, request=None):
        verdict = expected.check(status, body)
        self.trace.append(dict(wire=request, status=status, body=body, verdict=verdict))
        self.assert_ok(verdict.ok, verdict.rule, request, dict(status=status, body=body), verdict.detail)
        expected.update(status, body)

    def session(self):
        conn = self.model.wire.connect(tls=False, implicit_tls=False)
        wire = self.target.open()
        try:
            self.check_wire(conn.greeting(), wire.greeting, request='greeting')
        except BaseException:
            wire.close()
            raise
        return conn, wire

    @staticmethod
    def close_session(session):
        # Environment transition: this fixture itself closes its TCP endpoint.
        # Retire its model connection too; a local close is not a server QUIT
        # reply and does not supply any unobserved wire output.
        conn, wire = session
        wire.close()
        conn.quit = True

    def command(self, session, command):
        conn, wire = session
        expected = conn.send(command.encode() + b'\r\n')
        status = wire.command(command.encode())
        # Frame from observed status, so a wrong success does not leave a block
        # unread or become an invented response. Every read remains bounded.
        body = wire.block() if status[:3] in (b'211', b'222') and (
            command.startswith('LISTGROUP') or command.startswith('BODY')) else None
        self.check_wire(expected, status, body, request=command)
        return status

    @capture_step(None, 'store_ops')
    def observe(self):
        if not self.model.running:
            self.cli('inspect-group', GROUP, observe=False)
            return
        session = self.session()
        try:
            self.command(session, 'GROUP ' + GROUP)
            self.command(session, 'LISTGROUP ' + GROUP)
            for number, ident in self.model.wire.groups[GROUP]:
                self.command(session, 'STAT ' + str(number))
                self.command(session, 'BODY ' + ident)
            self.command(session, 'STAT <hz-never@surface.invalid>')
        finally:
            self.close_session(session)

    @capture_step(None, 'store_ops', request=lambda self, verb, argument='', **kwargs:
                  dict(verb=verb, argument=argument, **kwargs))
    def cli(self, verb, argument='', *, observe=True, **kwargs):
        expected = self.model.rule(verb, argument, **kwargs)
        reply = self.target.call(expected.request)
        self.trace.append(dict(request=expected.request, reply=reply))
        target = getattr(self.target, 'adjudication_target', 'fake')
        recorded = expected.recorded_difference(reply, target)
        if recorded is None:
            verdict = expected.check(reply)
            self.assert_ok(verdict is None, verb, expected.request, reply, verdict)
        expected.update(reply, target)
        if recorded and hasattr(self.case, 'evidence'):
            self.case.evidence.setdefault('recorded_differences', []).append(json_value(recorded))
        if observe:
            self.observe()
        return reply

    @capture_step(None, 'store_ops')
    def post(self):
        if not self.model.running:
            self.start()
        self.serial += 1
        ident, data = article(self.serial)
        # Only BODY/STAT are observed; generated signing headers aren't guessed.
        self.model.wire.policy['stored_articles'][ident] = data
        session = self.session()
        try:
            self.command(session, 'AUTHINFO USER ' + LOGIN)
            self.command(session, 'AUTHINFO PASS ' + PASSWORD)
            self.command(session, 'POST')
            expected = session[0].send_block(data + b'.\r\n')
            session[1].send(data + b'.\r\n')
            reply = session[1].line()
            self.check_wire(expected, reply, request='POST body ' + ident)
            self.assert_ok(reply.startswith(b'240 '), 'durable-post', ident, reply,
                           'fixture must reach acknowledged acceptance')
        finally:
            self.close_session(session)
        self.observe()

    @capture_step(None, 'store_ops')
    def stop(self):
        self.target.stop()
        self.model.running = False

    @capture_step(None, 'store_ops')
    def start(self, name=None):
        self.target.start(name)
        if name is not None:
            self.model.current = name
        self.model.running = True
        self.observe()

    @capture_step(None, 'store_ops')
    def prepare(self, name, kind, source=None):
        self.target.prepare(name, kind, source)
        origin = self.model.archives[source]['wire'] if source else self.model.wire
        self.model.archives[name] = dict(kind=kind, wire=deepcopy(origin), valid=False,
                                         marker=kind == 'snapshot', secret=True)

    def roundtrip(self):
        self.moves += 1
        archive, destination = 'archive-' + str(self.moves), 'import-' + str(self.moves)
        self.cli('export', archive)
        self.stop()
        self.cli('import', archive, destination=destination,
                 override=(('max-transactions', 8192),))
        self.start(destination)
        self.cli('status')

    def witnesses(self):
        self.post(); self.post()
        self.cli('inspect', article(1)[0])
        self.cli('inspect', '<hz-never@surface.invalid>')
        self.cli('inspect-group', GROUP)
        self.cli('inspect-group', 'hz.unknown')
        for verb in ('status', 'recover', 'compact', 'checkpoint'):
            self.cli(verb)
            self.cli(verb, malformed=True)
        self.cli('export', 'good')
        self.cli('export-status')
        self.cli('export', 'nonempty')
        self.cli('export', 'good')
        self.stop()
        self.cli('export-status')
        for verb in ('status', 'recover', 'checkpoint'):
            self.cli(verb, direct=True)
        self.cli('compact')
        self.cli('export', 'offline', direct=True)
        self.prepare('tampered', 'tampered', 'good')
        self.prepare('unmarked', 'unmarked')
        self.prepare('snapshot', 'snapshot')
        self.cli('bless-snapshot', 'unmarked', direct=True)
        self.cli('bless-snapshot', 'snapshot', direct=True)
        self.cli('import', 'tampered', destination='tampered-destination')
        self.cli('import', 'unmarked', destination='snapshot-destination')
        self.cli('import', 'good', destination='source')
        self.cli('import', 'good', destination='invalid-profile', override=(('max-history-octets', 1000),))
        self.cli('import', 'good', destination='imported', override=(('max-transactions', 8192),))
        self.start('imported')
        self.cli('status')
        self.cli('import', 'good', destination='imported')
        self.observe()


def machine(case, target_factory=StoreTarget, traces=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, precondition, rule

    class StoreMachine(RuleBasedStateMachine):
        @capture_step(case, 'store_ops')
        def __init__(self):
            super().__init__()
            self.cleanup, self.trace = ExitStack(), []
            resources = unittest.TestCase()
            resources.addCleanup = self.cleanup.callback
            try:
                self.exercise = Exercise(case, target_factory(resources), self.trace)
                self.exercise.witnesses()
            except BaseException:
                if traces is not None:
                    traces.append(self.trace)
                self.cleanup.close()
                raise

        @precondition(lambda self: self.exercise.serial < 8)
        @rule()
        @capture_step(case, 'store_ops')
        def post(self):
            self.exercise.post()

        @rule(verb=st.sampled_from(('compact', 'checkpoint', 'recover', 'status')),
              malformed=st.booleans())
        @capture_step(case, 'store_ops')
        def maintenance(self, verb, malformed):
            self.exercise.cli(verb, malformed=malformed)

        @rule()
        @capture_step(case, 'store_ops')
        def lifecycle(self):
            e = self.exercise
            if e.model.running:
                e.stop()
                e.cli('recover')
            else:
                e.start()

        @rule(unknown=st.booleans())
        @capture_step(case, 'store_ops')
        def inspect(self, unknown):
            self.exercise.cli('inspect-group', 'hz.unknown' if unknown else GROUP)

        @rule()
        @capture_step(case, 'store_ops')
        def export_status(self):
            self.exercise.cli('export-status')

        @rule()
        @capture_step(case, 'store_ops')
        def refused_export(self):
            self.exercise.cli('export', 'nonempty')

        @precondition(lambda self: self.exercise.moves < 1)
        @rule()
        @capture_step(case, 'store_ops')
        def roundtrip(self):
            self.exercise.roundtrip()

        def teardown(self):
            try:
                if traces is not None:
                    traces.append(self.trace)
            finally:
                self.cleanup.close()

    return StoreMachine


class TestSurface(SurfaceCase):
    family, form = 'store_ops', 'S'

    @serving('store_ops')
    def test_live_state_machine(self):
        self.evidence['recorded_differences'] = []
        traces = self.evidence['traces'] = []
        run_live_machine(self, 'store_ops', machine(self, traces=traces))
