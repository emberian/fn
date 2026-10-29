"""Peering S: fixed per-verb witnesses, then generated peer-table transitions (peering_model).

One fresh node per example (STORE_INIT, three groups), loopback only, three scripted peers: `fa` answers
MODE STREAM 203, `fb` answers it 500 (a server without RFC 4644), `src` lists its own two articles to a
NEWNEWS pull. Every CLI has a 5 s timeout (init/start 10 s), every wire read 3 s, every block <=512
lines/64 KiB; a fed or pulled article must arrive within peering_model.SETTLE seconds. The profile keeps
the transit and pull scopes (hz.peer) disjoint from every feed's groups (hz.test, hz.other), so a feed
carries local posts only; the model raises if a step would leave that profile. Test-work bounds, not
product ceilings; the enclosing surface child supplies the hard wall bound.
"""
from contextlib import ExitStack, contextmanager
import os
import socket
import threading
import time
import unittest

from fn2.tests.model import framing
from fn2.tests.model.limits_model import STORE_INIT
from fn2.tests.model.nntp_model import wildmat
from fn2.tests.model.peering_model import GROUPS, PRINCIPAL, SETTLE, PeeringModel
from fn2.tests.surface import SurfaceCase, owned_ports, serving
from fn2.tests.surface.live_evidence import capture_step, json_value, record_failure, run_live_machine


def article(ident, groups, extra=''):
    return (f'From: peer@surface.invalid\r\nNewsgroups: {groups}\r\nSubject: peering S\r\n'
            f'Date: Thu, 29 Oct 2026 12:00:00 +0000\r\nPath: far.example!not-for-mail\r\n{extra}'
            f'Message-ID: {ident}\r\n\r\nbody {ident}\r\n').encode()


SOURCE_OWN = {'<pull-1@surface.invalid>': article('<pull-1@surface.invalid>', 'hz.peer'),
              '<pull-2@surface.invalid>': article('<pull-2@surface.invalid>', 'hz.test'),
              '<pull-3@surface.invalid>': article('<pull-3@surface.invalid>', 'hz.peer,hz.test')}


class ScriptedPeer:
    """A scripted NNTP peer on loopback: the observation instrument of the feed and the pull's other end.
    It records, per connection, its start time and commands, and per Message-ID the first time an article
    body arrived. It is not an oracle: it answers every offer as wanted."""

    def __init__(self, mode_stream=True, own=None):
        self.mode_stream, self.own = mode_stream, dict(own or {})
        self.lock, self.connections, self.received = threading.Lock(), [], {}
        self.sock = socket.socket()
        self.sock.bind(('127.0.0.1', 0))
        self.sock.listen(16)
        self.port = self.sock.getsockname()[1]
        self.alive = True
        threading.Thread(target=self.serve, daemon=True).start()

    def serve(self):
        while self.alive:
            try:
                conn, _ = self.sock.accept()
            except OSError:
                return
            threading.Thread(target=self.session, args=(conn,), daemon=True).start()

    def session(self, conn):
        conn.settimeout(30)
        stream = conn.makefile('rb')
        record = dict(start=time.monotonic(), commands=[])
        with self.lock:
            self.connections.append(record)

        def say(text):
            conn.sendall(text.encode() + b'\r\n')

        def body(ident):
            for _ in range(4096):
                row = stream.readline(65536)
                if not row or row == b'.\r\n':
                    break
            with self.lock:
                self.received.setdefault(ident, time.monotonic())

        try:
            say('200 scripted peer')
            while True:
                row = stream.readline(4096)
                if not row:
                    return
                line = row.decode('ascii', 'replace').rstrip('\r\n')
                with self.lock:
                    record['commands'].append(line)
                verb, _, rest = line.partition(' ')
                verb = verb.upper()
                if verb == 'MODE' and rest.upper() == 'STREAM':
                    say('203 streaming permitted' if self.mode_stream else '500 unknown command')
                elif verb == 'IHAVE':
                    say('335 send it')
                    body(rest)
                    say('235 transferred')
                elif verb == 'CHECK':
                    say('238 ' + rest)
                elif verb == 'TAKETHIS':
                    body(rest)
                    say('239 ' + rest)
                elif verb == 'AUTHINFO':
                    say('381 more' if rest.upper().startswith('USER') else '281 ok')
                elif verb == 'DATE':
                    say('111 20261029120000')
                elif verb == 'NEWNEWS':
                    say('230 list follows')
                    for ident in self.own:
                        say(ident)
                    say('.')
                elif verb == 'ARTICLE' and rest in self.own:
                    say('220 0 ' + rest)
                    conn.sendall(framing.encode_block(self.own[rest]))
                elif verb == 'ARTICLE':
                    say('430 no such article')
                elif verb == 'QUIT':
                    say('205 bye')
                    return
                else:
                    say('500 unknown command')
        except OSError:
            return
        finally:
            conn.close()

    def snapshot(self):
        with self.lock:
            return dict(self.received), [dict(c, commands=list(c['commands'])) for c in self.connections]

    def close(self):
        self.alive = False
        self.sock.close()


class Wire:
    def __init__(self, client):
        self.client, self.greeting = client, client.greeting

    def command(self, command):
        self.client.send(command + b'\r\n')
        return self.client.line(limit=512)

    def send(self, data):
        self.client.send(data)
        return self.client.line(limit=512)

    def block(self):
        rows, total, deadline = [], 0, time.monotonic() + 3
        for _ in range(512):
            self.client.sock.settimeout(max(.001, deadline - time.monotonic()))
            row = self.client.line(limit=8192)
            rows.append(row)
            total += len(row)
            if total > 65536 or time.monotonic() > deadline:
                raise AssertionError('peering fixture block budget exceeded')
            if row == b'.\r\n':
                self.client.sock.settimeout(3)
                return b''.join(rows)
        raise AssertionError('peering fixture line budget exceeded')

    def close(self):
        self.client.close(quit=False)


class PeeringTarget:
    @owned_ports
    def __init__(self, case):
        from tests.native_harness import Node, native_image
        self.adjudication_target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
        self.node = Node(case, native_image('FN_NATIVE_HOST'))
        flags = [item for key, value in STORE_INIT.items() for item in ('--' + key, str(value))]
        result = self.node.operator('init', '--profile', 'development', *flags, *GROUPS, timeout=10)
        reply = dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('ascii', 'replace'))
        if result.returncode:
            record_failure(case, 'peering', rule='init', request=flags, reply=reply,
                           verdict=dict(ok=False, detail='fixture init'), trace=[])
        case.assertEqual(result.returncode, 0, reply)
        self.instruments = dict(fa=ScriptedPeer(True), fb=ScriptedPeer(False), src=ScriptedPeer(True, SOURCE_OWN))
        for instrument in self.instruments.values():
            case.addCleanup(instrument.close)
        self.node.start(timeout=10)

    def call(self, request):
        data = None
        if request.password is not None:
            data = ('\n'.join(request.password) + '\n').encode()
        result = self.node.operator(*request.words, input=data, timeout=5)
        return dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('ascii', 'replace'))

    def post(self, ident, data, group):
        path = self.node.root / ('post-%d.eml' % len(list(self.node.root.glob('post-*.eml'))))
        path.write_bytes(data)
        result = self.node.operator('post', '--message-id', ident, '--payload', path, '--group', group, timeout=5)
        return dict(exit=result.returncode, text=(result.stdout + result.stderr).decode('ascii', 'replace'))

    def scratch(self, name):
        return str(self.node.root / name)

    def open(self):
        from tests.native_harness import Client
        return Wire(Client(self.node.port, timeout=3, greeting=None))


class Exercise:
    def __init__(self, case, target, trace=None):
        self.case, self.target = case, target
        self.model = PeeringModel()
        self.trace = trace if trace is not None else []
        self.serial = 0
        self.checked_verbs = set()
        self.instruments = target.instruments
        self.streams = {}

    def require(self, good, *, rule, request, reply, detail):
        if not good:
            record_failure(self.case, 'peering', rule=rule, request=request, reply=reply,
                           verdict=dict(ok=False, detail=detail), trace=self.trace)
        self.case.assertTrue(good, (detail, request, reply))

    def check_wire(self, expected, status, body=None, *, request=None):
        verdict = expected.check(status, body)
        self.trace.append(dict(wire=request, status=status, body=body, verdict=verdict))
        if not verdict.ok:
            record_failure(self.case, 'peering', rule=verdict.rule, request=request,
                           reply=dict(status=status, body=body), verdict=verdict, trace=self.trace)
        self.case.assertTrue(verdict.ok, (verdict, status, body))
        expected.update(status, body)

    def port(self, slot):
        return str(self.instruments[slot].port) if slot in self.instruments else {'loop': '9', 'x': '7'}[slot]

    # -- CLI steps ------------------------------------------------------------------------------
    @capture_step(None, 'peering', request=lambda self, verb, *args, **kwargs: dict(verb=verb, args=args))
    def step(self, verb, *args, password=None):
        expected = self.model.rule(verb, *args, password=password)
        asked = time.monotonic()
        result = self.target.call(expected.request)
        self.trace.append(dict(request=expected.request, reply=result))
        target = getattr(self.target, 'adjudication_target', 'fake')
        recorded = expected.recorded_difference(result, target)
        problem = expected.check(result)
        if recorded is None:
            self.require(problem is None, rule=verb, request=expected.request, reply=result, detail=problem)
        expected.update(result, target)
        self.checked_verbs.add((verb, bool(expected.reason)))
        if recorded is not None and hasattr(self.case, 'evidence'):
            self.case.evidence.setdefault('recorded_differences', []).append(json_value(dict(recorded, step=len(self.trace))))
        if not expected.reason:
            name = args[0] if args else None
            if verb == 'peer feed' and args[1] == 'resume':
                self.model.resumed(name, asked)
            if verb in ('peer add', 'peer set') and name in self.instruments:
                # The offer form is fixed per connection at connect (specs/nntp.md:2452): only
                # connections the peer accepted after this edit returned are checked for it.
                self.streams[name] = time.monotonic()
        return result

    def add(self, slot, inbound='-', outbound='hz.test', kind='principal', value=PRINCIPAL, streaming='true'):
        return self.step('peer add', slot, slot + '.example', '127.0.0.1', self.port(slot), inbound, outbound,
                         kind, value, streaming)

    @capture_step(None, 'peering')
    def post(self, group, extra=''):
        self.serial += 1
        ident = f'<peer-{self.serial}@surface.invalid>'
        data = article(ident, group, extra)
        reply = self.target.post(ident, data, group)
        self.trace.append(dict(post=ident, group=group, reply=reply))
        self.require(reply['exit'] == 0, rule='post', request=ident, reply=reply,
                     detail='the funded fixture accepts a local post')
        self.model.local_accept(ident, data, [group])
        return ident

    # -- the wire ------------------------------------------------------------------------------
    @contextmanager
    def session(self):
        conn = self.model.wire.connect(tls=False, implicit_tls=False)
        wire = self.target.open()
        try:
            self.check_wire(conn.greeting(), wire.greeting)
            yield conn, wire
            self.command((conn, wire), 'QUIT')
        finally:
            conn.quit = True
            wire.close()

    def command(self, session, command):
        conn, wire = session
        raw = command.encode('ascii')
        expected = conn.send(raw + b'\r\n')
        status = wire.command(raw)
        body = wire.block() if expected.multiline_for(status) else None
        self.check_wire(expected, status, body, request=command)
        return status

    def transit(self, session, verb, ident, groups):
        """IHAVE (offer then body) or TAKETHIS (command and body, one reply) of one article."""
        conn, wire = session
        data = article(ident, groups)
        block = framing.encode_block(data)
        before = set(self.model.wire.articles)
        if verb == 'IHAVE':
            if self.command(session, 'IHAVE ' + ident)[:3] != b'335':
                return
            expected = conn.send_block(block)
            status = wire.send(block)
        else:
            raw = f'TAKETHIS {ident}\r\n'.encode()
            self.check_wire(conn.send(raw), b'', None, request='TAKETHIS ' + ident)
            expected = conn.send_block(block)
            status = wire.send(raw + block)
        self.check_wire(expected, status, None, request=data)
        for new in set(self.model.wire.articles) - before:
            local = [g for g, rows in self.model.wire.groups.items() if any(m == new for _, m in rows)]
            self.transferred(new, data, local)

    def transferred(self, ident, data, local):
        if any(p['outbound'] != '-' and any(wildmat(p['outbound'], g) for g in local)
               for p in self.model.peers.values()):
            raise ValueError('outside the profile: a transferred article in a feed group')
        recorded = self.model.transferred(ident, data, local, getattr(self.target, 'adjudication_target', 'fake'))
        if recorded is not None and hasattr(self.case, 'evidence'):
            self.case.evidence.setdefault('recorded_differences', []).append(
                json_value(dict(recorded, article=ident, local=local, step=len(self.trace))))

    @capture_step(None, 'peering')
    def observe(self):
        self.step('peer list')
        with self.session() as session:
            for name in GROUPS:
                self.command(session, 'GROUP ' + name)
            for ident in sorted(set(self.model.wire.articles) | set(SOURCE_OWN)):
                self.command(session, 'STAT ' + ident)
            for ident in sorted(self.model.wire.articles)[-4:]:
                self.command(session, 'BODY ' + ident)

    # -- the feed and the pull -----------------------------------------------------------------
    @capture_step(None, 'peering')
    def settle(self):
        """Wait for every due article at every scripted feed peer, then check each peer's record."""
        deadline = time.monotonic() + SETTLE
        for slot in ('fa', 'fb'):
            instrument = self.instruments[slot]
            due = self.model.due(instrument.port)
            while time.monotonic() < deadline and not due <= set(instrument.snapshot()[0]):
                time.sleep(.1)
            received, connections = instrument.snapshot()
            problem = self.model.check_feed(instrument.port, received)
            self.trace.append(dict(feed=slot, received=sorted(received), due=sorted(due), verdict=problem))
            self.require(problem is None, rule='feed', request=slot, reply=sorted(received), detail=problem)
            self.check_offer_form(slot, connections)

    def check_offer_form(self, slot, connections):
        record = self.model.peers.get(slot)
        since = self.streams.get(slot)
        if record is None or since is None:
            return
        streams = record['streaming'] and self.instruments[slot].mode_stream
        for conn in connections:
            if conn['start'] <= since:
                continue
            verbs = [c.split(' ', 1)[0].upper() for c in conn['commands']]
            offers = [v for v in verbs if v in ('IHAVE', 'CHECK', 'TAKETHIS')]
            if record['streaming']:
                good = verbs[:1] == ['MODE'] or verbs[:1] == ['AUTHINFO']
            else:
                good = 'MODE' not in verbs
            good = good and all(v in (('CHECK', 'TAKETHIS') if streams else ('IHAVE',)) for v in offers)
            self.require(good, rule='offer-form', request=slot, reply=conn['commands'],
                         detail='streaming record: MODE STREAM first, then CHECK/TAKETHIS on 203 or IHAVE on 500; '
                                'non-streaming record: IHAVE only')

    @capture_step(None, 'peering')
    def pull(self, slot='src'):
        """`peer pull SLOT 1`, wait for every article the round must bring in, stop the pull."""
        entering, never = self.model.pull_round(slot, SOURCE_OWN)
        self.step('peer pull', slot, '1')
        deadline = time.monotonic() + SETTLE
        pending = set(entering)
        while pending and time.monotonic() < deadline:
            wire = self.target.open()
            try:
                for ident in sorted(pending):
                    if wire.command(b'STAT ' + ident.encode())[:3] == b'223':
                        pending.discard(ident)
            finally:
                wire.close()
            time.sleep(.2)
        self.step('peer pull', slot, '0')
        for ident, (data, scope) in sorted(entering.items()):
            self.model.wire.add_article(ident, data, scope)
            self.transferred(ident, data, scope)
        self.trace.append(dict(pull=slot, entering=sorted(entering), never=sorted(never), late=sorted(pending)))
        # The wire oracle decides: entering articles are now held (STAT 223, BODY), the rest 430.
        self.observe()

    # -- the fixed witnesses -------------------------------------------------------------------
    def witness(self, verb, *args, password=None):
        self.step(verb, *args, password=password)

    @capture_step(None, 'peering')
    def witnesses(self):
        s = self.step
        s('peer list')
        s('peer list', 'extra')
        s('peer add', 'bad', 'bad.example', 'bad_host', '119', 'hz.peer', '-', 'principal', PRINCIPAL, 'false')
        s('peer remove', 'loop')
        # Transit: a loopback source-address record with an inbound half makes this connection its peer.
        with self.session() as session:
            self.command(session, 'IHAVE <in-0@surface.invalid>')
        self.add('loop', inbound='hz.peer', outbound='-', kind='source-address', value='127.0.0.1')
        with self.session() as session:
            self.transit(session, 'IHAVE', '<in-1@surface.invalid>', 'hz.peer')
            self.transit(session, 'IHAVE', '<in-1@surface.invalid>', 'hz.peer')
            self.transit(session, 'IHAVE', '<in-2@surface.invalid>', 'hz.test')
            self.transit(session, 'IHAVE', '<in-3@surface.invalid>', 'hz.peer,hz.test')
            self.command(session, 'MODE STREAM')
            self.command(session, 'CHECK <in-1@surface.invalid>')
            self.command(session, 'CHECK <in-4@surface.invalid>')
            self.transit(session, 'TAKETHIS', '<in-4@surface.invalid>', 'hz.peer')
            self.transit(session, 'TAKETHIS', '<in-5@surface.invalid>', 'hz.other')
        self.observe()
        s('peer set', 'loop', '--streaming', 'false')                     # needs-send
        s('peer set', 'absent', '--streaming', 'false')
        s('peer set', 'loop', '--nonsense', 'x')
        s('peer set', 'loop', '--port', '0')
        s('peer set', 'loop', '--port', '10')
        # The outbound feed: fa streams (203), fb does not (500: IHAVE on the same connection).
        self.add('fa', outbound='hz.test')
        self.add('fb', outbound='hz.test,hz.other')
        self.post('hz.test')
        self.post('hz.other')
        self.post('hz.peer')
        self.settle()
        s('peer feed', 'fa', 'pause')
        s('peer feed', 'fa', 'pause')
        s('peer feed', 'absent', 'pause')
        s('peer feed', 'fa', 'sideways')
        self.post('hz.test')
        self.settle()
        s('peer feed', 'fa', 'resume')
        self.settle()
        s('peer distributions', 'fa', 'fn')
        s('peer distributions', 'fa', 'fn,[')
        s('peer distributions', 'absent', 'fn')
        self.post('hz.test', 'Distribution: world\r\n')
        self.post('hz.test', 'Distribution: FN\r\n')
        self.settle()
        s('peer budget', 'fa', '1048577', '16')
        s('peer budget', 'fa', 'x', '16')
        s('peer budget', 'absent', '4096', '1')
        s('peer set', 'fb', '--streaming', 'false')
        s('peer set', 'fa', '--send', 'hz.test,hz.other')
        self.post('hz.other')
        self.settle()
        # The pull: src lists three of its own articles; only those with a hz.peer name enter.
        self.add('src', inbound='hz.peer', outbound='-', streaming='false')
        self.pull()
        s('peer pull', 'src', '30', '3')
        s('peer pull', 'src', '0')
        s('peer pull', 'src', 'x')
        s('peer pull', 'absent', '30')
        s('peer pull-login', 'src', '-', 'false')
        s('peer pull-login', 'src', '-', 'maybe')
        s('peer pull-login', 'absent', '-', 'false')
        s('peer catch-up', 'src', '60')
        s('peer catch-up', 'src', '0')
        s('peer catch-up', 'src', 'x')
        s('peer catch-up', 'absent', '60')
        # A login only for a record that sends (x: nothing listens on its port).
        self.add('x', outbound='hz.other', streaming='false')
        s('peer login', 'x', 'me-node', self.target.scratch('x.fnauth'), password=('pw-one', 'pw-one'))
        s('peer login', 'x', 'me-node', self.target.scratch('x2.fnauth'), password=('pw-one', 'pw-two'))
        s('peer login', 'loop', 'me-node', self.target.scratch('l.fnauth'), password=('pw', 'pw'))
        s('peer login', 'absent', 'me-node', self.target.scratch('a.fnauth'), password=('pw', 'pw'))
        s('peer remove', 'fb')
        s('peer remove', 'fb')
        self.post('hz.other')
        self.settle()
        s('peer remove', 'loop')
        with self.session() as session:
            self.command(session, 'IHAVE <in-9@surface.invalid>')
        self.observe()
        self.require(self.checked_verbs == {(v, r) for v in PeeringModel.VERBS for r in (False, True)},
                     rule='witness-coverage', request=None, reply=sorted(self.checked_verbs),
                     detail='each scoped verb needs a success and a refusal witness')


GENERATED = (
    ('peer feed', 'fa', 'pause'), ('peer feed', 'fa', 'resume'), ('peer feed', 'fb', 'pause'),
    ('peer feed', 'fb', 'resume'), ('peer distributions', 'fa', 'fn'), ('peer distributions', 'fa', '*,!local'),
    ('peer distributions', 'fb', 'world'), ('peer set', 'fa', '--send', 'hz.test'),
    ('peer set', 'fa', '--send', 'hz.test,hz.other'), ('peer set', 'fb', '--send', 'hz.other'),
    ('peer set', 'fa', '--streaming', 'false'), ('peer set', 'fa', '--streaming', 'true'),
    ('peer set', 'fb', '--streaming', 'true'), ('peer budget', 'fa', '8192', '4'), ('peer budget', 'fb', '1', '1'),
    ('peer budget', 'fa', 'x', '1'), ('peer pull', 'x', '0'), ('peer catch-up', 'x', '0'),
    ('peer set', 'x', '--port', '0'), ('peer set', 'x', '--port', '8'), ('peer set', 'x', '--take', 'hz.peer'),
    ('peer set', 'x', '--send', '-'), ('peer set', 'x', '--streaming', 'true'), ('peer remove', 'x'),
    ('peer remove', 'fa'), ('peer remove', 'fb'), ('peer remove', 'loop'), ('peer list',),
    ('peer feed', 'absent', 'resume'), ('peer pull-login', 'x', '-', 'true'),
)
ADDS = ('fa', 'fb', 'x', 'loop')


def machine(case, target_factory=PeeringTarget, traces=None):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, precondition, rule

    class PeeringMachine(RuleBasedStateMachine):
        @capture_step(case, 'peering')
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

        @rule(words=st.sampled_from(GENERATED), malformed=st.booleans())
        @capture_step(case, 'peering', request=lambda self, words, malformed: dict(words=words, malformed=malformed))
        def transition(self, words, malformed):
            self.exercise.step(words[0], *words[1:], *(('',) if malformed else ()))
            self.exercise.settle()

        @rule(slot=st.sampled_from(ADDS), streaming=st.booleans())
        @capture_step(case, 'peering', request=lambda self, slot, streaming: dict(slot=slot, streaming=streaming))
        def add(self, slot, streaming):
            if slot == 'loop':
                self.exercise.add('loop', inbound='hz.peer', outbound='-', kind='source-address', value='127.0.0.1')
            else:
                self.exercise.add(slot, outbound={'fa': 'hz.test', 'fb': 'hz.test,hz.other', 'x': 'hz.other'}[slot],
                                  streaming='true' if streaming else 'false')
            self.exercise.settle()

        @precondition(lambda self: self.exercise.serial < 16)
        @rule(group=st.sampled_from(GROUPS), distribution=st.sampled_from(('', 'Distribution: fn\r\n',
                                                                          'Distribution: world\r\n')))
        @capture_step(case, 'peering', request=lambda self, group, distribution: dict(group=group, d=distribution))
        def local_post(self, group, distribution):
            self.exercise.post(group, distribution)
            self.exercise.settle()

        @precondition(lambda self: self.exercise.model.transit_peer() is not None)
        @rule(verb=st.sampled_from(('IHAVE', 'TAKETHIS')), groups=st.sampled_from(('hz.peer', 'hz.test',
                                                                                   'hz.peer,hz.other')))
        @capture_step(case, 'peering', request=lambda self, verb, groups: dict(verb=verb, groups=groups))
        def transit(self, verb, groups):
            self.exercise.serial += 1
            with self.exercise.session() as session:
                if verb == 'TAKETHIS':
                    self.exercise.command(session, 'MODE STREAM')
                self.exercise.transit(session, verb, f'<in-g{self.exercise.serial}@surface.invalid>', groups)

        @rule()
        @capture_step(case, 'peering')
        def look(self):
            self.exercise.observe()

        def teardown(self):
            if traces is not None:
                traces.append(self.trace)
            self.cleanup.close()

    return PeeringMachine


class TestSurface(SurfaceCase):
    family, form = 'peering', 'S'

    @serving('peering')
    def test_live_state_machine(self):
        self.evidence['recorded_differences'] = []
        traces = self.evidence['traces'] = []
        run_live_machine(self, 'peering', machine(self, traces=traces))
