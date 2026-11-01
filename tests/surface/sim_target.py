"""The surface Target over layer D's simulator session (agreed with main 2026-10-30; D provides the hook).

`FN2_SURFACE_SIM_NNTP=module:callable` is called with (case=, family=, out=) and returns a session:

    open(peer=False) -> (id, greeting octets)       the listener admits a row and the greeting drains
    send(id, octets, chunks=None) -> (octets, closed)
                                                    the client octets as Receive results cut at CHUNKS, then
                                                    the scheduler to quiescence for that connection
    close(id) -> octets                             EOF, then quiescence
    stop() -> {id: WIRE verdict}                    the simulated node ends; sim/check-wire.lisp's verdicts

SimTarget gives the S forms what Target gives them over a socket (`connect()` -> a client with `greeting`,
`command(line)`, `line()`, `close(quit)`), so the machines, the model and the evidence capture are unchanged.
`stop()`'s WIRE verdicts are asserted at the case's cleanup: a connection the WIRE checker refuses fails the
example even when the model agreed with every reply, and so does a connection WIRE never judged. Every `open`
is one connection incarnation and needs its own id and its own verdict: a session that reuses a slot's id for
the next connection on that slot judges only the last one.

NativeTarget is the same Target over layer A's socket session (`FN2_SURFACE_NATIVE_NNTP=module:callable`, the
same constructor and API): the served core under the native event loop on loopback TCP, `send` writing the
octets to the real port in CHUNKS and returning what the node wrote until the loop is quiescent for that
connection, `stop` returning WIRE's verdict per connection over the octets that crossed the socket.
"""
import importlib
import os


CARRIERS = {'SIM': 'simulator session owed: set FN2_SURFACE_SIM_{F}=module:callable (layer D)',
            'NATIVE': 'socket session owed: set FN2_SURFACE_NATIVE_{F}=module:callable (layer A, A5r 3/3)'}


def session_from_hook(case, family, out, carrier='SIM'):
    spec = os.environ.get(f'FN2_SURFACE_{carrier}_' + family.upper())
    if not spec:
        import unittest
        raise unittest.SkipTest(CARRIERS[carrier].format(F=family.upper()))
    module, name = spec.rsplit(':', 1)
    return getattr(importlib.import_module(module), name)(case=case, family=family, out=out)


class SimClient:
    """A Client over one simulated connection: replies are whatever the session returned, line by line."""

    def __init__(self, session, peer=False):
        self.session = session
        self.id, greeting = session.open(peer=peer)
        self.buffer = bytearray(greeting)
        self.closed = False
        self.greeting = self.line()

    def line(self):
        at = self.buffer.find(b'\r\n')
        if at < 0:
            if self.closed:
                raise EOFError('the simulated node closed the connection')
            raise TimeoutError('no complete line from the simulated node at quiescence')
        line = bytes(self.buffer[:at + 2])
        del self.buffer[:at + 2]
        return line

    def send(self, octets, chunks=None):
        reply, closed = self.session.send(self.id, octets, chunks)
        self.buffer += reply
        self.closed = self.closed or closed

    def command(self, text):
        self.send((text.encode('utf-8') if isinstance(text, str) else text) + b'\r\n')
        return self.line()

    def close(self, quit=True):
        if self.closed:
            return
        if quit:
            self.send(b'QUIT\r\n')
        self.buffer += self.session.close(self.id)
        self.closed = True


class SimTarget:
    """Target over the simulator: one session per test, its WIRE verdicts checked at cleanup."""
    carrier = 'SIM'

    def __init__(self, case, family='nntp', out='build/surface'):
        self.session = session_from_hook(case, family, out, self.carrier)
        self.opened = []

        def verdicts():
            answered = self.session.stop() or {}
            refused = {cid: v for cid, v in answered.items() if v != 'ok'}
            unjudged = len(self.opened) - len(set(self.opened) & set(answered))
            if isinstance(getattr(case, 'evidence', None), dict):
                case.evidence['wire'] = dict(carrier=self.carrier, opened=len(self.opened),
                                             distinct_ids=len(set(self.opened)), judged=len(answered),
                                             ok=len(answered) - len(refused), refused=refused, unjudged=unjudged)
            if refused:
                raise AssertionError(f'WIRE refused {self.carrier.lower()} connections: {refused}')
            if unjudged:
                raise AssertionError(f'WIRE judged {len(answered)} of {len(self.opened)} {self.carrier.lower()} '
                                     f'connections ({len(set(self.opened))} distinct ids): every open needs its '
                                     'own id and verdict')
        case.addCleanup(verdicts)

    def connect(self, peer=False):
        client = SimClient(self.session, peer)
        self.opened.append(client.id)
        return client


class NativeTarget(SimTarget):
    """Target over the native event loop on a loopback socket (milestone M1b): the session API unchanged."""
    carrier = 'NATIVE'
