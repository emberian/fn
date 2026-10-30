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
example even when the model agreed with every reply.
"""
import importlib
import os


def session_from_hook(case, family, out):
    spec = os.environ.get('FN2_SURFACE_SIM_' + family.upper())
    if not spec:
        import unittest
        raise unittest.SkipTest(f'simulator session owed: set FN2_SURFACE_SIM_{family.upper()}=module:callable (layer D)')
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
    """Target over the simulator: one session per example, its WIRE verdicts checked at cleanup."""

    def __init__(self, case, family='nntp', out='build/surface'):
        self.session = session_from_hook(case, family, out)

        def verdicts():
            refused = {cid: v for cid, v in (self.session.stop() or {}).items() if v != 'ok'}
            if refused:
                raise AssertionError(f'WIRE refused simulated connections: {refused}')
        case.addCleanup(verdicts)

    def connect(self, peer=False):
        return SimClient(self.session, peer)
