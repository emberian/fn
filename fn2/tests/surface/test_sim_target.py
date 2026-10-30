"""SimTarget/SimClient over a fake simulator session (the model's own fake renderer behind a session API)."""
import os
import unittest
from unittest import mock

from fn2.tests.model import differential as d
from fn2.tests.surface import sim_target


class FakeSession:
    """The agreed session API over differential.Fake (H2's model rendering replies)."""

    def __init__(self, verdict='ok'):
        self.conns, self.verdict = {}, verdict

    def _drain(self, fake):
        out = b''
        while True:
            try:
                chunk = fake.recv(65536)
            except OSError:
                return out, False
            if not chunk:
                return out, fake.conn.quit
            out += chunk

    def open(self, peer=False):
        fake = d.Fake('peer' if peer else 'reader', 'plain')
        cid = len(self.conns)
        self.conns[cid] = fake
        return cid, self._drain(fake)[0]

    def send(self, cid, octets, chunks=None):
        fake, at = self.conns[cid], 0
        for size in (chunks or [len(octets)]):
            fake.sendall(octets[at:at + size])
            at += size
        if at < len(octets):
            fake.sendall(octets[at:])
        return self._drain(fake)

    def close(self, cid):
        return b''

    def stop(self):
        return {cid: self.verdict for cid in self.conns}


def hook(case, family, out):
    return FakeSession()


def refusing_hook(case, family, out):
    return FakeSession('reply after close')


class SimTargetUnit(unittest.TestCase):
    def test_client_over_the_session(self):
        with mock.patch.dict(os.environ, {'FN2_SURFACE_SIM_NNTP': __name__ + ':hook'}):
            target = sim_target.SimTarget(self)
            client = target.connect()
            self.assertTrue(client.greeting.startswith((b'200', b'201')))
            self.assertTrue(client.command(b'GROUP fn.test').startswith(b'211'))
            self.assertTrue(client.command(b'HELP').startswith(b'100'))
            body = []
            while True:
                line = client.line()
                body.append(line)
                if line == b'.\r\n':
                    break
            self.assertGreater(len(body), 1)
            self.assertTrue(client.command(b'NOSUCH').startswith(b'500'))
            self.assertEqual(client.command(b'QUIT')[:3], b'205')

    def test_wire_refusal_fails_the_case_and_missing_hook_is_a_named_skip(self):
        with mock.patch.dict(os.environ, {'FN2_SURFACE_SIM_NNTP': __name__ + ':refusing_hook'}):
            case = unittest.TestCase()
            sim_target.SimTarget(case).connect()
            function, args, kwargs = case._cleanups.pop()      # the verdict check SimTarget registered
            with self.assertRaisesRegex(AssertionError, 'WIRE refused'):
                function(*args, **kwargs)
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop('FN2_SURFACE_SIM_NNTP', None)
            with self.assertRaisesRegex(unittest.SkipTest, 'simulator session owed'):
                sim_target.SimTarget(self)


if __name__ == '__main__':
    unittest.main()
