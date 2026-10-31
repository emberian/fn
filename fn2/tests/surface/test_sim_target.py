"""SimTarget/SimClient over a fake simulator session (the model's own fake renderer behind a session API)."""
import os
import sys
from pathlib import Path
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

    def test_native_target_is_the_same_target_over_its_own_hook(self):
        with mock.patch.dict(os.environ, {'FN2_SURFACE_NATIVE_NNTP': __name__ + ':hook'}):
            os.environ.pop('FN2_SURFACE_SIM_NNTP', None)
            client = sim_target.NativeTarget(self).connect()
            self.assertTrue(client.command(b'GROUP fn.test').startswith(b'211'))
        with mock.patch.dict(os.environ, {'FN2_SURFACE_NATIVE_NNTP': __name__ + ':refusing_hook'}):
            case = unittest.TestCase()
            sim_target.NativeTarget(case).connect()
            function, args, kwargs = case._cleanups.pop()
            with self.assertRaisesRegex(AssertionError, 'WIRE refused native connections'):
                function(*args, **kwargs)
        with mock.patch.dict(os.environ, {'FN2_SURFACE_SIM_NNTP': __name__ + ':hook'}):
            os.environ.pop('FN2_SURFACE_NATIVE_NNTP', None)
            with self.assertRaisesRegex(unittest.SkipTest, 'socket session owed'):
                sim_target.NativeTarget(self)

    def test_a_reused_id_leaves_a_connection_unjudged(self):
        # A session keying its records by slot judges only each slot's last incarnation: two opens, one verdict.
        class SlotSession(FakeSession):
            def open(self, peer=False):
                cid, greeting = super().open(peer)
                self.conns = {0: self.conns[cid]}
                return 0, greeting
        with mock.patch.object(sys.modules[__name__], 'hook', lambda case, family, out: SlotSession()), \
                mock.patch.dict(os.environ, {'FN2_SURFACE_SIM_NNTP': __name__ + ':hook'}):
            case = unittest.TestCase()
            case.evidence = {}
            target = sim_target.SimTarget(case)
            target.connect(); target.connect()
            function, args, kwargs = case._cleanups.pop()
            with self.assertRaisesRegex(AssertionError, 'WIRE judged 1 of 2 sim connections'):
                function(*args, **kwargs)
            self.assertEqual(case.evidence['wire']['unjudged'], 1)

    def test_targets_pick_their_carrier_and_backend(self):
        # fn2 runs nntp S under the simulator, fn2-native on the socket; both are fn2's Node backend; fn2-native
        # serves nntp's other forms through the backend, and every other family stays a named skip.
        from fn2.tests import surface
        from fn2.tests.surface.nntp.test_model_nntp import TestSurface
        self.assertEqual({t: surface.backend(t) for t in surface.TARGETS},
                         {'fn1': 'fn1', 'fn2': 'fn2', 'fn2-native': 'fn2'})
        self.assertEqual(surface.MANIFEST['serves']['fn2-native'], ['nntp'])
        carriers = []
        with mock.patch.object(TestSurface, 'sim_state_machine', lambda self, carrier: carriers.append(carrier)):
            for target in ('fn2', 'fn2-native'):
                with mock.patch.dict(os.environ, {'FN2_SURFACE_TARGET': target}):
                    TestSurface('test_live_state_machine').test_live_state_machine()
        self.assertEqual(carriers, ['SIM', 'NATIVE'])
        with mock.patch.dict(os.environ, {'FN2_SURFACE_TARGET': 'fn2-native'}):
            gated = surface.serving('consumer')(lambda: self.fail('ran an unserved family'))
            with self.assertRaisesRegex(unittest.SkipTest, 'not yet serving'):
                gated()
        with mock.patch.dict(os.environ, {'FN2_SURFACE_TARGET': 'fn3'}):
            with self.assertRaises(ValueError):
                surface.backend()

    def test_named_host_contracts_are_owed_against_fn2_and_other_outcomes_still_fail(self):
        from fn2.tests import surface
        def child(tests):
            return lambda name, args: dict(status='ok', tests=tests, module=name)
        owed = dict(test='m.T.a', outcome='fail', classification='named-node-dead', skip_reason='',
                    exception='node dead: fn2 layer D not yet serving: init needs operator CONFIG init')
        ok = dict(test='m.T.b', outcome='ok', classification=None, skip_reason='', exception='')
        red = dict(test='m.T.c', outcome='fail', classification='other', skip_reason='', exception='wrong reply')
        for target, tests, verdict in [('fn2-native', [owed, ok], 'skip'), ('fn2-native', [owed, red], 'fail'),
                                       ('fn1', [owed, ok], 'fail')]:
            case = surface.SurfaceCase('setUp')
            case.setUp()
            with self.subTest(target=target, verdict=verdict), \
                    mock.patch.dict(os.environ, {'FN2_SURFACE_TARGET': target}), \
                    mock.patch.object(surface, 'RUN', {'native_envs': {'m': {}}, 'out': 'build/surface-unit'}), \
                    mock.patch.object(surface.run_natives, 'child', child(tests)):
                if verdict == 'skip':
                    with self.assertRaisesRegex(unittest.SkipTest, r'host contract owed \(1 tests; 1 ran ok\): init needs'):
                        case.native('nntp', 'm')
                    self.assertEqual(len(case.evidence['owed_host']), 1)
                else:
                    with self.assertRaises(AssertionError):
                        case.native('nntp', 'm')

    def test_a_fixture_setup_the_served_node_lacks_is_owed_against_fn2(self):
        from fn2.tests import surface
        from tests.native_harness import NodeDead
        def refuse(**kwargs):
            raise NodeDead(surface.run_natives.PREFIX + ': init needs operator CONFIG init GROUP...')
        for target, owed in (('fn2-native', True), ('fn1', False)):
            case = surface.SurfaceCase('setUp')
            case.setUp()
            with self.subTest(target=target), mock.patch.dict(os.environ, {'FN2_SURFACE_TARGET': target}), \
                    mock.patch.object(surface, 'hook', lambda *a, **k: refuse()):
                with self.assertRaisesRegex(unittest.SkipTest if owed else NodeDead, 'init needs'):
                    case.fixture('nntp', dict(path='x', reason='y'))

    def test_sim_machine_lines_against_the_interim_table(self):
        # The interim lines cover the reader and posting verbs; one whose verb has left the table is judged by
        # the model as served (sim_nntp.SimNntp.interim), so the lines need not be a subset of the table.
        import re
        from fn2.tests.surface.nntp import sim_nntp
        text = Path(sim_nntp.__file__).read_text()
        interim = re.search(r"interim_lines = st.sampled_from\(\[(.*?)\]\)", text, re.S).group(1)
        verbs = set(re.findall(r"b'([A-Z-]+)", interim))
        self.assertGreaterEqual(len(verbs), 18)
        self.assertEqual(sim_nntp.D3_POLICY['posting'], False)


if __name__ == '__main__':
    unittest.main()
