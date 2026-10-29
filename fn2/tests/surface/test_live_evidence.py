"""Socket-free controls for first-observation evidence and divergent replay."""
from dataclasses import dataclass
import json
from pathlib import Path
import tempfile
import traceback
import unittest
from unittest.mock import patch

from fn2.tests.surface import SurfaceCase, live_model_settings
from fn2.tests.surface.live_evidence import capture_step, failure_context, record_failure, run_live_machine


class LiveEvidenceTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.out = Path(self.directory.name)
        self.patch = patch('fn2.tests.surface.output', return_value=self.out)
        self.patch.start()
        self.addCleanup(self.patch.stop)
        self.case = SurfaceCase()
        self.case.setUp()

    def record(self, **changes):
        values = dict(rule='reader', request=b'NEXT\r\n', reply=b'501 wrong\r\n',
                      verdict={'ok': False, 'detail': 'expected 412'}, trace=[{'rule': 'connect'}])
        values.update(changes)
        record_failure(self.case, 'nntp', **values)

    def test_first_failure_is_snapshot_and_cannot_be_overwritten(self):
        trace = [{'reply': b'200 ready\r\n'}]
        self.record(trace=trace)
        trace[0]['reply'] = b'changed'
        self.record(reply=b'502 replay\r\n')
        saved = json.loads((self.out / 's-failure.json').read_text())
        self.assertEqual(saved, self.case.evidence['s_failure'])
        self.assertEqual(saved['reply'], {'hex': b'501 wrong\r\n'.hex()})
        self.assertEqual(saved['trace'], [{'reply': {'hex': b'200 ready\r\n'.hex()}}])
        self.assertEqual(set(saved), {'schema_version', 'family', 'test', 'rule', 'request',
                                     'reply', 'model_verdict', 'trace'})

    def test_dataclass_request_preserves_bytes(self):
        @dataclass
        class Request:
            command: bytes
        self.record(request=Request(b'POST'))
        self.assertEqual(self.case.evidence['s_failure']['request'], {'command': {'hex': '504f5354'}})

    def test_plain_fake_case_does_not_write(self):
        record_failure(unittest.TestCase(), 'nntp', rule='x', request=None, reply=None,
                       verdict=None, trace=[])
        self.assertFalse((self.out / 's-failure.json').exists())

    def test_write_failure_keeps_memory_and_original_exception(self):
        with patch.object(Path, 'open', side_effect=OSError('descriptor limit')):
            self.record()
        original = AssertionError('model mismatch')
        with self.assertRaises(AssertionError) as raised:
            with failure_context(self.case, 'nntp'):
                raise original
        self.assertIs(raised.exception, original)
        self.assertIn('artifact write failed: descriptor limit', original.__notes__[0])
        self.assertEqual(self.case.evidence['s_failure']['rule'], 'reader')

    def test_directory_failure_keeps_memory_and_original_exception(self):
        with patch('fn2.tests.surface.output', side_effect=OSError('cannot create directory')):
            self.record()
        self.assertEqual(self.case.evidence['s_failure']['rule'], 'reader')
        with self.assertRaises(AssertionError) as raised:
            with failure_context(self.case, 'nntp'):
                raise AssertionError('original mismatch')
        self.assertIn('cannot create directory', raised.exception.__notes__[0])

    def test_operation_exception_records_request_before_reraising(self):
        outer = self
        class Machine:
            trace = [{'rule': 'greeting', 'reply': b'200 ready\r\n'}]
            @capture_step(outer.case, 'nntp', request=lambda self, command: command)
            def command(self, command):
                raise EOFError('peer closed before status')
        with self.assertRaises(EOFError):
            Machine().command(b'NEXT')
        saved = self.case.evidence['s_failure']
        self.assertEqual(saved['request'], {'hex': b'NEXT'.hex()})
        self.assertIsNone(saved['reply'])
        self.assertFalse(saved['model_verdict']['evaluated'])
        self.assertEqual(saved['trace'][-1]['rule'], 'command')

    def test_skip_does_not_create_failure_evidence(self):
        outer = self
        class Machine:
            @capture_step(outer.case, 'nntp')
            def connect(self):
                raise unittest.SkipTest('fixture unavailable')
        with self.assertRaises(unittest.SkipTest):
            Machine().connect()
        self.assertNotIn('s_failure', self.case.evidence)

    def test_sibling_failure_does_not_replace_family_artifact(self):
        self.record()
        first = (self.out / 's-failure.json').read_bytes()
        self.case.setUp()
        self.record(reply=b'502 sibling failure')
        self.assertEqual((self.out / 's-failure.json').read_bytes(), first)
        self.assertIn('earlier failure', self.case.evidence['s_failure_file_note'])
        self.assertEqual(self.case.evidence['s_failure']['reply']['hex'], b'502 sibling failure'.hex())

    def test_hypothesis_divergent_replay_retains_first_step_and_pointer(self):
        from hypothesis import settings, strategies as st
        from hypothesis.stateful import RuleBasedStateMachine, rule
        calls = []
        outer = self

        class Divergent(RuleBasedStateMachine):
            @rule(data=st.data())
            def changed_draw(self, data):
                calls.append(None)
                # This is external live state changing between the first failed
                # execution and Hypothesis's mandatory reporting replay.
                value = 0 if len(calls) == 1 else 1
                data.draw(st.integers(min_value=value, max_value=value))
                outer.record(rule='changed_draw', request=b'NEXT\r\n', reply=b'501 original\r\n',
                             trace=[{'request': b'NEXT\r\n', 'reply': b'501 original\r\n'}])
                raise AssertionError('first live model rejection')

        with self.assertRaises(Exception) as raised:
            run_live_machine(self.case, 'nntp', Divergent,
                             settings=settings(live_model_settings('nntp'), max_examples=1,
                                               stateful_step_count=1))
        rendered = ''.join(traceback.format_exception(raised.exception))
        self.assertGreaterEqual(len(calls), 2, rendered)
        self.assertIn('Inconsistent data generation', rendered)
        self.assertIn(str(self.out / 's-failure.json'), rendered)
        saved = json.loads((self.out / 's-failure.json').read_text())
        self.assertEqual(saved['rule'], 'changed_draw')
        self.assertEqual(saved['reply']['hex'], b'501 original\r\n'.hex())
        self.assertEqual(saved, self.case.evidence['s_failure'])

    def test_live_nntp_machine_writes_its_first_wrong_reply(self):
        """The applied hooks, end to end: the real machine with a fake target."""
        from hypothesis import settings
        from fn2.tests.surface.nntp import test_model_nntp as module

        first = []

        class Client:
            greeting = b'200 ready\r\n'
            def command(self, command):
                # Only QUIT may answer 205: every other command is a planted mismatch.
                reply = b'205 bye\r\n' if command == b'QUIT' else b'599 planted\r\n'
                first.append((command, reply))
                return reply
            def close(self, **kwargs):
                pass

        class FakeTarget:
            def __init__(self, case):
                pass
            def connect(self):
                return Client()

        with patch.object(module, 'Target', FakeTarget), self.assertRaises(AssertionError) as raised:
            run_live_machine(self.case, 'nntp', module.machine(self.case),
                             settings=settings(live_model_settings('nntp'), max_examples=50,
                                               stateful_step_count=5))
        saved = json.loads((self.out / 's-failure.json').read_text())
        command, reply = next(row for row in first if row[0] != b'QUIT')
        self.assertEqual(saved['request'], {'hex': (command + b'\r\n').hex()})
        self.assertEqual(saved['reply']['status'], {'hex': reply.hex()})
        self.assertFalse(saved['model_verdict']['ok'])
        self.assertEqual(saved['trace'][-1]['request'], saved['request'])
        self.assertIn(str(self.out / 's-failure.json'), ''.join(traceback.format_exception(raised.exception)))

    def test_live_settings_enable_explicit_but_not_shrink_or_reuse(self):
        from hypothesis import Phase
        selected = live_model_settings('nntp')
        self.assertEqual(selected.phases, (Phase.explicit, Phase.generate))
        self.assertIsNone(selected.database)


if __name__ == '__main__':
    unittest.main()
