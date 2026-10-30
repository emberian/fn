"""Form S: live empty-group reader/cursor sequences against H2's NNTP model.

H2b's differential CLI supplies the wider generated command/transport hook;
accepted POST projection, cancellation and nonempty pinned views remain extensions.
"""
from fn2.tests.surface import SurfaceCase, Target, serving
from fn2.tests.surface.live_evidence import capture_step, record_failure, run_live_machine


def machine(case):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, invariant, rule
    from fn2.tests.model.nntp_model import NntpModel

    class NntpMachine(RuleBasedStateMachine):
        @capture_step(case, 'nntp')
        def __init__(self):
            super().__init__()
            # Cleanup per Hypothesis example, including construction failure.
            import unittest
            from contextlib import ExitStack
            self.cleanup = ExitStack()
            self.resources = unittest.TestCase()
            self.resources.addCleanup = self.cleanup.callback
            self.client = None
            self.trace = []
            try:
                self.target = Target(self.resources)
                self.model = NntpModel({'surface.test': {}}, [], {}, {'posting': True})
                self.connect()
            except BaseException:
                self.cleanup.close()
                raise

        def check(self, expected, status, body=None, *, command=None):
            verdict = expected.check(status, body)
            self.trace.append(dict(rule=verdict.rule, request=command,
                                   reply=dict(status=status, body=body), model_verdict=verdict))
            if not verdict.ok:
                record_failure(case, 'nntp', rule=verdict.rule, request=command,
                               reply=dict(status=status, body=body), verdict=verdict, trace=self.trace)
            case.assertTrue(verdict.ok, f'{verdict.rule}: {verdict.detail}; {status!r}')
            expected.update(status, body)

        @capture_step(case, 'nntp')
        def connect(self):
            self.conn = self.model.connect(tls=False, implicit_tls=False)
            self.client = self.target.connect()
            self.check(self.conn.greeting(), self.client.greeting)

        @capture_step(case, 'nntp', request=lambda self, command: command + b'\r\n')
        def command(self, command):
            expected = self.conn.send(command + b'\r\n')
            status = self.client.command(command)
            body = None
            if expected.multiline_for(status):
                # Client.block unstuffs bytes; use line() to retain the actual wire.
                rows = []
                while True:
                    line = self.client.line()
                    rows.append(line)
                    if line == b'.\r\n':
                        break
                body = b''.join(rows)
            self.check(expected, status, body, command=command + b'\r\n')

        @rule(group=st.sampled_from(['surface.test', 'absent']))
        def select(self, group):
            self.command(('GROUP ' + group).encode())

        @rule(command=st.sampled_from([
            b'LISTGROUP', b'LISTGROUP surface.test', b'NEXT', b'LAST',
            b'ARTICLE', b'HEAD', b'BODY', b'STAT', b'ARTICLE 1', b'STAT <absent@test>',
            b'OVER 1-', b'XOVER 1-', b'HDR subject 1-', b'XHDR subject 1-',
            b'LIST ACTIVE surface.*', b'LIST DISTRIBUTIONS', b'LIST DISTRIB.PATS',
            b'MODE READER', b'NOSUCHCOMMAND']))
        def reader(self, command):
            self.command(command)

        @rule()
        def reconnect(self):
            self.command(b'QUIT')
            self.client.close(quit=False)
            self.connect()

        @invariant()
        @capture_step(case, 'nntp')
        def empty_cursor(self):
            case.assertIsNone(self.conn.current_article_number)
            case.assertEqual(self.model.watermarks['surface.test'], 0)

        def teardown(self):
            try:
                if self.client is not None:
                    self.client.close(quit=False)
            finally:
                self.cleanup.close()

    return NntpMachine


class TestSurface(SurfaceCase):
    family, form = 'nntp', 'S'

    def test_live_state_machine(self):
        import os
        from fn2.tests.surface import MANIFEST
        target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
        if target == 'fn2' and 'nntp' in MANIFEST.get('serves_sim', {}).get('fn2', []):
            return self.sim_state_machine()
        return serving('nntp')(lambda self: run_live_machine(self, 'nntp', machine(self)))(self)

    def sim_state_machine(self):
        """fn2 under the simulator (M1a): served verbs judged by the model, interim replies named OWED."""
        import os
        from hypothesis import Phase, settings
        from hypothesis.stateful import run_state_machine_as_test
        from fn2.tests.surface import output
        from fn2.tests.surface.nntp import sim_nntp
        from fn2.tests.surface.sim_target import SimTarget
        from fn2.tests.surface.live_evidence import failure_context
        target = SimTarget(self, 'nntp', out=str(output('nntp')))
        owed, served = {}, {}
        self.evidence['owed_interim'], self.evidence['served_checked'] = owed, served
        examples = int(os.environ.get('FN2_SIM_EXAMPLES', '100'))
        with failure_context(self, 'nntp'):
            run_state_machine_as_test(sim_nntp.machine(self, target, owed, served), settings=settings(
                max_examples=examples, stateful_step_count=int(os.environ.get('FN2_SIM_STEPS', '30')),
                deadline=None, database=None, derandomize=True, phases=(Phase.explicit, Phase.generate),
                report_multiple_bugs=False))
        self.evidence['sim_examples'] = examples
