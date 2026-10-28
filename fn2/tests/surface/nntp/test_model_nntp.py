"""Form S: live empty-group reader/cursor sequences against H2's NNTP model.

H2b's differential CLI supplies the wider generated command/transport hook;
accepted POST projection, cancellation and nonempty pinned views remain extensions.
"""
from fn2.tests.surface import RUN, SurfaceCase, Target, serving


def machine(case):
    from hypothesis import strategies as st
    from hypothesis.stateful import RuleBasedStateMachine, invariant, rule
    from fn2.tests.model.nntp_model import NntpModel

    class NntpMachine(RuleBasedStateMachine):
        def __init__(self):
            super().__init__()
            # Cleanup per Hypothesis example, including construction failure.
            import unittest
            from contextlib import ExitStack
            self.cleanup = ExitStack()
            self.resources = unittest.TestCase()
            self.resources.addCleanup = self.cleanup.callback
            self.client = None
            try:
                self.target = Target(self.resources)
                self.model = NntpModel({'surface.test': {}}, [], {}, {'posting': True})
                self.connect()
            except BaseException:
                self.cleanup.close()
                raise

        def check(self, expected, status, body=None):
            verdict = expected.check(status, body)
            case.assertTrue(verdict.ok, f'{verdict.rule}: {verdict.detail}; {status!r}')
            expected.update(status, body)

        def connect(self):
            self.conn = self.model.connect(tls=False, implicit_tls=False)
            self.client = self.target.connect()
            self.check(self.conn.greeting(), self.client.greeting)

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
            self.check(expected, status, body)

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

    @serving('nntp')
    def test_live_state_machine(self):
        from hypothesis import settings
        from hypothesis.stateful import run_state_machine_as_test
        run_state_machine_as_test(machine(self), settings=settings(
            max_examples=RUN.get('examples', 200), stateful_step_count=50,
            deadline=None, database=None, derandomize=True))
