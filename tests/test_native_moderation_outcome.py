"""S083: observe a persisted authorization after its cause is refused.

Uses the existing pre-publication refusal cut, real control commands, and a
developer query of the ordinary ACL2 plan. No publication/submission adapters.
"""
import unittest
from tools import fn_dev
from tests.native_harness import (
    Client, Node, article, executable, keep_diagnostics, native_image,
)

IMAGE = native_image('FN_NATIVE_DEVELOPER_HOST')


@unittest.skipUnless(executable(IMAGE), 'native developer executable required')
class NativeModerationOutcome(unittest.TestCase):
    def test_refused_cause_keeps_authorization_across_restart(self):
        nodes = []
        keep_diagnostics(self, nodes)
        node = Node(self, IMAGE)
        nodes.append(node)
        sock = node.root / 'developer.sock'
        developer = {'FN_NATIVE_DEV_REPL': str(sock)}
        target = '<partial-withdrawal@example.invalid>'
        created = node.operator('init', '--budget', '2048', 'fn.test', 'control.cancel')
        self.assertEqual(created.returncode, 0, created.stderr.decode())

        def plan_has_existing_authorization():
            # The actual planner omits its configuration argv exactly when
            # the cause/target authorization already exists in carried state.
            form = """(progn (fnn-owner-advance-clock)
              (let ((plan (fnn-owner-core 'fn-owner-moderation-plan
                 :withdraw nil (fn-record-string-octets %s)
                 (fn-record-string-octets "test"))))
                (list (car plan) (null (cadr plan)))))""" % fn_dev.lisp_string(target)
            ok, text = fn_dev.evaluate(sock, form, 10)
            self.assertTrue(ok, text)
            self.assertIn(text.strip(), ('(:WITHDRAW NIL)', '(:WITHDRAW T)'))
            return text.strip() == '(:WITHDRAW T)'

        def stat():
            client = Client(node.port)
            try:
                return client.command('STAT ' + target)
            finally:
                client.close()

        node.start(env=developer)
        posted = node.post(target, article(target))
        self.assertEqual(posted.returncode, 0, posted.stderr.decode())
        self.assertFalse(plan_has_existing_authorization())
        node.stop()

        node.start(env={**developer, 'FN_NATIVE_POST_FAULT': 'record-prepublish:refuse'})
        refused = node.operator('article', 'withdraw', target, '--reason', 'test')
        observed = (refused.stdout + refused.stderr).decode()
        self.assertEqual(refused.returncode, 3, observed)
        self.assertIn('withdrawal-authorized-cause-refused', observed)
        self.assertIsNone(node.process.poll())
        self.assertTrue(plan_has_existing_authorization())
        self.assertTrue(stat().startswith(b'223'))
        node.stop()

        node.start(env=developer)
        self.assertTrue(plan_has_existing_authorization())
        self.assertTrue(stat().startswith(b'223'))
        completed = node.operator('article', 'withdraw', target, '--reason', 'test')
        self.assertEqual(completed.returncode, 0, completed.stderr.decode())
        self.assertTrue(stat().startswith(b'430'))
        node.stop()


if __name__ == '__main__':
    unittest.main()
