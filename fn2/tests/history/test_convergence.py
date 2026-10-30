"""V1-V4 of the convergence checker: each caught when injected, none on the clean history."""
import unittest

from fn2.tests.history import convergence


class Builder:
    def __init__(self):
        self.records, self.i = [], 0

    def op(self, f, outcome='ok', **value):
        process = f'p{self.i}'
        request = {k: v for k, v in value.items() if k not in ('code',)}
        self.records.append(dict(process=process, type='invoke', f=f, value=request, time=self.i, index=self.i))
        self.records.append(dict(process=process, type=outcome, f=f, value=value, time=self.i + 1, index=self.i + 1))
        self.i += 2
        return self


def clean():
    b = Builder()
    b.op('post', node='a', message_id='<m@x>', digest='d1', code=240)
    b.op('transfer', node='b', message_id='<m@x>', digest='d1', code=235)
    b.op('transfer', 'fail', node='b', message_id='<m@x>', digest='d1', code=435)   # second offer refused
    b.op('read', node='a', message_id='<m@x>', code=220, digest='d1')
    b.op('read', node='b', message_id='<m@x>', code=220, digest='d1')
    b.op('withdraw', node='b', message_id='<m@x>', authorized=True)
    b.op('read', node='b', message_id='<m@x>', code=430)                            # withdrawn: absent is fine
    return b


class ConvergenceTests(unittest.TestCase):
    def kinds(self, b):
        return sorted(a.kind for a in convergence.check(b.records))

    def test_clean_history_has_no_anomaly(self):
        self.assertEqual(self.kinds(clean()), [])

    def test_v1_accepted_twice(self):
        b = clean().op('transfer', node='a', message_id='<m@x>', digest='d1', code=235)
        self.assertEqual(self.kinds(b), ['V1'])

    def test_v2_accepted_then_absent(self):
        b = Builder().op('transfer', node='b', message_id='<n@x>', digest='d', code=235)
        b.op('read', node='b', message_id='<n@x>', code=430)
        self.assertEqual(self.kinds(b), ['V2'])
        excused = Builder().op('transfer', node='b', message_id='<n@x>', digest='d', code=235)
        excused.op('crash', node='b').op('read', node='b', message_id='<n@x>', code=430)
        self.assertEqual(self.kinds(excused), [])

    def test_v3_changed_body(self):
        b = Builder().op('post', node='a', message_id='<n@x>', digest='d', code=240)
        b.op('read', node='a', message_id='<n@x>', code=220, digest='e')
        self.assertEqual(self.kinds(b), ['V3'])

    def test_v4_divergence(self):
        b = Builder().op('read', node='a', message_id='<n@x>', code=220, digest='d')
        b.op('read', node='b', message_id='<n@x>', code=220, digest='e')
        self.assertEqual(self.kinds(b), ['V4'])
        same = Builder().op('read', node='a', message_id='<n@x>', code=220, digest='d')
        same.op('read', node='b', message_id='<n@x>', code=220, digest='d')
        self.assertEqual(self.kinds(same), [])


if __name__ == '__main__':
    unittest.main()
