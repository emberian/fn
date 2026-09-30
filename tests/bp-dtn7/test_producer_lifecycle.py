"""Driver lifecycle checks; these are not native image evidence."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
spec = importlib.util.spec_from_file_location('receipt_lab', HERE / 'run_fn_dtn7_app_receipt.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class FakeLab:
    def __init__(self, root, post_rc=0, ready=True):
        self.root, self.post_rc, self.ready = root, post_rc, ready
        self.calls = []
        self.owner = object()

    def path(self, name):
        return self.root / name

    def fn(self, tag, *args, **kwargs):
        self.calls.append((tag, args, kwargs))
        return types.SimpleNamespace(returncode=self.post_rc if tag == 'post' else 0)

    def spawn(self, *args, **kwargs):
        self.calls.append(('spawn', args, kwargs))
        return self.owner, self.path('owner.log')

    def wait_log(self, *args):
        return self.ready

    def stop(self, owner):
        assert owner is self.owner
        self.calls.append(('stop',))


class FakeClient:
    def __init__(self, port):
        pass

    def __enter__(self):
        return self

    def __exit__(self, *args):
        pass

    def article(self, mid):
        return b'Path: injected!not-for-mail\r\n\r\nactual stored bytes\r\n'


class ProducerLifecycle(unittest.TestCase):
    def run_case(self, post_rc=0, ready=True):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        lab = FakeLab(Path(self.temp.name), post_rc, ready)
        payload = lab.path('input')
        payload.write_bytes(b'input bytes differ')
        return lab, payload

    def test_actual_core_bytes_and_owner_stopped_before_return(self):
        lab, payload = self.run_case()
        with patch('tests.native_harness.Client', FakeClient):
            result = module.post_producer_articles(lab, '/explicit/default', '/store',
                                                   [('post', '<id>', payload)])
        self.assertEqual(result['<id>'], FakeClient(0).article('<id>'))
        self.assertEqual(lab.path('post.stored-article').read_bytes(), result['<id>'])
        self.assertEqual(lab.calls[-1], ('stop',))
        post = next(call for call in lab.calls if call[0] == 'post')
        self.assertEqual(post[1][:3], ('operator', lab.path('producer.toml'), 'post'))
        self.assertEqual(post[2]['image'], '/explicit/default')

    def test_refused_uncertain_and_unready_stop_owner(self):
        for rc, ready in ((1, True), (3, True), (0, False)):
            with self.subTest(rc=rc, ready=ready):
                lab, payload = self.run_case(rc, ready)
                with patch('tests.native_harness.Client', FakeClient), self.assertRaises(RuntimeError):
                    module.post_producer_articles(lab, '/explicit/default', '/store',
                                                 [('post', '<id>', payload)])
                self.assertEqual(lab.calls[-1], ('stop',))
                self.assertFalse(lab.path('post.stored-article').exists())


if __name__ == '__main__':
    unittest.main()
