"""Adapter controls: no image, ACL2 or SBCL is started."""
import argparse
import inspect
import json
import os
from pathlib import Path
import socketserver
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch
import tomllib

import tests.native_harness as native_harness
from . import inventory, node, run_natives, shim


class HarnessTests(unittest.TestCase):
    def setUp(self):
        shim.uninstall()
        shim.install('fn1')
        self.addCleanup(shim.uninstall)

    def test_import_aliases(self):
        shim.install('fn2')
        scope = {}
        exec('from tests.native_harness import Node, Client\n'
             'from tests import native_harness\n'
             'import tests.native_harness as h', scope)
        self.assertIs(scope['Node'], node.Fn2Backend)
        self.assertIs(scope['Client'], shim.Client)
        self.assertIs(scope['native_harness'], native_harness)
        self.assertIs(scope['h'], native_harness)
        self.assertIs(node.fn1, native_harness)

    def test_constructor_and_config(self):
        self.assertEqual(inspect.signature(node.Fn2Backend), inspect.signature(node.ORIGINAL_NODE))
        self.assertEqual(set(node.CONFIG_KEYS),
                         {r['value'] for r in inventory.load()['aggregates']['config_keys']})
        n = node.Fn2Backend(self, 'absent', listener=True,
            tls='key_exchange = "hybrid-preferred"',
            extra='tls_port = 1563\ntls_cert = "cert.pem"\ntls_key = "key.pem"\n',
            cold_resources={'cold_workers': 3, 'output_heap_octets': 4096})
        config = tomllib.loads(n.config.read_text())
        self.assertEqual(config['store']['path'], str(n.store_path))
        self.assertEqual(config['listener'], dict(host='127.0.0.1', port=n.port,
                         tls_port=1563, tls_cert='cert.pem', tls_key='key.pem'))
        self.assertEqual(config['control']['path'], str(n.control))
        self.assertEqual(config['tls']['key_exchange'], 'hybrid-preferred')
        self.assertEqual(config['profile'], dict(cold_workers=3, output_heap_octets=4096))
        self.assertNotIn('resources', config)
        n.write_config(protected_only=True)
        self.assertTrue(tomllib.loads(n.config.read_text())['auth']['protected_only'])
        self.assertIs(n.socket, n)

    def test_module_patches_use_the_real_module(self):
        for backend in ('fn1', 'fn2'):
            shim.install(backend)
            for name in ('start', 'Node', 'Client', '_NODE_DEAD', '_line_containing'):
                with self.subTest(backend=backend, name=name):
                    original = getattr(native_harness, name)
                    with patch.object(native_harness, name) as outer:
                        self.assertIs(getattr(node.fn1, name), outer)
                        with patch.object(native_harness, name) as inner:
                            self.assertIs(getattr(node.fn1, name), inner)
                        self.assertIs(getattr(node.fn1, name), outer)
                    self.assertIs(getattr(native_harness, name), original)
        with patch.object(native_harness, 'h1c_new_name', create=True) as value:
            self.assertIs(node.fn1.h1c_new_name, value)
        self.assertNotIn('h1c_new_name', vars(native_harness))

    def test_install_uninstall_restores_every_patch_point(self):
        shim.uninstall()
        originals = {name: getattr(native_harness, name) for name in shim.PATCH_POINTS}
        for backend in ('fn1', 'fn2', 'fn2', 'fn1'):
            self.assertIs(shim.install(backend), native_harness)
            for name, replacements in shim.PATCH_POINTS.items():
                self.assertIs(getattr(native_harness, name), replacements.get(backend, originals[name]))
        shim.uninstall()
        shim.uninstall()
        for name, original in originals.items():
            self.assertIs(getattr(native_harness, name), original)
        with patch.object(native_harness, 'run') as replacement:
            shim.install('fn2')
            shim.uninstall()
            self.assertIs(native_harness.run, replacement)
        with self.assertRaises(ValueError):
            shim.install('unknown')
        self.assertIs(node.Fn1Backend.__bases__[0], originals['Node'])

    def test_importing_shim_changes_nothing(self):
        # A fresh interpreter exercises import, not an already cached module.
        source = """import sys
import tests
import tests.native_harness as native_harness
before = dict(vars(native_harness))
from fn2.tests.harness import shim
assert vars(native_harness).keys() == before.keys()
assert all(vars(native_harness)[name] is value for name, value in before.items())
assert sys.modules['tests.native_harness'] is native_harness
assert tests.native_harness is native_harness
assert 'fn1_native_harness' not in sys.modules
assert shim.node.Fn1Backend.__bases__[0] is before['Node']
"""
        result = subprocess.run([sys.executable, '-c', source], cwd=node.ROOT,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_patched_start_preserves_fn1_lifecycle_scenarios(self):
        from tests import test_native_harness as controls
        names = (
            'test_a_planned_death_before_readiness_requires_its_actual_cut_marker',
            'test_a_restart_after_a_named_cut_needs_its_own_greeting_and_has_no_cut_allowance',
            'test_ready_none_is_asynchronous_and_an_unanswered_start_still_owes_liveness',
        )
        # The original controls already supply fake processes, including negative cases.
        for adapted in (False, True):
            shim.uninstall()
            if adapted:
                shim.install('fn1')
            with patch.object(controls, 'native_harness', native_harness), patch.dict(
                    os.environ, {'FN2_OBSERVE_DIR': ''}):
                for name in names:
                    with self.subTest(adapted=adapted, scenario=name):
                        result = unittest.TestResult()
                        controls.NodeLivenessTests(name).run(result)
                        self.assertEqual(result.testsRun, 1)
                        self.assertEqual(result.errors + result.failures + result.skipped, [])

    def test_stub_execution_entries_are_named(self):
        n = node.Fn2Backend(self, 'absent')
        for operation, args in [('start', ()), ('try_start', ()), ('invoke', ('status',)),
                                ('operator', ('status',)), ('store', ('init',)), ('init', ()),
                                ('post', ('id', b'payload')), ('start_store_owner', ()),
                                ('kill_at', ('before-persist',)), ('session', ())]:
            with self.subTest(operation=operation), self.assertRaisesRegex(
                    node.fn1.NodeDead, '^' + run_natives.PREFIX):
                getattr(n, operation)(*args)

    def test_images_do_not_skip_fn2(self):
        shim.install('fn2')
        image = native_harness.native_image('FN_NATIVE_HOST')
        self.assertEqual(image, node.ROOT / 'fn2/host/fn')
        self.assertTrue(native_harness.executable(image))
        @native_harness.requires(image)
        def case():
            return 'ran'
        self.assertEqual(case(), 'ran')
        self.assertFalse(getattr(case, '__unittest_skip__', False))
        with self.assertRaisesRegex(node.fn1.NodeDead, '^' + run_natives.PREFIX):
            native_harness.run([image, '--fn', 'operator', 'config', 'run'])
        self.assertIs(native_harness.slow, node.fn1.slow)

    def test_fn1_inheritance_and_dispatch(self):
        shim.install('fn1')
        self.assertTrue(issubclass(native_harness.Node, node.ORIGINAL_NODE))
        self.assertIs(native_harness.native_image, shim.ORIGINALS['native_image'])
        self.assertIs(native_harness.requires, shim.ORIGINALS['requires'])
        self.assertIs(native_harness.start, shim.ORIGINALS['start'])
        self.assertIs(native_harness.installed_launcher, shim.ORIGINALS['installed_launcher'])
        n = native_harness.Node(self, 'absent')
        with patch.object(node.ORIGINAL_NODE, 'invoke', return_value='sent') as invoke:
            self.assertEqual(n.invoke('status', timeout=1), 'sent')
            invoke.assert_called_once_with('status', timeout=1)
        for name in ('snapshot', 'restore', 'use_tls',
                     'exited', 'environment', 'argv', 'launch', 'log_on_failure'):
            self.assertIs(getattr(node.Fn1Backend, name), getattr(node.ORIGINAL_NODE, name))

    def test_observe_client_exchange(self):
        class Handler(socketserver.StreamRequestHandler):
            def handle(self):
                self.wfile.write(b'200 hello\r\n')
                self.server.command = self.rfile.readline()
                self.wfile.write(b'200 hello\r\n')
                self.server.post = self.rfile.readline()
                self.wfile.write(b'340 send\r\n')
                self.server.article = b''
                while (line := self.rfile.readline()) != b'.\r\n':
                    self.server.article += line
                self.wfile.write(b'240 accepted\r\n')
        with tempfile.TemporaryDirectory() as directory, socketserver.TCPServer(
                ('127.0.0.1', 0), Handler) as server:
            thread = threading.Thread(target=server.handle_request)
            thread.start()
            try:
                with patch.dict(os.environ, FN2_OBSERVE_DIR=directory, FN2_TEST_ID='wire.control'):
                    client = shim.Client(server.server_address[1])
                    try:
                        self.assertEqual(client.command(b'DATE'), b'200 hello\r\n')
                        self.assertEqual(client.post(b'Message-ID: <x>\r\n\r\n.body\r\n'),
                                         (b'340 send\r\n', b'240 accepted\r\n'))
                    finally:
                        client.close(quit=False)
                records = [json.loads(line) for line in
                           (Path(directory) / 'wire.control.jsonl').read_text().splitlines()]
                commands = [r for r in records if r['kind'] == 'client.command']
                self.assertEqual([r['phase'] for r in commands], ['invoke', 'ok'] * 2)
                self.assertEqual(commands[0]['command_hex'], b'DATE'.hex())
                self.assertEqual(commands[1]['reply_hex'], b'200 hello\r\n'.hex())
                self.assertTrue(all(r['test'] == 'wire.control' and isinstance(r['t'], int)
                                    for r in records))
                self.assertEqual(len({r['conn'] for r in records}), 1)
                self.assertEqual({r['node'] for r in records}, {f'port:{server.server_address[1]}'})
                for call in {r['call'] for r in records}:
                    self.assertEqual([r['phase'] for r in records if r['call'] == call], ['invoke', 'ok'])
                self.assertIn((server.article + b'.\r\n').hex(),
                              [r.get('sent_hex') for r in records])
            finally:
                thread.join(timeout=5)
            self.assertFalse(thread.is_alive())
            self.assertEqual(server.command, b'DATE\r\n')

    def test_observe_start_stop_preserves_process(self):
        from types import SimpleNamespace
        process = SimpleNamespace(pid=123, process=SimpleNamespace(args=['fn', '--fn', 'run']),
            poll=lambda: 0, stdout=SimpleNamespace(since=lambda offset: b'LISTENING 119\n'),
            stderr=SimpleNamespace(since=lambda offset: b'accepted operator run\n'))
        with tempfile.TemporaryDirectory() as directory, patch.dict(
                os.environ, FN2_OBSERVE_DIR=directory, FN2_TEST_ID='process.control'):
            n = node.Fn1Backend(self, 'absent')
            n.process = process
            with patch.object(node.ORIGINAL_NODE, 'start', return_value=process):
                self.assertIs(n.start(env={'FN_NATIVE_CONTROL_FAULT': 'cut'},
                                     death_cut=(-9, b'CUT')), process)
            with patch.object(node.ORIGINAL_NODE, 'stop', return_value=0):
                self.assertEqual(n.stop(), 0)
            records = [json.loads(line) for line in
                       (Path(directory) / 'process.control.jsonl').read_text().splitlines()]
            self.assertEqual([r['phase'] for r in records], ['invoke', 'ok', 'invoke', 'ok'])
            self.assertEqual(records[1]['pid'], 123)
            self.assertEqual(records[1]['argv'], ['fn', '--fn', 'run'])
            self.assertEqual(records[1]['exit_class'], 'OK')
            self.assertEqual(records[1]['stdout'], 'LISTENING 119\n')
            self.assertEqual(records[0]['env_selectors'], {'FN_NATIVE_CONTROL_FAULT': 'cut'})
            self.assertEqual(records[0]['death_cut'], [-9, 'CUT'])
            self.assertTrue(all(r['node'] == str(n.root) and r['control'] == str(n.control)
                                for r in records))
            with patch.object(shim.Client, '_connect'):
                self.assertEqual(n.session()._observation['node'], str(n.root))
                self.assertEqual(shim.Client(n.port)._observation['node'], str(n.root))

    def test_direct_process_kill_and_finish(self):
        from types import SimpleNamespace
        from unittest.mock import Mock
        with tempfile.TemporaryDirectory() as directory, patch.dict(
                os.environ, FN2_OBSERVE_DIR=directory, FN2_TEST_ID='death'):
            n = node.Fn1Backend(self, 'absent')
            p = node.fn1.NativeProcess.__new__(node.fn1.NativeProcess)
            p.pid, p.process = 123, SimpleNamespace(args=['fn'], poll=lambda: -9)
            p.stdout, p.stderr = (SimpleNamespace(since=lambda _: b'CUT\n'),
                                  SimpleNamespace(since=lambda _: b''))
            p.signal, p.finish = Mock(), Mock()
            signal, finish = p.signal, p.finish
            with patch.object(node.ORIGINAL_NODE, 'start', return_value=p):
                self.assertIs(n.start(death_cut=(-9, b'CUT')), p)
            p.kill()
            p.finish()
            signal.assert_called_once_with(9)
            finish.assert_called_once_with()
            records = [json.loads(line) for line in (Path(directory) / 'death.jsonl').read_text().splitlines()]
            self.assertEqual(records[-1]['signal'], 9)
            self.assertEqual(records[-1]['exit_code'], -9)
            self.assertEqual(records[-1]['death_cut'], [-9, 'CUT'])

    def test_snapshots_and_capture_limits(self):
        import hashlib
        import subprocess
        with tempfile.TemporaryDirectory() as directory, patch.dict(
                os.environ, FN2_OBSERVE_DIR=directory, FN2_TEST_ID='snapshots'):
            n = node.Fn1Backend(self, 'absent')
            path, large = Path(directory) / 'cursor.fncu', Path(directory) / 'large'
            path.write_bytes(b'before')
            large.write_bytes(b'x' * 65537)
            def invoke(*words, **kw):
                path.write_bytes(b'after')
                return subprocess.CompletedProcess([], 0, b'consumer accepted', b'')
            with patch.object(node.ORIGINAL_NODE, 'invoke', side_effect=invoke):
                n.invoke('consumer', 'position', str(path), str(large))
            records = [json.loads(line) for line in (Path(directory) / 'snapshots.jsonl').read_text().splitlines()]
            self.assertEqual(records[0]['files_before'][str(path)], b'before'.hex())
            self.assertEqual(records[1]['files_after'][str(path)], b'after'.hex())
            self.assertEqual(records[1]['files_after'][str(large)],
                             dict(length=65537, sha256=hashlib.sha256(b'x' * 65537).hexdigest()))
        for size in (1 << 20, (1 << 20) + 1):
            captured = node.sent(b'x' * size)
            self.assertEqual(len(bytes.fromhex(captured['sent_hex'])), size if size == 1 << 20 else 65536)
            if size > 1 << 20:
                self.assertEqual(captured['sent_len'], size)
                self.assertEqual(captured['sent_sha256'], hashlib.sha256(b'x' * size).hexdigest())

    def test_disabled_observer_has_no_reads(self):
        class Untouchable:
            def __getattribute__(self, name):
                raise AssertionError('extra attribute read: ' + name)
        with patch.dict(os.environ, {}, clear=True), patch.object(Path, 'open', side_effect=AssertionError), \
                patch.object(node, 'node_fields', side_effect=AssertionError), \
                patch.object(node, 'sent', side_effect=AssertionError), \
                patch.object(node, 'snapshots', side_effect=AssertionError), \
                patch.object(node, 'emit', side_effect=AssertionError):
            for name, args in [('send', (b'x',)), ('post', (b'x',)), ('multiline', (b'DATE',)),
                               ('starttls', ()), ('close', ()), ('command', (b'DATE',))]:
                wrapped = node.observed('client.' + name, lambda *a: a[0].missing)(lambda *a: 42)
                self.assertEqual(wrapped(Untouchable(), *args), 42)
            n = node.Fn1Backend.__new__(node.Fn1Backend)
            with patch.object(node.ORIGINAL_NODE, 'start', return_value=42):
                self.assertEqual(n.start(), 42)
            client = shim.Client.__new__(shim.Client)
            with patch.object(shim.ORIGINAL_CLIENT, '__init__', return_value=None):
                client.__init__(123)
            self.assertEqual(vars(client), {})
            client.sock = type('Socket', (), {'sendall': lambda *args: None})()
            client.send(b'unchanged')  # real alias, with no observation attributes

    def test_observe_invocations_and_unknown_outcomes(self):
        import subprocess
        with tempfile.TemporaryDirectory() as directory, patch.dict(
                os.environ, FN2_OBSERVE_DIR=directory, FN2_TEST_ID='invoke.control'):
            n = node.Fn1Backend(self, 'absent')
            answer = subprocess.CompletedProcess(['absent'], 1, b'x' * 5000, b'refused')
            with patch.object(node.ORIGINAL_NODE, 'invoke', return_value=answer):
                self.assertIs(n.invoke('store', 'status'), answer)
            with patch.object(node.ORIGINAL_NODE, 'invoke', side_effect=TimeoutError('unknown')):
                with self.assertRaises(TimeoutError):
                    n.invoke('store', 'status')
            records = [json.loads(line) for line in
                       (Path(directory) / 'invoke.control.jsonl').read_text().splitlines()]
            self.assertEqual([r['phase'] for r in records], ['invoke', 'fail', 'invoke', 'info'])
            self.assertEqual(len(records[1]['stdout']), 4096)
            self.assertEqual(records[1]['exit_class'], 'REFUSED')
            self.assertEqual(records[3]['exception'], 'unknown')

    def test_assertion_counter_and_outcomes(self):
        class Cases(unittest.TestCase):
            def test_three(self):
                self.assertTrue(True)
                self.assertEqual(3, 3)
                self.assertIsNone(None)
        result = run_natives.Result()
        original = unittest.TestCase.assertTrue
        with run_natives.count_assertions(result):
            Cases('test_three').run(result)
        self.assertEqual(result.assertions, 3)
        self.assertEqual(result.records[0]['assertions'], 3)
        self.assertEqual(result.records[0]['outcome'], 'ok')
        self.assertIs(unittest.TestCase.assertTrue, original)
        self.assertIs(unittest.TestCase.failureException, AssertionError)
        class Failing(unittest.TestCase):
            def runTest(self):
                self.assertEqual(1, 2)
        result = run_natives.Result()
        with run_natives.count_assertions(result):
            Failing().run(result)
        self.assertEqual(result.records[0]['outcome'], 'fail')
        # Integer assertEqual raises directly in _baseAssertEqual.
        self.assertEqual(result.records[0]['assertions'], 1)

    def test_fixture_failure_is_attributed_without_multiplying_assertions(self):
        source = '''import unittest
from tests.native_harness import Node, class_case
class Cases(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        Node(class_case(cls), "absent").start()
    def test_one(self): pass
    def test_two(self): pass
'''
        with tempfile.TemporaryDirectory(prefix='h1b_fixture_', dir=node.ROOT / 'build') as tmp:
            path = Path(tmp)
            (path / 'fixture.py').write_text(source)
            name = 'build.' + path.name + '.fixture'
            result = run_natives.run_one(name, 'fn2')
        self.assertEqual(len(result['tests']), 2)
        self.assertTrue(all(t['classification'] == 'named-node-dead' for t in result['tests']))
        self.assertEqual(result['assertions'], 0)
        self.assertEqual(len(result['fixtures']), 1)

    def test_stub_observation_names_words_and_unknown_process(self):
        with tempfile.TemporaryDirectory() as directory, patch.dict(
                os.environ, FN2_OBSERVE_DIR=directory, FN2_TEST_ID='stub.control'):
            n = node.Fn2Backend(self, 'absent')
            with self.assertRaises(node.fn1.NodeDead):
                n.invoke('operator', 'a path with spaces', 'status')
            with self.assertRaises(node.fn1.NodeDead):
                n.start()
            records = [json.loads(line) for line in
                       (Path(directory) / 'stub.control.jsonl').read_text().splitlines()]
            self.assertEqual([r['phase'] for r in records], ['invoke', 'info', 'invoke', 'info'])
            self.assertEqual(records[0]['words'], ['operator', 'a path with spaces', 'status'])
            self.assertIsNone(records[2]['pid'])
            self.assertEqual(records[2]['argv'], ['absent', '--fn', 'operator', str(n.config), 'run'])

    def test_raw_sbcl_guard(self):
        with self.assertRaisesRegex(RuntimeError, 'raw SBCL execution is forbidden'):
            run_natives.forbid_raw_sbcl('subprocess.Popen', ('/usr/bin/sbcl',))
        run_natives.forbid_raw_sbcl('subprocess.Popen', ('/usr/bin/openssl',))

    def test_existing_child_pid_refuses_before_spawn(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)
            (path / 'control.pid').write_text('123\n')
            (path / 'control.json').write_text('previous result')
            args = argparse.Namespace(out=directory, backend='fn2', retired_skip=False, timeout=1)
            with patch.object(run_natives.subprocess, 'Popen') as popen:
                with self.assertRaises(FileExistsError):
                    run_natives.child('control', args)
                popen.assert_not_called()
            self.assertEqual((path / 'control.json').read_text(), 'previous result')

    def test_timeout_reaps_recorded_child(self):
        with tempfile.TemporaryDirectory(prefix='h1b_timeout_', dir=node.ROOT / 'build') as tmp:
            path = Path(tmp)
            (path / 'hang.py').write_text('import time, unittest\n'
                'class Hang(unittest.TestCase):\n'
                '    def test_hang(self): time.sleep(600)\n')
            name = 'build.' + path.name + '.hang'
            args = argparse.Namespace(out=str(path), backend='fn2', retired_skip=False, timeout=1)
            result = run_natives.child(name, args)
            self.assertEqual(result['status'], 'timeout')
            self.assertEqual(json.loads((path / (name + '.json')).read_text())['status'], 'timeout')
            self.assertFalse((path / (name + '.pid')).exists())
            with self.assertRaises(ProcessLookupError):
                os.kill(result['pid'], 0)


class ProvisionTests(unittest.TestCase):
    def args(self, **changes):
        return argparse.Namespace(**(dict(backend='fn2', env_plan='developer,production',
                                         identity=None, source=None) | changes))

    def output(self, stdout, code=0, stderr=''):
        import subprocess
        return subprocess.CompletedProcess([], code, stdout, stderr)

    def test_plan_is_once_isolated_and_expands_without_shell(self):
        plan = ('tests.test_native_auth FN_NATIVE_HOST=$T/build/fn-host FN_OPENSSL=$FN_TEST_OPENSSL_BIN\n'
                'tests.test_native_control FN_NATIVE_DEVELOPER_HOST=${T}/build/fn-host-developer '
                'FN_OPEN_DEPTH_FIXTURES=$FN_FIXTURES_DIR FN_RUN_CONSUMER_EXCHANGE=1\n')
        parent = dict(PATH='/bin', FN2_HOST='/absent/fn2', FN_TEST_OPENSSL_BIN='/tools/a b/openssl',
                      FN_FIXTURES_DIR='/fixture/$(never-run)', FN_NATIVE_HOST='leaked')
        original = parent.copy()
        with patch.object(run_natives.subprocess, 'run', return_value=self.output(plan)) as run:
            result = run_natives.provision(['auth', 'control'], self.args(), parent)
        self.assertEqual(run.call_count, 1)
        self.assertEqual(run.call_args.args[0][-2:], ['tests.test_native_auth', 'tests.test_native_control'])
        self.assertEqual(parent, original)
        self.assertEqual(result['auth']['FN_NATIVE_HOST'], str(run_natives.placeholder()))
        self.assertEqual(result['auth']['FN_OPENSSL'], '/tools/a b/openssl')
        self.assertNotIn('FN_RUN_CONSUMER_EXCHANGE', result['auth'])
        self.assertEqual(result['control']['FN_NATIVE_HOST'], result['auth']['FN2_HOST'])
        self.assertEqual(result['control']['FN_OPEN_DEPTH_FIXTURES'], '/fixture/$(never-run)')
        self.assertEqual(result['control']['FN_RUN_CONSUMER_EXCHANGE'], '1')
        from tools.native_env import IDENTITY
        from tools.native_env import image_identity
        self.assertEqual({k: result['auth'][k] for k in IDENTITY},
                         image_identity(run_natives.placeholder(), 'fn2-host-placeholder'))

    def test_fn1_real_paths_and_identity_exports(self):
        from tools.native_env import IDENTITY
        exports = ''.join(f'export {k}=value{i}\n' for i, k in enumerate(IDENTITY))
        with patch.object(run_natives.subprocess, 'run', side_effect=[
                self.output('tests.test_native_auth FN_NATIVE_HOST=$T/build/fn-host\n'),
                self.output(exports)]) as run:
            env = run_natives.provision(['auth'], self.args(backend='fn1', identity='/image', source='sha'), {})['auth']
        self.assertEqual(env['FN_NATIVE_HOST'], str(node.ROOT / 'build/fn-host'))
        self.assertEqual({k: env[k] for k in IDENTITY}, {k: f'value{i}' for i,k in enumerate(IDENTITY)})
        self.assertIn('--export', run.call_args.args[0])
        self.assertEqual(run.call_count, 2)

    def test_fn2_present_executable_identity(self):
        import hashlib
        from tools.native_env import IDENTITY
        with tempfile.TemporaryDirectory() as tmp:
            path = run_natives.placeholder(tmp)
            with patch.object(run_natives.subprocess, 'run') as run:
                env = run_natives.provision(['auth'], self.args(env_plan=None, identity='ignored', source='source'),
                                           {'FN2_HOST': str(path)})['auth']
            run.assert_not_called()
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            from tools.native_env import image_identity
            self.assertEqual({k: env[k] for k in IDENTITY}, image_identity(path, 'source'))
            self.assertEqual(env['FN_NATIVE_DEVELOPER_CORE_SHA256'], env['FN_NATIVE_CORE_SHA256'])
            self.assertEqual(env['FN_NATIVE_DEVELOPER_LAUNCHER_SHA256'], digest)
            self.assertEqual(env['FN_NATIVE_IMAGE_SOURCE_SHA'], 'source')

    def test_no_options_preserves_old_environment(self):
        with patch.object(run_natives.subprocess, 'run') as run:
            result = run_natives.provision(['auth'], self.args(backend='fn1', env_plan=None), {'FN_NATIVE_HOST': 'old'})
        run.assert_not_called()
        self.assertEqual(result['auth'], dict(FN_NATIVE_HOST='old', FN2_NODE_BACKEND='fn1'))

    def test_invalid_plan_and_incomplete_identity_are_rejected(self):
        for plan in ('', 'tests.test_native_other X=1',
                     'tests.test_native_auth X=$UNKNOWN',
                     'tests.test_native_auth BAD',
                     'tests.test_native_auth\ntests.test_native_auth'):
            with self.subTest(plan=plan), patch.object(run_natives.subprocess, 'run',
                    return_value=self.output(plan)), self.assertRaises(ValueError):
                run_natives.provision(['auth'], self.args(), {})
        with patch.object(run_natives.subprocess, 'run', return_value=self.output('export FN_NATIVE_CORE_SHA256=x')):
            with self.assertRaisesRegex(ValueError, 'all four'):
                run_natives.provision(['auth'], self.args(backend='fn1', env_plan=None, identity='x', source='y'), {})

    def test_plan_failure_does_not_spawn_child(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(run_natives.subprocess, 'run',
                return_value=self.output('', 2, 'missing image')), patch.object(run_natives, 'child') as child:
            with self.assertRaisesRegex(ValueError, 'plan exit 2'):
                run_natives.main(['--modules', 'auth', '--backend', 'fn2', '--env-plan', 'production', '--out', tmp])
            child.assert_not_called()

    def test_placeholder_is_executable_idempotent_and_refuses(self):
        import subprocess
        from tools.outcome_codes import EXIT
        with tempfile.TemporaryDirectory() as directory:
            host = run_natives.placeholder(directory)
            before = {p: (p.read_bytes(), p.stat().st_mtime_ns)
                      for p in Path(directory).rglob('*') if p.is_file()}
            self.assertEqual(run_natives.placeholder(directory), host)
            self.assertEqual(before, {p: (p.read_bytes(), p.stat().st_mtime_ns) for p in before})
            self.assertTrue(os.access(host, os.X_OK))
            answer = subprocess.run([host, 'operator', 'a path', 'run'], capture_output=True, timeout=5)
            self.assertEqual(answer.returncode, EXIT.REFUSED)
            self.assertEqual(answer.stdout, b'')
            self.assertEqual(answer.stderr.decode(), run_natives.PLACEHOLDER_PREFIX + ' operator a path run\n')
            env = run_natives.provision(['auth'], self.args(env_plan=None),
                                       {'FN2_HOST': str(host / 'absent')})['auth']
            self.assertTrue(Path(env['FN2_HOST']).is_file())

    def test_intended_skip_is_module_and_literal_prefix_specific(self):
        table = run_natives.intended_skips()
        with patch.object(run_natives.sys, 'platform', 'darwin'):
            for entry in table:
                reason = entry['reason_prefix']
                for module in entry['modules']:
                    self.assertEqual(run_natives.intended_category(module, reason + ' detail'), entry['category'])
                    self.assertIsNone(run_natives.intended_category('unlisted-module', reason))
                    self.assertIsNone(run_natives.intended_category(module, 'unlisted ' + reason))
        records = [run_natives.row('planted', 'skip', reason='unlisted prerequisite',
                   placeholder_reason=run_natives.PLACEHOLDER_PREFIX + ' earlier invocation')]
        result = run_natives.finish('auth', 'fn2', records, 1, 0)
        self.assertEqual(result['tests'][0]['classification'], 'other')
        self.assertFalse(result['tests'][0]['intended_skip'])
        with patch.object(run_natives.sys, 'platform', 'linux'):
            self.assertIsNone(run_natives.intended_category('checkpoint', table[0]['reason_prefix']))

    def test_refusal_evidence_is_scoped_and_does_not_change_outcomes(self):
        import subprocess
        with tempfile.TemporaryDirectory() as directory:
            host = run_natives.placeholder(directory)
            class Cases(unittest.TestCase):
                def test_pipe(self):
                    subprocess.run([host, 'pipe'], capture_output=True, timeout=5)
                    self.fail('terse failure')
                def test_inherited(self):
                    subprocess.run([host, 'inherited'], timeout=5)
                    self.fail('terse failure')
                def test_unlisted(self):
                    self.skipTest('unlisted prerequisite')
            result = run_natives.Result()
            with run_natives.capture_refusals(result):
                unittest.defaultTestLoader.loadTestsFromTestCase(Cases).run(result)
            data = run_natives.finish('control', 'fn2', result.records, 3, 0)
            self.assertEqual([r['classification'] for r in data['tests']],
                             ['named-placeholder', 'named-placeholder', 'other'])
            entry = run_natives.row('multiline', 'fail', exception='terse',
                exception_text='terse\n' + run_natives.PLACEHOLDER_PREFIX + ' command')
            self.assertEqual(run_natives.finish('control', 'fn2', [entry], 1, 0)
                             ['tests'][0]['classification'], 'named-placeholder')

    def test_real_plan_reaches_stub_past_opt_in_and_identity(self):
        args = self.args(env_plan='developer,production,dtn,dtn-developer,reference,developer-stripped')
        envs = run_natives.provision(['consumer_exchange', 'peering'], args, {})
        self.assertEqual(envs['consumer_exchange']['FN_RUN_CONSUMER_EXCHANGE'], '1')
        self.assertEqual(envs['peering']['FN_NATIVE_IMAGE_SOURCE_SHA'], 'fn2-host-placeholder')
        with patch.dict(os.environ, envs['consumer_exchange'], clear=True), \
                patch.object(node.fn1, 'free_port', return_value=119):
            try:
                result = run_natives.run_one('consumer_exchange', 'fn2', True)
            finally:
                shim.uninstall()
        self.assertGreater(sum(t.get('classification') == 'named-node-dead' for t in result['tests']), 0)
        self.assertFalse(any('set FN_RUN_CONSUMER_EXCHANGE' in t['skip_reason'] for t in result['tests']))


if __name__ == '__main__':
    unittest.main()
