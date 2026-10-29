"""Shared surface gates and hooks. Drivers never turn missing evidence into a pass."""
import argparse
import functools
import importlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import unittest

from fn2.tests.harness import run_natives

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = json.loads(Path(__file__).with_name('families.json').read_text())
FAMILIES = MANIFEST['families']
SKIP = 'layer D/E not yet serving'
# These are the first relevant Fn2Backend execution requirements in node.py.
REQUIREMENTS = {
    'nntp': 'socket needs NNTP 200/201 greeting on listener.port / listener.tls_port',
    'consumer': 'operator needs operator CONFIG ...; FNCT control socket',
    'operator': 'init needs operator CONFIG init [--profile P] GROUP...',
    'web': 'start needs LISTENING-WEB PORT and an HTTP greeting',
    'peering': 'start needs LISTENING PORT and an NNTP greeting',
    'bp': 'invoke needs fn --fn carry / bp-route',
    'tls_auth': 'socket needs NNTP 200/201 greeting on listener.port / listener.tls_port',
    'config_limits': 'try_start needs operator CONFIG run; LISTENING or a named startup refusal',
    'store_ops': 'store needs store STORE ...',
}
RUN = {}


def serving(family):
    """The one gate, evaluated at execution (also works under unittest discovery)."""
    def decorate(call):
        @functools.wraps(call)
        def wrapped(*args, **kwargs):
            target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
            if target not in MANIFEST['serves']:
                raise ValueError('FN2_SURFACE_TARGET must be fn1 or fn2')
            if family not in MANIFEST['serves'][target]:
                raise unittest.SkipTest(SKIP + ': ' + REQUIREMENTS[family])
            return call(*args, **kwargs)
        return wrapped
    return decorate


def output(family):
    path = Path(RUN.get('out', os.environ.get('FN2_SURFACE_OUT', 'build/surface'))) / family
    path.mkdir(parents=True, exist_ok=True)
    return path


def hook(family, form, case, **kwargs):
    """Optional module:callable; see README for its explicit reporting contract."""
    key = 'FN2_SURFACE_' + form + '_' + family.upper()
    spec = os.environ.get(key)
    if not spec:
        raise unittest.SkipTest(f'{form.lower()} driver owed: {family}; set {key}=module:callable')
    module, name = spec.rsplit(':', 1)
    return getattr(importlib.import_module(module), name)(case=case,
        target=os.environ.get('FN2_SURFACE_TARGET', 'fn2'),
        family=family, out=output(family), **kwargs)


def driver(command, directory, seconds, env=None):
    """Bound a driver and reap only its recorded session, including descendants."""
    directory.mkdir(parents=True, exist_ok=True)
    pidfile = directory / 'driver.pid'
    with pidfile.open('x') as pid, (directory / 'driver.log').open('wb') as log:
        process = None
        try:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log, stderr=log,
                                       start_new_session=True)
            pid.write(str(process.pid) + '\n'); pid.flush()
            return process.wait(timeout=seconds)
        finally:
            if process is not None and process.poll() is None:
                os.killpg(int(pidfile.read_text()), signal.SIGKILL)
                process.wait(timeout=10)
            pidfile.unlink()


class Target:
    """The selected live backend; the model owns expected replies, never this class."""
    def __init__(self, case):
        import tests.native_harness as native_harness
        image = native_harness.native_image('FN_NATIVE_HOST')
        self.node = native_harness.Node(case, image)
        self.node.init('surface.test')
        self.node.start()

    def connect(self):
        return self.node.session(timeout=5)


class SurfaceCase(unittest.TestCase):
    def setUp(self):
        self.evidence = {}

    def native(self, family, name):
        out = output(family) / 'natives'; out.mkdir(exist_ok=True)
        args = argparse.Namespace(out=str(out), backend=os.environ.get('FN2_SURFACE_TARGET', 'fn2'), retired_skip=True,
                                  timeout=300, env_plan=os.environ.get('FN2_SURFACE_IMAGES',
                                  'developer,production,dtn,dtn-developer,reference,developer-stripped'),
                                  identity=os.environ.get('FN2_SURFACE_IDENTITY'),
                                  source=os.environ.get('FN2_SURFACE_SOURCE'))
        environments = RUN.get('native_envs')
        args.module_envs = environments if environments is not None else run_natives.provision([name], args)
        args.module_envs = {name: dict(args.module_envs[name], FN2_OBSERVE_DIR=str(out / 'observe' / name))}
        data = run_natives.child(name, args)
        self.evidence['native'] = data
        self.assertNotEqual(data['status'], 'timeout', f'{name}: timeout')
        self.assertTrue(data['tests'], f'{name}: collected no outcomes')
        for entry in data['tests']:
            with self.subTest(native_test=entry['test']):
                self.assertIn(entry['outcome'], ('ok', 'skip'),
                    f"{entry['outcome']}: {entry['exception'] or entry['skip_reason']}")
        skipped = [entry for entry in data['tests'] if entry['outcome'] == 'skip']
        if skipped:
            self.skipTest('; '.join(dict.fromkeys(entry['skip_reason'] for entry in skipped)))

    def model(self, family):
        raise ValueError('no implemented model adapter: ' + FAMILIES[family]['model'])

    def fuzz(self, family):
        budget = RUN.get('fuzz_remaining', 600)
        if budget <= 0:
            self.skipTest('aggregate fuzz budget exhausted')
        start = time.monotonic()
        try:
            if family != 'nntp' or os.environ.get('FN2_SURFACE_FUZZ_NNTP'):
                command = hook(family, 'FUZZ', self, seconds=budget,
                               corpus=FAMILIES[family]['fuzz']['corpus'])
            else:
                # Public H2b CLI only; no dependency on its changing internals.
                command = [sys.executable, '-m', 'fn2.tests.model.differential', '--target',
                           os.environ.get('FN2_SURFACE_TARGET', 'fn2'),
                           '--seeds', f"0..{RUN.get('examples', 200)-1}", '--mode', 'reader,node,peer',
                           '--steps', '50', '--out', str(output(family) / 'fuzz')]
            if not isinstance(command, list) or not command or not all(isinstance(s, str) for s in command):
                raise ValueError('fuzz hook must return a nonempty argv list')
            status = driver(command, output(family) / 'fuzz', budget)
            self.evidence['fuzz_report'] = str(output(family) / 'fuzz')
            self.assertEqual(status, 0, 'wire fuzz driver failed; see driver.log')
        finally:
            RUN['fuzz_remaining'] = max(0, budget - (time.monotonic() - start))

    def history(self, family):
        if family not in ('nntp', 'consumer'):
            return hook(family, 'HISTORY', self, checkers=FAMILIES[family]['history'])
        from fn2.tests.history import from_observe, consumer, durable, pair
        checker = consumer.check if family == 'consumer' else durable.check
        relevant = consumer.CONSUMER if family == 'consumer' else {'post', 'read'}
        directory = Path(os.environ.get('FN2_SURFACE_HISTORY_' + family.upper(),
                                       str(output(family) / 'natives' / 'observe')))
        reports = []
        for path in sorted(directory.rglob('*.jsonl')):
            adapted = from_observe.adapt(json.loads(line) for line in path.read_text().splitlines())
            ops = [o for o in pair(adapted.history) if o.f in relevant and not o.value.get('observed_only')]
            anomalies = checker(adapted.history)
            reports.append(dict(source=str(path), counts=adapted.counts, unmapped=adapted.unmapped,
                                operations=len(ops), anomalies=[str(a) for a in anomalies]))
            self.assertFalse(anomalies, str(path))
        self.evidence['history'] = reports
        if not any(r['operations'] for r in reports):
            self.skipTest('history driver owed: no mapped ' + family + ' operations observed')

    def fixture(self, family, fixture):
        return hook(family, 'FIXTURE', self, path=ROOT / fixture['path'], contract=fixture['reason'])

    def perf(self, family, row):
        measured = hook(family, 'PERF', self, row=row)
        # Validate the driver shape, never compare a measurement to a threshold.
        if not isinstance(measured, dict) or not {'value', 'unit', 'profile'} <= measured.keys():
            raise ValueError('performance driver must return value, unit, profile')
        self.evidence['performance'] = dict(row=row, **measured)


def cases(module, family, form):
    """One example test per native and per fixture; one perf test per published row."""
    methods = {'__module__': module, 'family': family, 'form': form}
    def add(name, call):
        methods['test_' + re.sub('[^a-zA-Z0-9_]', '_', name)] = serving(family)(call)
    if form == 'E':
        for name in FAMILIES[family]['carried_natives']:
            add('native_' + name, lambda self, name=name: self.native(family, name))
        for index, fixture in enumerate(FAMILIES[family]['fixtures']):
            add('fixture_' + str(index), lambda self, fixture=fixture: self.fixture(family, fixture))
    elif form == 'R':
        for index, row in enumerate(FAMILIES[family]['performance_rows']):
            add(f'row_{index}_{row}', lambda self, row=row: self.perf(family, row))
    else:
        method = dict(S='model', F='fuzz', H='history')[form]
        add(method, lambda self: getattr(self, method)(family))
    return type('TestSurface', (SurfaceCase,), methods)


def form_suite(family, form, loader=None):
    """Generate the old per-form IDs without per-form discovery wrappers."""
    loader = loader or unittest.defaultTestLoader
    info = FAMILIES[family]['forms'][form]
    if not info['applicable'] or info.get('status') == 'owed' or form == 'P':
        return unittest.TestSuite()
    if family == 'nntp' and form == 'S':
        return loader.loadTestsFromName(info['module'])
    return loader.loadTestsFromTestCase(cases(info['module'], family, form))


def family_loader(package):
    """Unittest package hook; discovery does not recurse into generated forms."""
    family = package.rsplit('.', 1)[-1]

    def load_tests(loader, tests, pattern):
        return unittest.TestSuite(form_suite(family, form, loader)
                                  for form in ('E', 'S', 'F', 'H', 'R'))

    return load_tests
