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
import threading
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
# A target names what answers (fn1, or fn2 under one carrier) and the Node backend its natives run against:
# fn2 is the simulator carrier for serves_sim's S forms, fn2-native the loopback-socket carrier for
# serves_native's; both are fn2's backend for everything else.
TARGETS = {'fn1': 'fn1', 'fn2': 'fn2', 'fn2-native': 'fn2'}


def backend(target=None):
    """The Node backend (fn1 or fn2) behind a surface target."""
    target = os.environ.get('FN2_SURFACE_TARGET', 'fn2') if target is None else target
    if target not in TARGETS:
        raise ValueError('FN2_SURFACE_TARGET must be one of ' + ', '.join(TARGETS))
    return TARGETS[target]


def box_budget():
    return MANIFEST['budget'][RUN.get('box', os.environ.get('FN2_SURFACE_BOX', 'laptop'))]


def native_timeout(name):
    box = RUN.get('box', os.environ.get('FN2_SURFACE_BOX', 'laptop'))
    return MANIFEST['native_timeout_overrides'].get(name, {}).get(box,
        MANIFEST['budget'][box]['native_timeout'])


def live_model_settings(family):
    """Live explicit/generation phases, with no shrinking or database replay.

    Hypothesis 6.170.13 core.py:1537-1574 unconditionally replays discovered
    failures for reporting even without Phase.shrink (whose separate guard is
    internal/conjecture/engine.py:1693). No public setting disables that final
    replay. Each live machine records its first failing step through
    live_evidence (OUT/<family>/s-failure.json) before raising, and the
    replay's error carries a pointer to it.
    Fake-target model unit tests retain their own shrinking settings.
    """
    from hypothesis import Phase, settings
    box = RUN.get('box', os.environ.get('FN2_SURFACE_BOX', 'laptop'))
    cadence = FAMILIES[family]['cadence'][box]
    return settings(max_examples=cadence['model_examples'],
                    stateful_step_count=cadence['steps'], deadline=None,
                    database=None, derandomize=True, phases=(Phase.explicit, Phase.generate),
                    report_multiple_bugs=False)


def fuzz_allocations(families, box):
    eligible = [name for name in families if 'F' in FAMILIES[name]['cadence'][box]['forms']
                and FAMILIES[name]['forms']['F']['applicable']
                and FAMILIES[name]['forms']['F'].get('status') != 'owed']
    share = MANIFEST['budget'][box]['fuzz_seconds'] / len(eligible) if eligible else 0
    return dict.fromkeys(eligible, share)


def adjudicate_differences(rows, target, evidence_dir=None):
    """Match exact observations or reviewed predicates; missing evidence stays new."""
    from .adjudication_predicates import PREDICATES
    ledger = json.loads((ROOT / 'fn2/tests/model/adjudications.json').read_text())
    if ledger['schema_version'] != 2:
        raise ValueError('unsupported differential adjudication schema')
    for group in ledger['groups']:
        if ('match' in group) == ('command_pattern' in group):
            raise ValueError('adjudication needs exactly one command matcher')
        if 'match' in group and group['match'] not in PREDICATES:
            raise ValueError('unknown adjudication predicate: ' + group['match'])
    groups = [g for g in reversed(ledger['groups']) if not g.get('superseded_by')]
    result = []
    for row in rows:
        evidence = row
        # The differential summary deliberately stays small. Only its named
        # reproducer supplies the causal prefix needed by closure predicates.
        name = row.get('reproducer')
        if evidence_dir is not None and isinstance(name, str) and Path(name).name == name:
            directory = Path(evidence_dir).resolve()
            path = (directory / name).resolve()
            if path.parent == directory and path.is_file():
                try:
                    saved = json.loads(path.read_text())
                except (OSError, ValueError):
                    saved = None
                binding = ('command_index', 'command_hex', 'reply_hex', 'rule', 'detail', 'mode')
                if isinstance(saved, dict) and all(saved.get(k) == row.get(k) for k in binding):
                    evidence = dict(saved, **row)
        group = next((g for g in groups
            if row.get('rule') == g['rule'] and row.get('detail') == g['detail']
            and row.get('reply_hex') in g['reply_patterns']
            and (PREDICATES[g['match']](evidence) if 'match' in g
                 else row.get('command_hex') == g['command_pattern'])), None)
        # The differential's own targets (fake) are no surface target: they record nothing.
        node = TARGETS.get(target, target)
        recorded = group is not None and (node == 'fn1' or
            (node == 'fn2' and group['primary_class'] == 'spec-ambiguity'))
        result.append(dict(row, disposition='recorded' if recorded else 'new',
                           group=group['group'] if group else None,
                           match=group.get('match') if group else None,
                           primary_class=group['primary_class'] if group else row.get('class', 'unclassified')))
    return result


def serving(family):
    """The one gate, evaluated at execution (also works under unittest discovery)."""
    def decorate(call):
        @functools.wraps(call)
        def wrapped(*args, **kwargs):
            target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
            backend(target)
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


_PORT_CONSTRUCTION = threading.RLock()


def owned_ports(call):
    """Scope native harness port locks to this target's registered cleanups.

    tools.ports deliberately retains each lock until process exit. Live S has
    many fresh nodes per process, so its adapter must release only leases that
    this constructor acquired, after Node.stop_all and client cleanups finish.
    """
    @functools.wraps(call)
    def wrapped(*args, **kwargs):
        with _PORT_CONSTRUCTION:
            return construct(*args, **kwargs)

    def construct(*args, **kwargs):
        from tests import native_harness
        from tools import ports
        case = args[0] if isinstance(args[0], unittest.TestCase) else args[1]
        leases = []
        thread = threading.get_ident()
        original = native_harness.free_port

        def release():
            with ports._lock:
                for port, descriptor in leases:
                    if ports._held.get(port) == descriptor:
                        del ports._held[port]
                        os.close(descriptor)
            leases.clear()

        def acquire():
            port = original()
            if threading.get_ident() == thread:
                with ports._lock:
                    leases.append((port, ports._held[port]))
            return port

        # Register first: LIFO cleanup stops nodes before releasing their ports.
        case.addCleanup(release)
        native_harness.free_port = acquire
        try:
            return call(*args, **kwargs)
        finally:
            native_harness.free_port = original
    return wrapped


class Target:
    """The selected live backend; the model owns expected replies, never this class."""
    @owned_ports
    def __init__(self, case, groups=('surface.test',)):
        import tests.native_harness as native_harness
        image = native_harness.native_image('FN_NATIVE_HOST')
        self.node = native_harness.Node(case, image)
        self.node.init(*groups)
        self.node.start()

    def connect(self):
        return self.node.session(timeout=5)


class SurfaceCase(unittest.TestCase):
    def setUp(self):
        self.evidence = {}

    def native(self, family, name):
        out = output(family) / 'natives'; out.mkdir(exist_ok=True)
        args = argparse.Namespace(out=str(out), backend=backend(), retired_skip=True,
                                  timeout=native_timeout(name), env_plan=os.environ.get('FN2_SURFACE_IMAGES',
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
        if backend() == 'fn2':
            # Against fn2 a native outcome that names a host contract the served node does not provide yet (the
            # Node adapter's requirement, or the placeholder host's refusal of a verb) is owed, never a pass and
            # never a red; any other outcome is judged as on fn1.
            owed = [e for e in data['tests'] if e.get('classification') in ('named-node-dead', 'named-placeholder')]
            self.evidence['owed_host'] = [dict(test=e['test'], requirement=(e['exception'] or '')[:300]) for e in owed]
            data = dict(data, tests=[e for e in data['tests'] if e not in owed])
            if owed and all(e['outcome'] in ('ok', 'skip') for e in data['tests']):
                ran = sum(e['outcome'] == 'ok' for e in data['tests'])
                needs = dict.fromkeys(re.sub(r'^.*?not yet serving: ', '', (e['exception'] or '').splitlines()[0])[:120]
                                      for e in owed)
                self.skipTest(f'fn2 host contract owed ({len(owed)} tests; {ran} ran ok): ' + ' | '.join(list(needs)[:3]))
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
        budget = RUN.get('fuzz_allocations', {}).get(family, box_budget()['fuzz_seconds'])
        margin = min(box_budget()['fuzz_margin_seconds'], budget / 2)
        seconds = budget - margin
        directory = output(family) / 'fuzz'
        if family == 'nntp' and backend() == 'fn2' and not os.environ.get('FN2_SURFACE_FUZZ_NNTP'):
            # The differential's owner is fn1's fuzz Node (fixture groups, a login, posted articles); against the
            # served fn2 profile every command past D3 would be an interim reply, not a judgement.
            raise unittest.SkipTest('nntp F against fn2 owed: the differential needs an fn2 owner with fixture '
                                    'groups and a login (D6, E2); set FN2_SURFACE_FUZZ_NNTP to supply one')
        if family != 'nntp' or os.environ.get('FN2_SURFACE_FUZZ_NNTP'):
            command = hook(family, 'FUZZ', self, seconds=seconds,
                           corpus=FAMILIES[family]['fuzz']['corpus'])
        else:
            command = [sys.executable, '-m', 'fn2.tests.model.differential', '--target',
                       os.environ.get('FN2_SURFACE_TARGET', 'fn2'),
                       '--seeds', f"0..{RUN.get('examples', 200)-1}", '--mode', 'reader,node,peer',
                       '--steps', '50', '--minimize-seconds',
                       str(min(box_budget()['fuzz_minimize_seconds'], margin / 4)),
                       '--out', str(directory)]
        if not isinstance(command, list) or not command or not all(isinstance(s, str) for s in command):
            raise ValueError('fuzz hook must return a nonempty argv list')
        command = list(command)
        if '--seconds' in command:
            command[command.index('--seconds') + 1] = str(seconds)
        else:
            command += ['--seconds', str(seconds)]
        # Each invocation owns fresh artifacts: never adjudicate stale prior output.
        if any((directory / name).exists() for name in ('summary.json', 'differences.jsonl')):
            raise ValueError('fuzz output already contains results; choose a fresh --out directory')
        self.evidence.update(fuzz_report=str(directory), fuzz_budget_seconds=budget,
                             fuzz_driver_seconds=seconds)
        status = driver(command, directory, budget)
        # nntp's F (its differential, or a hook standing in for it) and the wire differential launched by any
        # family's hook (H7: tls_auth and peering run it with a focus) are adjudicated against the ledger;
        # every other driver owns its own oracle and exits 0.
        if family == 'nntp' or command[1:3] == ['-m', 'fn2.tests.model.differential']:
            summary = json.loads((directory / 'summary.json').read_text())
            path = directory / 'differences.jsonl'
            rows = [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []
            judged = adjudicate_differences(rows, os.environ.get('FN2_SURFACE_TARGET', 'fn2'),
                                           evidence_dir=directory)
            self.evidence['differences'] = judged
            self.evidence['recorded_difference_count'] = sum(r['disposition'] == 'recorded' for r in judged)
            self.evidence['new_difference_count'] = sum(r['disposition'] == 'new' for r in judged)
            self.evidence['fuzz_summary'] = summary
            self.assertFalse(summary.get('setup_error') or summary.get('interrupted'), str(summary))
            self.assertEqual(sum(summary.get('mismatches', {}).values()), len(rows),
                             'differential summary and mismatch records disagree')
            self.assertEqual(status, int(bool(rows)), 'wire fuzz driver failed; see driver.log')
            self.assertEqual(self.evidence['new_difference_count'], 0, 'new wire mismatches; see differences evidence')
        else:
            self.assertEqual(status, 0, 'wire fuzz driver failed; see driver.log')

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
    if form == 'S' and info.get('status') == 'implemented':
        return loader.loadTestsFromName(info['module'])
    return loader.loadTestsFromTestCase(cases(info['module'], family, form))


def family_loader(package):
    """Unittest package hook; discovery does not recurse into generated forms."""
    family = package.rsplit('.', 1)[-1]

    def load_tests(loader, tests, pattern):
        return unittest.TestSuite(form_suite(family, form, loader)
                                  for form in ('E', 'S', 'F', 'H', 'R'))

    return load_tests
