"""Isolated native modules, measured assertions, explicit skips and startup failures."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import functools
import importlib
import inspect
import json
import os
from pathlib import Path
import re
import shlex
import signal
import subprocess
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parents[3]
PREFIX = 'node dead: fn2 layer D not yet serving'


def inventory():
    return json.loads(Path(__file__).with_name('natives-inventory.json').read_text())['modules']


def flatten(suite):
    for test in suite:
        if isinstance(test, unittest.TestSuite):
            yield from flatten(test)
        else:
            yield test


@contextmanager
def count_assertions(result):
    """Count calls, including delegation between assert* / fail* methods.

    Restore originals even on interruption. Python assert statements and
    custom assertion helpers which do not call TestCase are outside this metric.
    """
    originals = {name: value for name, value in vars(unittest.TestCase).items()
                 if name.startswith(('assert', 'fail')) and inspect.isfunction(value)}
    def wrap(call):
        @functools.wraps(call)
        def counted(*args, **kwargs):
            result.assertions += 1
            return call(*args, **kwargs)
        return counted
    try:
        for name, call in originals.items():
            setattr(unittest.TestCase, name, wrap(call))
        yield
    finally:
        for name, call in originals.items():
            setattr(unittest.TestCase, name, call)


def row(test_id, outcome, *, exception='', reason='', duration=0, assertions=0, **extra):
    return dict(test=test_id, outcome=outcome, exception=exception, skip_reason=reason,
                duration=duration, assertions=assertions,
                intended_skip=outcome == 'skip' and reason.startswith('retired (inventory):'),
                **extra)


def first_line(error):
    return str(error[1]).split('\n', 1)[0]


class Result(unittest.TestResult):
    def __init__(self):
        super().__init__()
        self.records = []
        self.assertions = 0
        self.active = None
        self.started = 0
        self.before = 0

    def startTest(self, test):
        super().startTest(test)
        self.active = test.id()
        self.started, self.before = time.monotonic(), self.assertions
        os.environ['FN2_TEST_ID'] = test.id()

    def record(self, test, outcome, **fields):
        active = self.active == test.id()
        entry = row(test.id(), outcome, duration=time.monotonic() - self.started if active else 0,
                    assertions=self.assertions - self.before if active else 0, **fields)
        # A test can fail in a subtest and again during cleanup. Keep all
        # diagnostics, count its assertions/duration once in stopTest.
        prior = next((r for r in self.records if r['test'] == test.id()), None)
        if prior:
            prior.setdefault('additional', []).append(entry)
            if outcome == 'error':
                prior.update(outcome=outcome, exception=fields.get('exception', ''))
        else:
            self.records.append(entry)

    def stopTest(self, test):
        for entry in self.records:
            if entry['test'] == test.id():
                entry.update(duration=time.monotonic() - self.started,
                             assertions=self.assertions - self.before)
        super().stopTest(test)
        self.active = None
        os.environ.pop('FN2_TEST_ID', None)

    def addSuccess(self, test):
        super().addSuccess(test)
        self.record(test, 'ok')

    def addFailure(self, test, err):
        super().addFailure(test, err)
        self.record(test, 'fail', exception=first_line(err))

    def addError(self, test, err):
        super().addError(test, err)
        self.record(test, 'error', exception=first_line(err))

    def addSkip(self, test, reason):
        super().addSkip(test, reason)
        self.record(test, 'skip', reason=reason)

    def addExpectedFailure(self, test, err):
        super().addExpectedFailure(test, err)
        self.record(test, 'expected-failure', exception=first_line(err))

    def addUnexpectedSuccess(self, test):
        super().addUnexpectedSuccess(test)
        self.record(test, 'unexpected-success')

    def addSubTest(self, test, subtest, err):
        super().addSubTest(test, subtest, err)
        if err is not None:
            outcome = 'fail' if issubclass(err[0], test.failureException) else 'error'
            self.record(test, outcome, exception=first_line(err), subtest=str(subtest))


def module_name(name):
    return name if '.' in name else 'tests.test_native_' + name


def run_one(name, backend, retired_skip=False):
    from . import shim
    shim.install(backend)
    module = module_name(name)
    result = Result()
    try:
        loaded = importlib.import_module(module)
        suite = unittest.defaultTestLoader.loadTestsFromModule(loaded)
        tests = list(flatten(suite))
    except Exception:
        result.records.append(row(module, 'error', exception=first_line(sys.exc_info()),
                                  fixture='import'))
        return finish(name, backend, result.records, 0, 0)
    record = next((m for m in inventory() if m['module'] == name), {})
    judgment = record.get('judgment', {})
    retired = set(judgment.get('in_image_tests', []) + judgment.get('internal_only_tests', []))
    reason = 'retired (inventory): {} {}'.format(
        record.get('module_verdict', ''), judgment.get('reason', '').split('. ', 1)[0])
    active = []
    for test in tests:
        short = test.id().removeprefix(module + '.')
        if retired_skip and short in retired:
            result.records.append(row(test.id(), 'skip', reason=reason))
        else:
            active.append(test)
    # Removing retired tests before running avoids obsolete setUpClass probes.
    # Unittest's class/module fixture grouping remains unchanged for active tests.
    with count_assertions(result):
        unittest.TestSuite(active).run(result)
    seen = {r['test'] for r in result.records}
    fixtures = [r for r in result.records if r['test'] not in {t.id() for t in tests}]
    for test in active:
        if test.id() in seen:
            continue
        class_name = test.__class__.__module__ + '.' + test.__class__.__qualname__
        fixture = next((r for r in fixtures if r['test'] in (
            f'setUpClass ({class_name})', f'setUpModule ({module})')), None)
        if fixture:
            result.records.append(row(test.id(), fixture['outcome'],
                exception=fixture['exception'], reason=fixture['skip_reason'],
                fixture=fixture['test']))
        else:
            result.records.append(row(test.id(), 'error', exception='test did not execute'))
    # Setup events remain separate evidence; their assertions are counted once,
    # never multiplied by the number of tests blocked by that fixture.
    result.records = [r for r in result.records if r not in fixtures]
    for fixture in fixtures:
        if not fixture['test'].startswith(('setUpClass (', 'setUpModule (')):
            result.records.append(fixture)
    return finish(name, backend, result.records, len(tests), result.assertions, fixtures)


def finish(name, backend, records, collected, assertions, fixtures=()):
    for entry in records:
        if backend == 'fn2' and entry['outcome'] != 'ok':
            entry['classification'] = ('named-node-dead' if entry['exception'].startswith(PREFIX)
                                       else 'other')
    outcomes = {r['outcome'] for r in records}
    status = ('any error' if 'error' in outcomes else 'any fail' if
              outcomes & {'fail', 'unexpected-success'} else 'all ok')
    return dict(module=name, backend=backend, status=status, collected=collected,
                assertions=assertions, tests=records, fixtures=list(fixtures),
                fixture_assertions=assertions - sum(r['assertions'] for r in records))


def write_json(path, data):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


def provision(names, args, parent=None):
    """One native_env plan for the selection; no shell evaluation or shared mutation.

    Only the three documented box substitutions expand. An unset tool/fixture
    variable expands to empty, leaving its pre-node prerequisite observable.
    fn2 is a single executable: its bytes supply all three image digests.
    """
    from tools import native_env
    parent = dict(os.environ if parent is None else parent)
    images, identity = getattr(args, 'env_plan', None), getattr(args, 'identity', None)
    source = getattr(args, 'source', None)
    environments = {name: dict(parent, FN2_NODE_BACKEND=args.backend) for name in names}
    if not (images or identity or source):
        return environments
    host = parent.get('FN2_HOST', str(ROOT / 'fn2/host/fn'))
    variables = dict(T=str(ROOT), FN_TEST_OPENSSL_BIN=parent.get('FN_TEST_OPENSSL_BIN', ''),
                     FN_FIXTURES_DIR=parent.get('FN_FIXTURES_DIR', ''))

    def invoke(*words):
        answer = subprocess.run([sys.executable, str(ROOT / 'tools/native_env.py'), *words],
                                cwd=ROOT, env=parent, capture_output=True, text=True,
                                timeout=max(60, 5 * len(names)))
        if answer.stderr:
            print(answer.stderr, end='', file=sys.stderr)
        if answer.returncode:
            raise ValueError(f'native_env {words[0]} exit {answer.returncode}: {answer.stderr.strip()}')
        return answer.stdout

    def assignment(word):
        key, separator, value = word.partition('=')
        if not separator or not re.fullmatch(r'[A-Z][A-Z0-9_]*', key):
            raise ValueError('invalid native_env assignment: ' + word)
        def expand(match):
            name = match[1] or match[2]
            if name not in variables:
                raise ValueError('unknown native_env substitution: ' + name)
            return variables[name]
        return key, re.sub(r'\$\{([A-Za-z_][A-Za-z0-9_]*)\}|\$([A-Za-z_][A-Za-z0-9_]*)',
                           expand, value)

    if images and names:
        modules = {module_name(name): name for name in names}
        plan = invoke('plan', '--allow-skips', '--images', images, *modules)
        seen = set()
        for line in plan.splitlines():
            module, *words = shlex.split(line)
            if module not in modules or module in seen:
                raise ValueError('unexpected/duplicate native_env module: ' + module)
            seen.add(module)
            env = environments[modules[module]]
            for key in native_env.IMAGES.keys() | native_env.FIXED.keys():
                env.pop(key, None)
            for word in words:
                key, value = assignment(word)
                env[key] = host if args.backend == 'fn2' and key in native_env.IMAGES else value
        if seen != modules.keys():
            raise ValueError('native_env omitted selected modules')
    values = {}
    if args.backend == 'fn2':
        path = Path(host)
        digest = native_env.sha256_file(path) if path.is_file() else 'fn2-host-absent'
        values = dict.fromkeys(native_env.IDENTITY, digest)
        if path.is_file() and source:
            values['FN_NATIVE_IMAGE_SOURCE_SHA'] = source
    elif identity:
        for line in invoke('identity', '--image', identity, '--source', source, '--export').splitlines():
            words = shlex.split(line)
            if len(words) != 2 or words[0] != 'export':
                raise ValueError('invalid native_env identity output')
            key, value = assignment(words[1])
            values[key] = value
        if values.keys() != native_env.IDENTITY.keys():
            raise ValueError('native_env identity must provide all four identity variables')
    for env in environments.values():
        env.update(values)
    return environments


def child(name, args):
    out = Path(args.out)
    target = out / (name + '.json')
    command = [sys.executable, '-m', 'fn2.tests.harness.run_natives', '--one', name,
               '--backend', args.backend, '--out', str(out)]
    if args.retired_skip:
        command.append('--retired-skip')
    env = getattr(args, 'module_envs', {}).get(name, dict(os.environ, FN2_NODE_BACKEND=args.backend))
    pidfile = out / (name + '.pid')
    started = time.monotonic()
    with pidfile.open('x') as pid_output, (out / (name + '.log')).open('wb') as log:
        target.unlink(missing_ok=True)
        try:
            process = subprocess.Popen(command, cwd=ROOT, env=env, stdout=log, stderr=log,
                                       start_new_session=True)
        except BaseException:
            pidfile.unlink()
            raise
        pid_output.write(str(process.pid) + '\n')
        pid_output.flush()
        try:
            process.wait(timeout=args.timeout)
            if process.returncode in (0, 1) and target.exists():
                data = json.loads(target.read_text())
            else:
                data = finish(name, args.backend, [row(module_name(name), 'error',
                    exception=f'child exit {process.returncode}; see {name}.log')], 0, 0)
        except subprocess.TimeoutExpired:
            # The group leader is our unreaped child, recorded in our PID file.
            # Kill its whole session group, including any inherited node children.
            os.killpg(int(pidfile.read_text()), signal.SIGKILL)
            process.wait(timeout=10)
            data = dict(module=name, backend=args.backend, status='timeout',
                        collected=0, assertions=0, tests=[], fixtures=[])
        finally:
            if process.poll() is None:
                os.killpg(int(pidfile.read_text()), signal.SIGKILL)
                process.wait(timeout=10)
            pidfile.unlink()
    data.update(pid=process.pid, duration=time.monotonic() - started,
                child_exit=process.returncode)
    write_json(target, data)
    return data


def summarize(results):
    tests = [dict(module=m['module'], **r) for m in results for r in m['tests']]
    summary = dict(modules=dict(Counter(m['status'] for m in results)),
                   tests=dict(Counter(r['outcome'] for r in tests)),
                   executed_assertions=sum(m['assertions'] for m in results),
                   intended_skips=sum(r['intended_skip'] for r in tests),
                   skips=dict(Counter(r['skip_reason'] for r in tests if r['outcome'] == 'skip')),
                   classifications=dict(Counter(r['classification'] for r in tests
                                                if 'classification' in r)),
                   other=[r for r in tests if r.get('classification') == 'other'
                          and not r['intended_skip']],
                   module_results=[m['module'] for m in results])
    print('Modules | count')
    for key in ('all ok', 'any fail', 'any error', 'timeout'):
        print(f"{key} | {summary['modules'].get(key, 0)}")
    print('Tests | count')
    for key in ('ok', 'fail', 'error', 'skip', 'expected-failure', 'unexpected-success'):
        print(f"{key} | {summary['tests'].get(key, 0)}")
    print(f"Executed assertions | {summary['executed_assertions']}")
    print(f"Intended retired skips | {summary['intended_skips']}")
    print('Skips by reason | count')
    for reason, count in sorted(summary['skips'].items()):
        print(f'{reason} | {count}')
    print('fn2 non-ok classification (includes intended skips) | count')
    for classification, count in sorted(summary['classifications'].items()):
        print(f'{classification} | {count}')
    print('Other outcomes (excluding intended retired skips) | test | first exception / skip reason')
    for r in summary['other']:
        print(f"{r['module']} | {r['test']} | {r['exception'] or r['skip_reason']}")
    return summary


def forbid_raw_sbcl(event, args):
    """The H1b laptop run is explicitly forbidden to start SBCL.

    Modules bypassing the Node adapter must fail before subprocess exec,
    not silently skip or accidentally qualify against a system runtime.
    """
    if event == 'subprocess.Popen' and Path(os.fsdecode(args[0])).name == 'sbcl':
        raise RuntimeError('H1b laptop rule: raw SBCL execution is forbidden; '
                           'this module bypasses the Node adapter')


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--backend', choices=('fn1', 'fn2'),
                        default=os.environ.get('FN2_NODE_BACKEND', 'fn1'))
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument('--modules')
    selection.add_argument('--all', action='store_true')
    selection.add_argument('--one', help=argparse.SUPPRESS)
    parser.add_argument('--verdict')
    parser.add_argument('--jobs', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=300)
    parser.add_argument('--out', default='build/natives')
    parser.add_argument('--pid-file')
    parser.add_argument('--retired-skip', action='store_true')
    parser.add_argument('--env-plan', metavar='IMAGES')
    parser.add_argument('--identity', metavar='IMAGE')
    parser.add_argument('--source', metavar='SHA')
    args = parser.parse_args(argv)
    if args.jobs < 1 or args.timeout <= 0:
        parser.error('jobs and timeout must be positive')
    if bool(args.identity) != bool(args.source):
        parser.error('--identity and --source must be supplied together')
    out = Path(args.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    args.out = str(out)
    pidfile = Path(args.pid_file) if args.pid_file else None
    if pidfile:
        pidfile.parent.mkdir(parents=True, exist_ok=True)
        with pidfile.open('x') as output:
            output.write(str(os.getpid()) + '\n')
    try:
        if args.one:
            environment = provision([args.one], args)[args.one]
            os.environ.clear()
            os.environ.update(environment)
            if args.backend == 'fn2':
                sys.addaudithook(forbid_raw_sbcl)
            result = run_one(args.one, args.backend, args.retired_skip)
            write_json(out / (args.one + '.json'), result)
            return int(result['status'] != 'all ok')
        entries = inventory()
        names = args.modules.split(',') if args.modules else [m['module'] for m in entries]
        known = {m['module']: m for m in entries}
        if any(n not in known for n in names):
            parser.error('modules must be names from natives-inventory.json')
        if args.verdict:
            if args.verdict not in {m['module_verdict'] for m in entries}:
                parser.error('unknown inventory verdict')
            names = [n for n in names if known[n]['module_verdict'] == args.verdict]
        names = list(dict.fromkeys(names))
        args.module_envs = provision(names, args)
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            results = list(pool.map(lambda name: child(name, args), names))
        summary = summarize(results)
        write_json(out / 'summary.json', summary)
        return int(any(m['status'] != 'all ok' for m in results))
    finally:
        if pidfile:
            pidfile.unlink()


if __name__ == '__main__':
    sys.exit(main())
