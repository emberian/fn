"""Run selected surface families: failure is 1, missing execution is 3 (NOT RUN)."""
import argparse
from collections import Counter
import os
import json
import time
from pathlib import Path
import re
import sys
import unittest

from fn2.tests.harness import run_natives, shim
from fn2.tests.surface.live_evidence import json_value
from . import FAMILIES, MANIFEST, RUN, TARGETS, backend, form_suite, fuzz_allocations, driver, native_timeout


def intended_skip(record, module=None):
    """Use the native runner's retirement inventory and intended-skips registry."""
    if record['outcome'] != 'skip':
        return False
    if any(row['outcome'] == 'skip' and not intended_skip(row, module)
           for row in record.get('additional', [])):
        return False
    if module is None:
        match = re.search(r'(?:^|[.(])test_native_([a-zA-Z0-9_]+)(?=[.)]|$)', record['test'])
        module = match[1] if match else None
    if not module:
        return False
    reason = record['skip_reason']
    if run_natives.intended_category(module, reason):
        return True
    if not reason.startswith('retired (inventory):'):
        return False
    inventory = next((entry for entry in run_natives.inventory() if entry['module'] == module), {})
    judgment = inventory.get('judgment', {})
    retired = judgment.get('in_image_tests', []) + judgment.get('internal_only_tests', [])
    return any(record['test'].endswith('.' + name) for name in retired)


class Result(run_natives.Result):
    def addSkip(self, test, reason):
        # A skipped subtest with successful siblings is one incomplete selected
        # TestCase, not a separate selected test for each subtest diagnostic.
        unittest.TestResult.addSkip(self, test, reason)
        parent = getattr(test, 'test_case', test)
        self.record(parent, 'skip', reason=reason,
                    **({'subtest': str(test)} if parent is not test else {}))

    def record(self, test, outcome, **fields):
        prior = next((row for row in self.records if row['test'] == test.id()), None)
        super().record(test, outcome, **fields)
        # A skipped subtest followed by a failure is still a failure.
        if prior and outcome in ('fail', 'unexpected-success') and prior['outcome'] != 'error':
            prior.update(outcome=outcome, exception=fields.get('exception', ''))
        for entry in self.records:
            if entry['test'] == test.id():
                entry['intended_skip'] = intended_skip(entry)

    def stopTest(self, test):
        super().stopTest(test)
        for entry in self.records:
            if entry['test'] == test.id():
                evidence = getattr(test, 'evidence', {})
                # Evidence is data on disk: a model's records (dataclasses, sets, bytes) become JSON values.
                entry['evidence'] = json_value(evidence)
                native = evidence.get('native', {})
                # Native TestCase calls occurred in another process; count once.
                entry['assertions'] += native.get('assertions', 0)
                skipped = [row for row in native.get('tests', []) if row['outcome'] == 'skip']
                entry['intended_skip'] = (all(intended_skip(row, native['module']) for row in skipped)
                    if skipped and entry['outcome'] == 'skip' else intended_skip(entry))
                if skipped and entry['outcome'] == 'skip' and not entry['intended_skip']:
                    entry['skip_reason'] = next(row['skip_reason'] for row in skipped
                        if not intended_skip(row, native['module']))


def execute_suite(suite):
    """Keep one outcome per selected TestCase, including failed setup fixtures."""
    selected = list(run_natives.flatten(suite))
    result = Result()
    with run_natives.count_assertions(result):
        suite.run(result)
    records = {row['test']: row for row in result.records}
    fixtures = []
    for name, fixture in list(records.items()):
        if not name.startswith(('setUpClass (', 'setUpModule (', 'tearDownClass (', 'tearDownModule (')):
            continue
        fixtures.append(fixture)
        del records[name]
        for index, test in enumerate(test for test in selected if name in (
                f'setUpClass ({test.__class__.__module__}.{test.__class__.__qualname__})',
                f'tearDownClass ({test.__class__.__module__}.{test.__class__.__qualname__})',
                f'setUpModule ({test.__class__.__module__})',
                f'tearDownModule ({test.__class__.__module__})')):
            entry = records.get(test.id())
            calls = fixture['assertions'] if index == 0 else 0
            if entry is None:
                entry = dict(fixture, test=test.id(), fixture=name, assertions=calls)
                entry['executed'] = False
                records[test.id()] = entry
            else:
                entry.setdefault('additional', []).append(dict(fixture, assertions=0))
                entry['assertions'] += calls
                if fixture['outcome'] == 'error' or entry['outcome'] == 'ok':
                    entry.update(outcome=fixture['outcome'], exception=fixture['exception'],
                                 skip_reason=fixture['skip_reason'], fixture=name)
            entry['intended_skip'] = intended_skip(entry)
    for test in selected:
        if test.id() not in records:
            records[test.id()] = run_natives.row(test.id(), 'error', exception='test did not execute')
            records[test.id()]['executed'] = False
    return list(records.values()), fixtures


def test_timeout(family, form, test_id):
    """Outer supervisors leave time for the nested native/fuzz supervisor."""
    if form == 'F':
        return RUN.get('fuzz_allocations', {}).get(family, 0) + 30
    if form == 'E' and '.test_native_' in test_id:
        return native_timeout(test_id.rsplit('.test_native_', 1)[1]) + 30
    box = RUN.get('box', 'laptop')
    if form == 'S' and 's_timeout' in FAMILIES[family]['cadence'][box]:
        return FAMILIES[family]['cadence'][box]['s_timeout']
    return MANIFEST['budget'][box]['native_timeout']


def child_test(family, form, test):
    """Run one selected TestCase, preserving its actual outcome and evidence."""
    name = re.sub('[^a-zA-Z0-9_.-]', '_', test.id())
    directory = Path(RUN['out']) / family / 'children' / form / name
    directory.mkdir(parents=True, exist_ok=True)
    config = directory / 'request.json'
    result_file = directory / 'result.json'
    if config.exists() or result_file.exists():
        raise ValueError('surface child output already exists; choose a fresh --out directory')
    run_natives.write_json(config, dict(family=family, form=form, test=test.id(),
        target=os.environ.get('FN2_SURFACE_TARGET', 'fn2'),
        run={key: str(value) if isinstance(value, Path) else value for key, value in RUN.items()
             if key != 'native_envs'}))
    native = test.id().rsplit('.test_native_', 1)[-1] if '.test_native_' in test.id() else None
    environment = RUN.get('native_envs', {}).get(native)
    started = time.monotonic()
    try:
        code = driver([sys.executable, '-m', 'fn2.tests.surface.run_surface',
                       '--child-config', str(config)], directory, test_timeout(family, form, test.id()), env=environment)
        if code not in (0, 1) or not result_file.exists():
            raise RuntimeError(f'child exit {code}; see {directory / "driver.log"}')
        data = json.loads(result_file.read_text())
        if [row['test'] for row in data['records']] != [test.id()]:
            raise ValueError('child did not report exactly its selected TestCase')
        return data['records'], data['fixtures']
    except Exception as error:
        # A child resource fault remains this selected test's outcome. Later
        # tests and families still get a fresh interpreter and descriptor table.
        record = run_natives.row(test.id(), 'error', exception=f'{type(error).__name__}: {error}',
                                 duration=time.monotonic() - started)
        record['evidence'] = dict(child_log=str(directory / 'driver.log'))
        failure = Path(RUN['out']) / family / 's-failure.json'
        if form == 'S' and failure.exists():
            record['evidence']['s_failure_path'] = str(failure)
        data = dict(records=[record], fixtures=[])
        run_natives.write_json(result_file, data)
        return data['records'], data['fixtures']


def isolated_suite(family, form, suite):
    records, fixtures = [], []
    for test in run_natives.flatten(suite):
        rows, setup = child_test(family, form, test)
        records.extend(rows)
        fixtures.extend(setup)
    return records, fixtures


def child_main(config):
    request = json.loads(config.read_text())
    RUN.clear()
    RUN.update(request['run'])
    os.environ['FN2_SURFACE_TARGET'] = request['target']
    if '.test_native_' in request['test']:
        name = request['test'].rsplit('.test_native_', 1)[1]
        RUN['native_envs'] = {name: dict(os.environ)}
    try:
        shim.install(backend(request['target']))
        tests = [test for test in run_natives.flatten(form_suite(request['family'], request['form']))
                 if test.id() == request['test']]
        if len(tests) != 1:
            raise ValueError('child could not collect its selected TestCase')
        records, fixtures = execute_suite(unittest.TestSuite(tests))
        data = dict(records=records, fixtures=fixtures)
        run_natives.write_json(config.with_name('result.json'), data)
        return int(bool(totals(records)['fail']))
    finally:
        shim.uninstall()


def totals(records):
    def reasons(record):
        return dict.fromkeys(row['skip_reason'] for row in [record, *record.get('additional', [])]
                             if row['outcome'] == 'skip')

    outcomes = Counter(r['outcome'] for r in records)
    missing = [r for r in records if r['outcome'] == 'skip' and not r.get('intended_skip')]
    return dict(tests=len(records), executed=sum(r.get('executed', r['outcome'] != 'skip') for r in records),
                ok=outcomes['ok'],
                fail=sum(outcomes[k] for k in ('fail', 'error', 'unexpected-success', 'expected-failure')),
                skip=outcomes['skip'], not_run=len(missing),
                not_run_reasons=dict(Counter(reason for r in missing for reason in reasons(r))),
                skips=dict(Counter(reason for r in records if r['outcome'] == 'skip' for reason in reasons(r))),
                testcase_calls=sum(r['assertions'] for r in records))


def status(row):
    return 'FAIL' if row['fail'] else 'NOT RUN' if row['skip'] or not row['executed'] else 'PASS'


def exit_status(report):
    if report['errors'] or report['totals']['fail'] or any(
            family.get('served_empty') for family in report['families'].values()):
        return 1
    return 3 if report['totals']['not_run'] else 0


def markdown(family, result):
    def cell(value):
        return str(value).replace('|', '\\|').replace('\n', ' ')
    lines = [f'# {family}: {result["status"]}', '',
             '| form | status | tests | executed | pass | fail/error | skip (by reason) | TestCase-call count |',
             '|---|---|---:|---:|---:|---:|---|---:|']
    for form, row in result['forms'].items():
        skipped = '; '.join(f'{n} × {reason}' for reason, n in row['skips'].items())
        label = form + ('' if row['selected'] else ' (' + row['selection_reason'] + ')')
        lines.append('| ' + ' | '.join(map(cell, [label, row['status'], row['tests'], row['executed'],
                     row['ok'], row['fail'], skipped or row['selection_reason'] or '0', row['testcase_calls']])) + ' |')
    for form, row in result['forms'].items():
        for record in row['records']:
            evidence = record.get('evidence', {})
            differences = evidence.get('differences', []) + evidence.get('recorded_differences', [])
            if differences or 'recorded_difference_count' in evidence:
                lines += ['', f"{form} differences: recorded={evidence.get('recorded_difference_count', len(differences))}; new={evidence.get('new_difference_count', 0)}",
                          '', '| disposition | group | class | detail |', '|---|---|---|---|']
                for difference in differences:
                    lines.append('| ' + ' | '.join(map(cell, [difference.get('disposition', 'recorded'),
                        difference.get('group', ''), difference.get('primary_class', difference.get('class', '')),
                        difference.get('detail', difference.get('observed_reply', ''))])) + ' |')
    if result['owed_forms']:
        lines += ['', 'Owed forms: ' + '; '.join(f"{row['form']}: {row['model']}" for row in result['owed_forms'])]
    if result['served_empty']:
        lines += ['', 'served family ran nothing']
    lines += ['', '## published, not a gate', '',
              '| row | value | unit | profile | status / reason |', '|---|---|---|---|---|']
    for row in result['performance']:
        lines.append('| ' + ' | '.join(cell(row.get(k, '—'))
                     for k in ('row', 'value', 'unit', 'profile', 'status')) + ' |')
    return '\n'.join(lines) + '\n'


def run_family(family, box):
    entry = FAMILIES[family]
    selected = entry['cadence'][box]['forms']
    reports, performance, owed = {}, [], []
    for form in ('E', 'S', 'F', 'H', 'R', 'P'):
        info = entry['forms'][form]
        records, fixtures = [], []
        is_owed = info.get('status') == 'owed'
        if is_owed:
            owed.append(dict(form=form, model=info['model']))
        if form in selected and not is_owed:
            suite = form_suite(family, form)
            target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
            if form in ('S', 'E', 'F', 'H') and family in MANIFEST['serves'][target]:
                records, fixtures = isolated_suite(family, form, suite)
            else:
                records, fixtures = execute_suite(suite)
        reason = 'owed: ' + info['model'] if is_owed else '' if form in selected else (
                 '§2.2 dash' if not info['applicable'] else
                 'simulator driver' if form == 'P' else 'hbox nightly only')
        row = dict(selected=form in selected and not is_owed, selection_reason=reason,
                   **totals(records), records=records, fixtures=fixtures)
        row['status'] = 'OWED' if is_owed else status(row) if form in selected else 'NOT SELECTED'
        reports[form] = row
        if form == 'R':
            for index, name in enumerate(entry['performance_rows']):
                record = next((r for r in records if f'.test_row_{index}_' in r['test']), None)
                value = record.get('evidence', {}).get('performance', {}) if record else {}
                measured = (('NOT RUN: ' + record['skip_reason']) if record['outcome'] == 'skip' else
                            record['exception'] or record['outcome']) if record else reason
                performance.append(dict(row=name, **{k: v for k, v in value.items() if k != 'row'}, status=measured))
    summary = totals([r for f in reports.values() for r in f['records']])
    target = os.environ.get('FN2_SURFACE_TARGET', 'fn2')
    served_empty = family in MANIFEST['serves'][target] and summary['executed'] == 0
    return dict(carried_natives=entry['carried_natives'], forms=reports, performance=performance,
                owed_forms=owed, served_empty=served_empty,
                status='FAIL' if served_empty else status(summary), **summary)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    select = parser.add_mutually_exclusive_group()
    select.add_argument('--family', help='comma-separated families; hyphen aliases accepted')
    select.add_argument('--all', action='store_true')
    parser.add_argument('--box', choices=('laptop', 'hbox'), default='laptop')
    parser.add_argument('--target', choices=tuple(TARGETS), default=os.environ.get('FN2_SURFACE_TARGET', 'fn2'))
    parser.add_argument('--out', type=Path, default=Path('build/surface'))
    parser.add_argument('--pid-file', type=Path)
    parser.add_argument('--child-config', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args(argv)
    if args.child_config is not None:
        return child_main(args.child_config)
    families = list(dict.fromkeys(f.strip().replace('-', '_') for f in args.family.split(','))) if args.family else list(FAMILIES)
    if any(f not in FAMILIES for f in families):
        parser.error('unknown family; choose ' + ','.join(FAMILIES))
    if args.target not in TARGETS:
        parser.error('FN2_SURFACE_TARGET must be one of ' + ', '.join(TARGETS))
    args.out = args.out.resolve(); args.out.mkdir(parents=True, exist_ok=True)
    pidfile = args.pid_file or args.out / 'surface.pid'
    pidfile.parent.mkdir(parents=True, exist_ok=True)
    with pidfile.open('x') as pid:
        pid.write(str(os.getpid()) + '\n')
    old_target = os.environ.get('FN2_SURFACE_TARGET')
    os.environ['FN2_SURFACE_TARGET'] = args.target
    budget = MANIFEST['budget'][args.box]
    RUN.clear()
    RUN.update(out=args.out, box=args.box, examples=budget['model_examples'],
               fuzz_allocations=fuzz_allocations(families, args.box))
    report = dict(schema_version=2, target=args.target, box=args.box, profile=os.environ.get('FN2_SURFACE_PROFILE',
                  'harness fixture profile; each measurement must name its own'), budget=budget,
                  assertion_metric='TestCase-call count: assert*/fail* calls (including delegation), plus native subprocess counts; excludes Python assert and external driver internals',
                  families={}, errors=[])
    try:
        shim.install(backend(args.target))
        if args.target == 'fn1':
            names = [name for f in families for name in FAMILIES[f]['carried_natives']]
            options = argparse.Namespace(backend='fn1', env_plan=os.environ.get('FN2_SURFACE_IMAGES',
                'developer,production,dtn,dtn-developer,reference,developer-stripped'),
                identity=os.environ.get('FN2_SURFACE_IDENTITY'), source=os.environ.get('FN2_SURFACE_SOURCE'))
            if bool(options.identity) != bool(options.source):
                raise ValueError('FN2_SURFACE_IDENTITY and FN2_SURFACE_SOURCE must be supplied together')
            RUN['native_envs'] = run_natives.provision(names, options)
        for family in families:
            result = run_family(family, args.box)
            report['families'][family] = result
            (args.out / (family + '.md')).write_text(markdown(family, result))
            run_natives.write_json(args.out / 'surface.json', report)
            print(f"{family}: {result['status']} tests={result['tests']} executed={result['executed']} pass={result['ok']} fail={result['fail']} skip={result['skip']} TestCase-call count={result['testcase_calls']}", flush=True)
            if result['served_empty']:
                print(f'{family}: served family ran nothing', flush=True)
            for owed in result['owed_forms']:
                print(f"{family}: OWED {owed['form']}: {owed['model']}", flush=True)
    except Exception as error:
        report['errors'].append(f'{type(error).__name__}: {error}')
    finally:
        shim.uninstall()
        report['fuzz_allocations'] = RUN['fuzz_allocations']
        report['totals'] = totals([r for family in report['families'].values()
                                  for form in family['forms'].values() for r in form['records']])
        report['exit_status'] = exit_status(report)
        run_natives.write_json(args.out / 'surface.json', report)
        if old_target is None:
            os.environ.pop('FN2_SURFACE_TARGET', None)
        else:
            os.environ['FN2_SURFACE_TARGET'] = old_target
        pidfile.unlink()
    for error in report['errors']:
        print(error, file=sys.stderr)
    if report['totals']['not_run']:
        print(f"NOT RUN: {report['totals']['not_run']} selected tests", flush=True)
        for reason, count in report['totals']['not_run_reasons'].items():
            print(f'  {count}: {reason}', flush=True)
    return report['exit_status']


if __name__ == '__main__':
    sys.exit(main())
