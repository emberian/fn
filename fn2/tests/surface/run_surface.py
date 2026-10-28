"""Run selected surface families and publish outcomes beside their profile."""
import argparse
from collections import Counter
import importlib
import json
import os
from pathlib import Path
import sys
import unittest

from fn2.tests.harness import run_natives
from . import FAMILIES, MANIFEST, ROOT, RUN


class Result(run_natives.Result):
    def stopTest(self, test):
        super().stopTest(test)
        for entry in self.records:
            if entry['test'] == test.id():
                evidence = getattr(test, 'evidence', {})
                entry['evidence'] = evidence
                # Native assertion calls occurred in another process; count once.
                entry['assertions'] += evidence.get('native', {}).get('assertions', 0)


def totals(records):
    outcomes = Counter(r['outcome'] for r in records)
    return dict(tests=len(records), ok=outcomes['ok'],
                fail=sum(outcomes[k] for k in ('fail', 'error', 'unexpected-success')),
                skip=outcomes['skip'],
                skips=dict(Counter(r['skip_reason'] for r in records if r['outcome'] == 'skip')),
                executed_assertions=sum(r['assertions'] for r in records))


def markdown(family, result):
    def cell(value):
        return str(value).replace('|', '\\|').replace('\n', ' ')
    lines = [f'# {family}', '',
             '| form | tests | ok | fail/error | skip (by reason) | executed assertions |',
             '|---|---:|---:|---:|---|---:|']
    for form, row in result['forms'].items():
        skipped = '; '.join(f'{n} × {reason}' for reason, n in row['skips'].items())
        label = form + ('' if row['selected'] else ' (' + row['selection_reason'] + ')')
        lines.append('| ' + ' | '.join(map(cell, [label, row['tests'], row['ok'], row['fail'],
                                                skipped or '0', row['executed_assertions']])) + ' |')
    lines += ['', '## published, not a gate', '',
              '| row | value | unit | profile | status / reason |', '|---|---|---|---|---|']
    for row in result['performance']:
        lines.append('| ' + ' | '.join(cell(row.get(k, '—'))
                     for k in ('row', 'value', 'unit', 'profile', 'status')) + ' |')
    return '\n'.join(lines) + '\n'


def run_family(family, box):
    entry = FAMILIES[family]
    selected = entry['cadence'][box]['forms']
    reports, performance = {}, []
    for form in ('E', 'S', 'F', 'H', 'R', 'P'):
        info = entry['forms'][form]
        records = []
        if form in selected:
            suite = unittest.defaultTestLoader.loadTestsFromName(info['module'])
            result = Result()
            with run_natives.count_assertions(result):
                suite.run(result)
            records = result.records
        reason = '' if form in selected else ('§2.2 dash' if not info['applicable'] else
                 'simulator driver' if form == 'P' else 'hbox nightly only')
        reports[form] = dict(selected=form in selected, selection_reason=reason,
                             **totals(records), records=records)
        if form == 'R':
            # Match by index, preserving a row even when no number is available.
            for index, name in enumerate(entry['performance_rows']):
                record = next((r for r in records if f'.test_row_{index}_' in r['test']), None)
                value = record.get('evidence', {}).get('performance', {}) if record else {}
                status = (record['skip_reason'] or record['exception'] or record['outcome']) if record else reason
                performance.append(dict(row=name, **{k: v for k, v in value.items() if k != 'row'}, status=status))
    return dict(carried_natives=entry['carried_natives'], forms=reports, performance=performance,
                **totals([r for f in reports.values() for r in f['records']]))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    select = parser.add_mutually_exclusive_group()
    select.add_argument('--family', help='comma-separated families; hyphen aliases accepted')
    select.add_argument('--all', action='store_true')
    parser.add_argument('--box', choices=('laptop', 'hbox'), default='laptop')
    parser.add_argument('--target', choices=('fn1', 'fn2'), default=os.environ.get('FN2_SURFACE_TARGET', 'fn2'))
    parser.add_argument('--out', type=Path, default=Path('build/surface'))
    parser.add_argument('--pid-file', type=Path)
    args = parser.parse_args(argv)
    families = list(dict.fromkeys(f.strip().replace('-', '_') for f in args.family.split(','))) if args.family else list(FAMILIES)
    if any(f not in FAMILIES for f in families):
        parser.error('unknown family; choose ' + ','.join(FAMILIES))
    if args.target not in ('fn1', 'fn2'):
        parser.error('FN2_SURFACE_TARGET must be fn1 or fn2')
    args.out = args.out.resolve(); args.out.mkdir(parents=True, exist_ok=True)
    pidfile = args.pid_file or args.out / 'surface.pid'
    pidfile.parent.mkdir(parents=True, exist_ok=True)
    with pidfile.open('x') as pid:
        pid.write(str(os.getpid()) + '\n')
    old_target = os.environ.get('FN2_SURFACE_TARGET')
    os.environ['FN2_SURFACE_TARGET'] = args.target
    budget = MANIFEST['budget'][args.box]
    RUN.clear()
    RUN.update(out=args.out, examples=budget['model_examples'], fuzz_remaining=budget['fuzz_seconds'])
    report = dict(schema_version=1, target=args.target, box=args.box, profile=os.environ.get('FN2_SURFACE_PROFILE',
                  'harness fixture profile; each measurement must name its own'), budget=budget,
                  assertion_metric='TestCase assert*/fail* calls (including delegation), plus native subprocess counts; excludes Python assert and external driver internals',
                  families={}, errors=[])
    try:
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
            print(f"{family}: tests={result['tests']} ok={result['ok']} fail={result['fail']} skip={result['skip']} assertions={result['executed_assertions']}", flush=True)
    except Exception as error:
        report['errors'].append(f'{type(error).__name__}: {error}')
    finally:
        report['fuzz_seconds_remaining'] = RUN['fuzz_remaining']
        report['totals'] = totals([r for family in report['families'].values()
                                  for form in family['forms'].values() for r in form['records']])
        run_natives.write_json(args.out / 'surface.json', report)
        if old_target is None:
            os.environ.pop('FN2_SURFACE_TARGET', None)
        else:
            os.environ['FN2_SURFACE_TARGET'] = old_target
        pidfile.unlink()
    for error in report['errors']:
        print(error, file=sys.stderr)
    return int(bool(report['errors'] or report['totals']['fail']))


if __name__ == '__main__':
    sys.exit(main())
