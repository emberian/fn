"""Per-image load sweep: plan/install remote queues, or fetch one comparison table.

    python3 -m tools.load.sweep plan --image-dir /box/images/rev --label rev
    python3 -m tools.load.sweep install --image-dir /box/images/rev --label rev --baseline previous
    python3 -m tools.load.sweep table --label rev

Image directories are paths on the boxes, not laptop paths. Plan is offline;
install ships the driver's payload, validates the launchers/TREE_SHA remotely,
and starts bounded detached queues. Labels are immutable: use a new label for
another installation. Table fetches raw results only into temporary directories.
"""
from __future__ import annotations

import argparse
import json
import math
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

from tools.load import driver, result, workloads

PATH = Path(__file__).with_suffix('.json')
LOCK = '/tank/fn/scratch/timing-12-23.lock'
CORES = '12-23'


def safe_name(value):
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', value):
        raise ValueError('unsafe label or queue key: %r' % value)
    return value


def load(path=PATH):
    data = json.loads(Path(path).read_text())
    wl = workloads.load()
    seen = set()
    hbox = []
    for lane in data['lanes']:
        safe_name(lane['name'])
        if lane['box'] not in ('hbox', 'persvati'):
            raise ValueError('unknown box')
        if lane['box'] == 'hbox':
            hbox.append(lane['memory'])
        for cell in lane['cells']:
            safe_name(cell['key'])
            if cell['key'] in seen:
                raise ValueError('duplicate sweep key: ' + cell['key'])
            seen.add(cell['key'])
            resolved = workloads.resolve(cell['cell'], wl)
            if cell.get('runner') != resolved.spec.get('runner'):
                raise ValueError('wrong runner for ' + cell['cell'])
            for store in cell.get('sweep', []):
                workloads.resolve(cell['cell'] + '@' + store, wl)
            if cell.get('image', 'fn-host') not in ('fn-host', 'fn-host-developer'):
                raise ValueError('unknown image')
            if type(cell['timeout']) is not int or cell['timeout'] <= 0:
                raise ValueError('timeout must be positive')
            mem = cell.get('memory', lane['memory'])
            if mem not in ('16G', '24G', '32G') or (lane['box'] == 'hbox' and mem != lane['memory']):
                raise ValueError('cell exceeds its lane memory budget')
    if sorted(hbox) != ['16G', '16G', '32G']:
        raise ValueError('hbox requires exactly two 16G lanes and one 32G lane')
    for key in ('queue_timeout', 'attempts', 'retry_seconds', 'busy_sample_seconds'):
        if type(data[key]) is not int or data[key] <= 0:
            raise ValueError(key + ' must be positive')
    if data['busy_max'] != 4:
        raise ValueError('timing admission requires busy <= 4')
    return data


def run_label(label, cell):
    return safe_name(label) + '-' + cell['key']


def image_path(args, box, cell):
    directory = (args.persvati_image_dir or args.image_dir) if box == 'persvati' else args.image_dir
    return str(Path(directory) / cell.get('image', 'fn-host'))


def cell_command(args, lane, cell):
    box, label = lane['box'], run_label(args.label, cell)
    out = driver.BOX_BASE + '/runs/' + label
    work = (driver.BOX_BASE + '/work-nvme-' + args.label if cell.get('work') == 'nvme'
            else '/dev/shm/fn-sweep-' + args.label) + '/' + cell['key']
    image = image_path(args, box, cell)
    if cell.get('runner') == 'w7_extent':
        return ['python3', '-m', 'tools.load.w7_extent', 'run', '--image', args.label + '=' + image,
                '--readers', ','.join(map(str, cell['readers'])), '--runs', str(cell['runs']),
                '--mode', cell['mode'], '--workdir', work, '--out', out + '/extent.jsonl']
    cmd = ['python3', '-m', 'tools.load.driver', 'run', '--cell', cell['cell'], '--label', label,
           '--out', out, '--box', box, '--repeat', '1', '--image', image, '--work', work]
    if box == 'persvati':
        cmd += ['--cores', CORES]
    if cell.get('arms'):
        cmd += ['--arms', cell['arms']]
    if cell.get('sweep'):
        cmd += ['--sweep', ','.join(cell['sweep'])]
    return cmd


def queue_script(args, lane, data):
    q = shlex.quote
    base = driver.BOX_BASE
    ship = base + '/ship/sweep-' + args.label
    queue = args.label + '-' + lane['name']
    lines = ['#!/bin/bash', 'set -u', 'cd ' + q(ship) + ' || exit 1',
             'B=' + q(base), 'Q=' + q(queue), 'mkdir -p "$B/runs"',
             'run() {', '  local label=$1 mem=$2 seconds=$3 image=$4; shift 4',
             '  local out="$B/runs/$label" rc attempt', '  mkdir -p "$out" || return 1',
             '  for ((attempt=1; attempt<=%d; attempt++)); do' % data['attempts']]
    if lane['box'] == 'persvati':
        # Probe and command execute within the same lock hold. Exit 75 releases
        # both the lock and scope before the queue sleeps and retries.
        inner = ('out=$1; image=$2; shift 2\n'
                 'python3 -m tools.load.sweep probe --out "$out/admission.json" --image "$image"\n'
                 'rc=$?; [ "$rc" -eq 0 ] || exit "$rc"\nexec "$@"')
        lines += ['    # probe calls driver.busy_cores(list(range(12, 24)), 5.0); busy > 4 exits 75',
                  '    systemd-run --user --scope -q -p MemoryMax="$mem" flock ' + q(LOCK) +
                  ' taskset -c ' + CORES + ' bash -c ' + q(inner) +
                  ' "$label" "$out" "$image" timeout "$seconds" "$@" >> "$out/run.log" 2>&1 < /dev/null']
    else:
        lines += ['    SWARM_MEM_MAX="$mem" swarm-build timeout "$seconds" "$@" >> "$out/run.log" 2>&1 < /dev/null']
    lines += ['    rc=$?',
              '    printf "%s attempt=%s rc=%s %s\\n" "$label" "$attempt" "$rc" "$(date -u +%FT%TZ)" >> "$B/runs/$Q.done"',
              '    if [ "$rc" -ne 75 ] || [ ' + shlex.quote(lane['box']) + ' = hbox ]; then',
              '      printf "done rc=%s\\n" "$rc" > "$out/status"', '      return 0', '    fi',
              '    printf "%s attempt=%s busy=%s %s\\n" "$label" "$attempt" "$(cat "$out/admission.json")" "$(date -u +%FT%TZ)" >> "$B/runs/$Q.skips"',
              '    if [ "$attempt" -lt %d ]; then sleep %d; fi' % (data['attempts'], data['retry_seconds']),
              '  done', '  echo "skipped rc=75: busy retry budget exhausted" > "$out/status"', '}', '']
    for cell in lane['cells']:
        lines.append(shlex.join(['run', run_label(args.label, cell), cell.get('memory', lane['memory']),
                                 str(cell['timeout']), image_path(args, lane['box'], cell)] + cell_command(args, lane, cell)))
    return '\n'.join(lines) + '\n'


def prepare_script(args, box):
    directory = str(Path(image_path(args, box, {})).parent)
    q = shlex.quote
    sd = driver.BOX_BASE + '/sweeps/' + args.label
    return ('set -eu\n' + '\n'.join('test -x ' + q(directory + '/' + name)
                                  for name in ('fn-host', 'fn-host-developer')) +
            '\ntest -s ' + q(directory + '/TREE_SHA') + '\nmkdir -p ' + q(driver.BOX_BASE + '/sweeps') +
            '\nmkdir ' + q(sd) + '\n')


def install_script(args, box, data):
    q = shlex.quote
    sd = driver.BOX_BASE + '/sweeps/' + args.label
    lanes = [ln for ln in data['lanes'] if ln['box'] == box]
    manifest = dict(data, label=args.label, baseline=args.baseline, lanes=lanes,
                    boxes=['persvati', 'hbox'] if args.box == 'both' else [args.box])
    lines = ['set -eu', 'cat > ' + q(sd + '/manifest.json') + " <<'FN_SWEEP_MANIFEST'",
             json.dumps(manifest, indent=2), 'FN_SWEEP_MANIFEST']
    for lane in lanes:
        path = sd + '/' + lane['name']
        lines += ['cat > ' + q(path + '.sh') + " <<'FN_SWEEP_QUEUE'",
                  queue_script(args, lane, data).rstrip(), 'FN_SWEEP_QUEUE',
                  'chmod +x ' + q(path + '.sh')]
    # Write all scripts before any starts. No descriptor inherited by a job is
    # connected to ssh, and $! is the exact bounded process launched here.
    for lane in lanes:
        path = sd + '/' + lane['name']
        lines += ['setsid nohup timeout %d %s > %s 2>&1 < /dev/null &' %
                  (data['queue_timeout'], q(path + '.sh'), q(path + '.log')),
                  'echo $! > ' + q(path + '.pid'),
                  'printf "%s: " ' + q(path + '.pid') + '; cat ' + q(path + '.pid')]
    return '\n'.join(lines) + '\n'


def cmd_plan_install(args):
    data = load()
    for box in ('persvati', 'hbox') if args.box == 'both' else (args.box,):
        prepare = prepare_script(args, box)
        script = install_script(args, box, data)
        if args.cmd == 'plan':
            print('# ' + box + ' installation (tree shipped by driver.ship_tree)')
            print(prepare + script)
        else:
            driver.ssh(box, prepare, timeout=30).check_returncode()
            driver.ship_tree(box, driver.BOX_BASE + '/ship/sweep-' + args.label)
            p = driver.ssh(box, script, timeout=30)
            p.check_returncode()
            print(box + ':\n' + p.stdout, end='')
    return 0


def cmd_probe(args):
    data = load()
    busy = driver.busy_cores(list(range(12, 24)), float(data['busy_sample_seconds']))
    target = driver.Target('image', args.image)
    record = {'box': {'name': 'persvati', 'busy_cores_start': busy, 'busy_cores_set': CORES,
                      'pinned': list(range(12, 24)), 'loadavg_start': driver.loadavg()},
              'image': {'path': args.image, 'core_sha256': target.core_sha256, 'tree_sha': target.tree_sha}}
    Path(args.out).write_text(json.dumps(record) + '\n')
    return 0 if busy is not None and math.isfinite(busy) and busy <= data['busy_max'] else 75


def extent_result(raw, admission, spec):
    """Bridge W7's JSONL matrix to bar metrics; partial matrices cannot pass."""
    from tools.load.w7_extent import evaluate_cells
    cr = dict(admission, box=dict(admission.get('box', {})), cell='W7', target='image', rep=1, metrics={}, status='incomplete')
    expected = {(r, i) for r in spec['readers'] for i in range(spec['runs'])}
    actual = {(int(c['cell'].rsplit('/R', 1)[1]), c['run_index']) for c in raw}
    complete = (actual == expected and len(raw) == len(expected) and
                all(c.get('cmd', {}).get('ARTICLE', {}).get('n', 0) >= result.MIN_P99_SAMPLES and
                    c.get('cmd', {}).get('ARTICLE', {}).get('p99_ms', 0) > 0 and
                    not c.get('errors') and c.get('mode') == spec['mode'] for c in raw))
    if not complete:
        cr['not_measured'] = {'*': 'W7 matrix incomplete or has reader errors'}
        return cr
    rows = evaluate_cells(raw)
    if len(rows) != 1:
        return cr
    ev = rows[0]
    cr['status'] = 'complete'
    cr['metrics']['extent.p99_ratio'] = ev.get('ratio_p99_16_over_1')
    hits = [c.get('extent', {}).get('hit_ratio') for c in raw]
    cr['metrics']['extent.hit_non_decreasing'] = (int(ev['hit_non_decreasing'])
                                                if all(h is not None for h in hits) else None)
    for r, vals in ev['R'].items():
        for key in ('p99_worst', 'rate_worst', 'hit_worst', 'preads_per_article_worst', 'wait_ms_worst'):
            cr['metrics']['extent.%s.R%d' % (key, r)] = vals[key]
    box = cr.setdefault('box', {})
    # W7 samples before every member; use the worst member, not merely the
    # initial admission sample before preloading the template.
    starts = [(c.get('quiet_check') or {}).get('mean') for c in raw]
    box['busy_cores_start'] = max(starts) * 12 if all(v is not None for v in starts) else None
    ends = [{int(k): v for k, v in c.get('core_busy_measured', {}).items() if 12 <= int(k) <= 23}
            for c in raw]
    box['busy_cores_end'] = max(sum(v.values()) for v in ends) if all(set(v) == set(range(12, 24)) for v in ends) else None
    box['loadavg_start'] = [max(c['loadavg_start'] for c in raw)]
    box['loadavg_end'] = [max(c['loadavg_end'] for c in raw)]
    return cr


def conditions(cr):
    box, img = cr.get('box') or {}, cr.get('image') or {}
    return ('box=%s; cores=%s; busy=%s/%s; load=%s/%s; core sha=%s; tree=%s; status=%s; target=%s arm=%s rep=%s' %
            (box.get('name', '?'), box.get('busy_cores_set', '?'), box.get('busy_cores_start'),
             box.get('busy_cores_end'), box.get('loadavg_start'), box.get('loadavg_end'),
             img.get('core_sha256', '?'), img.get('tree_sha', '?'), cr.get('status', '?'),
             cr.get('target', '?'), cr.get('arm'), cr.get('rep')))


def time_admissible(cr):
    box = cr.get('box') or {}
    busy = box.get('busy_cores_start')
    return (box.get('name') == 'persvati' and box.get('busy_cores_set') == CORES and
            box.get('pinned') == list(range(12, 24)) and
            isinstance(busy, (int, float)) and math.isfinite(busy) and 0 <= busy <= 4)


def table_rows(records, bars):
    rows = []
    for key, cr in records:
        if cr.get('sub'):
            continue
        applicable = [b for b in bars if b['cell'] == result.cell_head(cr['cell'])]
        # Cells without a published bar still appear, with measured quantities
        # explicitly reported rather than inventing thresholds.
        if not applicable:
            applicable = [{'id': '-', 'quantity': metric, 'cell': result.cell_head(cr['cell']),
                           'source': 'reported only', 'checks': [{'metric': metric, 'cmp': 'report', 'threshold': None}]}
                          for metric in (cr.get('metrics') or {'result': None})]
        for bar in applicable:
            judged = result.judge_cell(cr, [bar])[0]
            checks = judged['checks'] or [{'metric': '(no applicable check)', 'value': None}]
            for check in checks:
                metric = check['metric']
                definition = next((c for c in bar['checks'] if c['metric'] == metric), {})
                timed = definition.get('time', bar.get('time')) or bar.get('latency', False)
                verdict = judged['verdict']
                reason = judged.get('reason')
                if timed and not time_admissible(cr):
                    verdict, reason = 'not judged', 'requires persvati cores 12-23, recorded start busy <= 4'
                elif timed and check.get('reason') and check.get('value') is not None:
                    verdict, reason = 'not judged', check['reason']
                rows.append({'identity': (key, cr['cell'], cr.get('target'), cr.get('arm'), cr.get('rep'), bar['id'], metric),
                             'bar': bar['id'], 'quantity': '%s: %s; %s (%s)' % (key, cr['cell'], bar['quantity'], metric),
                             'value': check['value'], 'verdict': verdict, 'reason': reason,
                             'conditions': conditions(cr)})
    return rows


def render_table(records, baseline=(), bars=None):
    bars = bars if bars is not None else result.load_bars() + load()['w7_bars']
    previous = {r['identity']: r for r in table_rows(baseline, bars)}
    rows = table_rows(records, bars)
    rows.sort(key=lambda r: (r['verdict'] != 'FAIL', r['bar'], r['quantity'], str(r['identity'])))
    lines = ['| bar id | quantity | value | verdict | baseline value | ratio | conditions |',
             '|---|---|---|---|---|---|---|']
    def md(v):
        return str(v).replace('|', '&#124;').replace('\n', ' ')
    for row in rows:
        old = previous.get(row['identity'])
        before = old['value'] if old else None
        value = row['value']
        ratio = (value / before if isinstance(value, (int, float)) and
                 isinstance(before, (int, float)) and before != 0 else None)
        verdict = row['verdict'] + (' (' + row['reason'] + ')' if row['reason'] else '')
        cond = row['conditions'] + ('; baseline: ' + old['conditions'] if old else '')
        lines.append('| ' + ' | '.join(map(md, (row['bar'], row['quantity'], result._fmt(value), verdict,
                                                result._fmt(before), result._fmt(ratio), cond))) + ' |')
    return '\n'.join(lines) + '\n'


def fetch_records(label, box, data):
    records = []
    for lane in data['lanes']:
        if lane['box'] != box:
            continue
        for spec in lane['cells']:
            with tempfile.TemporaryDirectory(prefix='fn-sweep-cell-') as tmp:
                root = Path(tmp)
                try:
                    driver.fetch_run(box, run_label(label, spec), root)
                    if spec.get('runner') == 'w7_extent':
                        admission = json.loads((root / 'admission.json').read_text())
                        raw = [json.loads(line) for line in (root / 'extent.jsonl').read_text().splitlines() if line.strip()]
                        cells = [extent_result(raw, admission, spec)]
                    else:
                        cells = json.loads((root / 'result.json').read_text())['cells']
                    if not cells:
                        raise ValueError('no cell results yet')
                except (OSError, ValueError, KeyError, RuntimeError, subprocess.SubprocessError) as exc:
                    cells = [{'cell': spec['cell'], 'box': {'name': box}, 'status': str(exc), 'metrics': {}}]
                records.extend((spec['key'], cr) for cr in cells)
    return records


def cmd_table(args):
    current, previous, manifests = [], [], []
    # A saved manifest preserves the exact matrix and selected boxes of this
    # installation. A missing manifest is an error, never a silently empty table.
    pending = ['persvati', 'hbox'] if args.box in (None, 'both') else [args.box]
    errors = []
    while pending:
        box = pending.pop(0)
        try:
            with tempfile.TemporaryDirectory(prefix='fn-sweep-manifest-') as tmp:
                driver.fetch_files(box, driver.BOX_BASE + '/sweeps/' + args.label, tmp)
                data = json.loads((Path(tmp) / 'manifest.json').read_text())
        except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as exc:
            if args.box is not None or manifests:
                raise
            errors.append(str(exc))
            continue
        if not manifests and args.box is None:
            # The first available manifest names the selected boxes, including
            # a previously failed box if this was a two-box installation.
            pending = [b for b in data['boxes'] if b != box]
        manifests.append(data)
        current.extend(fetch_records(args.label, box, data))
    if not manifests:
        raise RuntimeError('no sweep manifest found: ' + '; '.join(errors))
    baseline = args.baseline or manifests[0].get('baseline')
    if baseline:
        safe_name(baseline)
        for data in manifests:
            box = data['lanes'][0]['box']
            previous.extend(fetch_records(baseline, box, data))
    print(render_table(current, previous, result.load_bars() + manifests[0]['w7_bars']), end='')
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='cmd', required=True)
    for name in ('plan', 'install', 'table'):
        p = sub.add_parser(name)
        p.add_argument('--label', required=True)
        p.add_argument('--baseline')
        p.add_argument('--box', choices=('persvati', 'hbox', 'both'), default=None if name == 'table' else 'both')
        if name != 'table':
            p.add_argument('--image-dir', required=True, help='image directory on each box')
            p.add_argument('--persvati-image-dir', help='alternate image directory on persvati')
    probe = sub.add_parser('probe', help=argparse.SUPPRESS)
    probe.add_argument('--image', required=True)
    probe.add_argument('--out', required=True)
    args = parser.parse_args(argv)
    try:
        if args.cmd == 'probe':
            return cmd_probe(args)
        safe_name(args.label)
        if args.baseline:
            safe_name(args.baseline)
        return cmd_table(args) if args.cmd == 'table' else cmd_plan_install(args)
    except (ValueError, OSError, RuntimeError, subprocess.SubprocessError) as exc:
        print(str(exc), file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
