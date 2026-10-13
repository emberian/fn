#!/usr/bin/env python3.12
"""Full native control at dev: list modules, launch detached, and diff its reds."""
from __future__ import annotations

import argparse
import ast
import fcntl
import json
import math
from pathlib import Path
import re
import shlex
import subprocess
import sys
import time
from types import SimpleNamespace
import uuid

if __package__:
    from . import train
    from .known_reds import commit_sha
else:
    import train
    from known_reds import commit_sha

ROOT = Path(__file__).resolve().parents[1]
RESULT_PREFIX = 'FN_TEST_BUDGET_RESULT '


def rules_modules(text: str) -> set[str]:
    """Read the tuple declarations at the run's SHA without executing that tree."""
    assignments = {target.id: node.value for node in ast.parse(text).body
                   if isinstance(node, ast.Assign) for target in node.targets
                   if isinstance(target, ast.Name)}

    def value(node):
        if isinstance(node, ast.Name):
            return value(assignments[node.id])
        if isinstance(node, (ast.Tuple, ast.List)):
            return tuple(value(element) for element in node.elts)
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            return value(node.left) + value(node.right)
        raise train.TrainError('unsupported IMAGE_RULES declaration')

    try:
        return {module for _, _, modules in value(assignments['IMAGE_RULES']) for module in modules}
    except (KeyError, TypeError, ValueError, RecursionError) as error:
        raise train.TrainError(f'cannot read IMAGE_RULES: {error}') from error


def modules(root: Path, sha: str | None = None) -> list[str]:
    if sha is None:
        files = [path.relative_to(root).as_posix() for path in (root / 'tests').glob('test_native_*.py')]
        declared = {module for _, _, names in train.IMAGE_RULES for module in names}
    else:
        files = train.git(root, 'ls-tree', '-r', '--name-only', sha, '--', 'tests').stdout.splitlines()
        declared = rules_modules(train.git(root, 'show', sha + ':tools/train.py').stdout)
    native = {path[:-3].replace('/', '.') for path in files
              if re.fullmatch(r'tests/test_native_[^/]*\.py', path)}
    return sorted(native | declared)


def read_record(path: Path) -> dict:
    return dict(line.split('=', 1) for line in path.read_text(encoding='utf-8').splitlines() if '=' in line)


def fetched_dev(root: Path) -> str:
    ref = 'refs/dev-control/' + uuid.uuid4().hex + '/dev'
    try:
        train.git(root, 'fetch', '--no-tags', '--no-write-fetch-head', '--refmap=', 'origin',
                  '+refs/heads/dev:' + ref)
        return train.git(root, 'rev-parse', ref).stdout.strip()
    finally:
        train.git(root, 'update-ref', '-d', ref)


def existing_run(root: Path, sha: str) -> Path | None:
    for path in sorted((root / 'build/hbox-native').glob('devctl-*.run')):
        if path.name == f'devctl-{sha[:12]}.run':
            return path
        record = read_record(path)
        source = record.get('tree') or record.get('source', '')
        if re.fullmatch(r'[0-9a-fA-F]{4,40}', source):
            if commit_sha(root, source) == sha:
                return path
    return None


def box_load(root: Path, box: str) -> float:
    result = subprocess.run(['timeout', '60', 'sh', 'tools/boxes.sh'], cwd=root,
                            capture_output=True, text=True, timeout=65)
    if result.returncode:
        raise train.TrainError(f'box load probe failed (rc {result.returncode}): {result.stderr.strip()}')
    for line in result.stdout.splitlines():
        match = re.match(r'^' + re.escape(box) + r'\s+load\s+([0-9.]+)\s+on\s', line)
        if match:
            load = float(match[1])
            if math.isfinite(load) and load >= 0:
                return load
    raise train.TrainError(f'no load reading for {box} (unreachable or malformed probe)')


def launch(root: Path, box: str, requested: str | None) -> str:
    sha = commit_sha(root, requested) if requested else fetched_dev(root)
    label = 'devctl-' + sha[:12]
    directory = root / 'build/hbox-native'
    directory.mkdir(parents=True, exist_ok=True)
    # Serialize control launches here; the native runner owns its separate label lock
    # and remote PID file, so this wrapper never invents a process-stop mechanism.
    with (directory / '.dev-control-launch.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        previous = existing_run(root, sha)
        if previous:
            raise train.TrainError(f'devctl run already recorded for {sha}: {previous}')
        load = box_load(root, box)
        if load >= 24:
            raise train.TrainError(f'{box} load {load:g} is not under 24; launch refused')
        argv = ['timeout', '600', 'sh', 'tools/hbox_native.sh', '--box', box, '--label', label,
                '--allow-skips', '--detach', sha, *modules(root, sha)]
        result = subprocess.run(argv, cwd=root, capture_output=True, text=True, timeout=605)
        if result.returncode:
            raise train.TrainError(f'native launch failed (rc {result.returncode}): '
                                   + (result.stdout + result.stderr).strip())
    return label


def run_identity(root: Path, record: dict) -> tuple[str, str | None]:
    """Train's image-source/tree check, applied to the run's tree rather than HEAD."""
    sha = commit_sha(root, record.get('tree') or record.get('source', ''))
    source = commit_sha(root, record.get('source', ''))
    if source != sha:
        changed = train.git(root, 'diff', '--name-only', source, sha).stdout.splitlines()
        inputs = train.image_inputs_changed(changed)
        if inputs:
            raise train.TrainError(f'run images are of {source}, tree {sha} changes image input {inputs[0]}')
    if not record.get('box') or not record.get('dir'):
        raise train.TrainError('run record lacks box or dir')
    return sha, source if source != sha else None


def result_details(text: str) -> dict:
    """Keep executed counts and skip reasons from the same train-reader output."""
    details = {}
    for line in text.splitlines():
        if line.startswith(RESULT_PREFIX):
            try:
                record = json.loads(line[len(RESULT_PREFIX):])
                if isinstance(record, dict) and isinstance(record.get('module'), str):
                    details[record['module']] = record
            except ValueError:
                pass  # train's parser also ignores non-JSON result lines
    return details


def classify(expected: list[str], results: dict, details: dict, rows: list[dict],
             box: str, directory: str) -> dict:
    known = {row['subject'] for row in rows if row['kind'] == 'native'}
    new, retire, not_run = [], [], []
    for module in sorted(set(expected) | set(results)):
        log = box + ':' + directory.rstrip('/') + '/logs/test-' + module + '.log'
        def entry(subject, **fields):
            return dict(subject=subject, module=module, log=log, **fields)
        detail = details.get(module, {})
        reasons = dict(detail.get('skips') or [])
        if module not in results:
            carried = '; '.join(f'{case}: {why}' for case, why in reasons.items()) or detail.get('load_error')
            reason = 'missing module result' + (': ' + carried if carried else '')
            not_run.append(entry(module, reason=reason))
            continue
        result = results[module]
        rc, cases = result['rc'], result['cases']
        skipped = [case for case, status in cases.items() if status == 'skip']
        if not cases or rc == train.IMAGE_RC_ALL_SKIPPED or detail.get('executed') == 0:
            reason = '; '.join(f'{case}: {why}' for case, why in reasons.items())
            reason = reason or detail.get('load_error') or ('module skipped' if rc == train.IMAGE_RC_ALL_SKIPPED
                                                          else 'no test executed')
            not_run.append(entry(module, reason=reason, rc=rc))
        else:
            for case in sorted(skipped):
                not_run.append(entry(case, reason=reasons.get(case, 'skipped (no reason recorded)')))
        reds = [case for case, status in cases.items() if status not in train.IMAGE_CASE_PASS]
        for case in sorted(reds):
            if case not in known:
                new.append(entry(case, status=cases[case]))
        # A failed module without a red case is still a red: includes build refusal,
        # node death before a case, and module-level errors absent from case records.
        if rc not in (0, train.IMAGE_RC_ALL_SKIPPED) and not reds:
            new.append(entry(module, rc=rc, reason='module failed without a red case'))
        for case, status in sorted(cases.items()):
            if case in known and status == 'ok':
                retire.append(entry(case))
    return {'new': new, 'retire': retire, 'not_run': not_run}


def diff(root: Path, label: str) -> dict:
    if not re.fullmatch(r'[A-Za-z0-9_.-]+', label) or label in ('.', '..'):
        raise train.TrainError('invalid run label')
    record = read_record(train.image_record_path(SimpleNamespace(root=root), label))
    sha, images_from = run_identity(root, record)
    rows = train.known_reds_at(SimpleNamespace(root=root), sha)
    if rows is None:
        raise train.TrainError(f'no known-red baseline at run SHA {sha}')
    script = 'test -d ' + shlex.quote(record['dir']) + ' && { ' + train.image_read_script(record['dir']) + '; }'
    result = subprocess.run(['timeout', '60', 'ssh', '-n', record['box'], script],
                            capture_output=True, text=True, timeout=65)
    if result.returncode:
        raise train.TrainError(f'reading {record["box"]}:{record["dir"]} failed (rc {result.returncode}): {result.stderr.strip()}')
    outcome = classify(modules(root, sha), train.parse_image_results(result.stdout),
                       result_details(result.stdout), rows, record['box'], record['dir'])
    report = dict(label=label, sha=sha, recorded_at=time.time(), box=record['box'],
                  directory=record['dir'], images_from=images_from, **outcome)
    destination = root / 'build/dev-control' / (label + '.json')
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = destination.with_suffix('.tmp')
    temporary.write_text(json.dumps(report, indent=1, ensure_ascii=False) + '\n', encoding='utf-8')
    temporary.replace(destination)
    for title, key in [('NEW reds', 'new'), ('RETIRE candidates', 'retire'), ('NOT RUN', 'not_run')]:
        print(f'{title}: {len(report[key])}')
        for entry in report[key]:
            line = f'RED {entry["subject"]} {entry["log"]}' if key == 'new' else f'{entry["subject"]} {entry["log"]}'
            if entry.get('reason'):
                line += ' — ' + entry['reason']
            print('  ' + line)
    return report


def status_line(root: Path) -> str:
    paths = list((root / 'build/dev-control').glob('*.json'))
    if not paths:
        return 'dev control: none recorded'
    newest = max(paths, key=lambda path: (path.stat().st_mtime, path.name))
    try:
        report = json.loads(newest.read_text(encoding='utf-8'))
        age = max(0, (time.time() - float(report['recorded_at'])) / 3600)
        return f'dev control: {report["sha"]} age {age:.1f} hours NEW {len(report["new"])}'
    except (OSError, ValueError, KeyError, TypeError) as error:
        return f'dev control: invalid record {newest.name}: {error}'


def main(argv=None, *, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    commands.add_parser('modules')
    launch_parser = commands.add_parser('launch')
    launch_parser.add_argument('--box', default='hbox')
    launch_parser.add_argument('--sha')
    diff_parser = commands.add_parser('diff')
    diff_parser.add_argument('label')
    args = parser.parse_args(argv)
    try:
        if args.command == 'modules':
            print('\n'.join(modules(root)))
        elif args.command == 'launch':
            print(launch(root, args.box, args.sha))
        else:
            return 1 if diff(root, args.label)['new'] else 0
        return 0
    except (train.TrainError, OSError, ValueError, SyntaxError, subprocess.TimeoutExpired) as error:
        print(f'dev_control: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
