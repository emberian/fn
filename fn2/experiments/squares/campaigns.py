#!/usr/bin/env python3
"""Run frozen E1 campaigns, with at most two fresh ACL2 processes at once."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
EXP = ROOT / 'fn2/experiments/squares'
SEEDS = (1, 20261028, 314159265)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--controls-only', action='store_true')
    parser.add_argument('--mutants-only', action='store_true')
    parser.add_argument('--config', choices=('baseline','random','exhaustive'))
    args = parser.parse_args()
    frozen = json.loads((EXP / 'freeze.json').read_text())
    for name, expected in frozen['mutants'].items():
        actual = hashlib.sha256((EXP / 'mutants' / name).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f'freeze mismatch: {name}')
    if shutil.disk_usage(ROOT).free < 60 * 1024**3:
        raise SystemExit('BLOCKED: disk below 60 GiB; no files deleted')
    mutants = ['ORIGINAL'] if args.controls_only else [f'M{i}' for i in range(1, 7)] if args.mutants_only else ['ORIGINAL'] + [f'M{i}' for i in range(1, 7)]
    # Deterministic campaign order; controls are a separate prerequisite batch.
    jobs = [(m, c, seed) for m in mutants for c in ((args.config,) if args.config else ('baseline', 'random', 'exhaustive'))
            for seed in (SEEDS if c != 'exhaustive' else (1,))]
    running = []
    outcomes = []
    while jobs or running:
        while jobs and len(running) < 2:
            if shutil.disk_usage(ROOT).free < 60 * 1024**3:
                print('BLOCKED: disk below 60 GiB; no further campaigns launched', flush=True)
                jobs.clear()
                break
            m, c, seed = jobs.pop(0)
            stem = EXP / 'results' / f'{m}-{c}-{seed}'
            log = open(str(stem) + '.log', 'wb')
            env = dict(os.environ, FN_ACL2_SLOT_DIR='/tmp/fn2-a4-acl2-slots',
                       FN_ACL2_SLOTS='6', E1_MUTANT=m, E1_CONFIG=c, E1_SEED=str(seed))
            with open(EXP / 'driver.lsp', 'rb') as driver:
                process = subprocess.Popen(['timeout', '-k', '5', '600', 'tools/acl2'], cwd=ROOT,
                                           env=env, stdin=driver, stdout=log, stderr=subprocess.STDOUT,
                                           start_new_session=True)
            Path(str(stem) + '.pid').write_text(str(process.pid) + '\n')
            running.append((process, log, str(stem), time.monotonic()))
            print(f'E1 START {m} {c} {seed} pid={process.pid}', flush=True)
        for item in list(running):
            process, log, stem, start = item
            code = process.poll()
            if code is not None:
                log.close()
                elapsed = time.monotonic() - start
                record = dict(stem=stem, exit=code, process_seconds=elapsed)
                outcomes.append(record)
                print('E1 PROCESS ' + json.dumps(record, sort_keys=True), flush=True)
                running.remove(item)
        if running:
            time.sleep(0.5)
    (EXP / 'results' / (('control-processes' if args.controls_only else 'mutant-processes') + ('-' + args.config if args.config else '') + '.json')).write_text(json.dumps(outcomes, indent=2) + '\n')
    if any(x['exit'] != 0 for x in outcomes):
        raise SystemExit(1)

if __name__ == '__main__':
    main()
