#!/usr/bin/env python3
"""Execute explicit sprint drivers through tools/acl2 and reject false exit-zero runs."""
from pathlib import Path
import argparse
import json
import os
import subprocess
import sys
sys.dont_write_bytecode = True
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'tools'))
import triage


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('drivers', nargs='+', help='explicit .lsp paths relative to repository')
    parser.add_argument('--timeout', type=int, default=300)
    args = parser.parse_args()
    evidence = ROOT / 'fn2/sprint/evidence'
    evidence.mkdir(exist_ok=True)
    results = []
    for name in args.drivers:
        driver = (ROOT / name).resolve()
        driver.relative_to(ROOT / 'fn2/sprint/tests')
        if driver.suffix != '.lsp':
            parser.error(f'not a driver: {driver}')
        target = evidence / f'{driver.stem}.out'
        started = time.monotonic()
        env = dict(os.environ)
        env.pop('FN_ACL2_SLOT_DIR', None)
        with driver.open('rb') as source, target.open('wb') as output:
            process = subprocess.run(
                [str(ROOT / 'fn2/sprint/acl2-readonly-slot.py'), '--timeout', str(args.timeout)],
                cwd=ROOT, stdin=source, stdout=output, stderr=subprocess.STDOUT, env=env,
                timeout=args.timeout + 30)
        transcript = target.read_text(errors='replace')
        errors = triage.acl2_errors(transcript)
        marker = f'SPRINT-EXAMPLE-PASS {driver.stem}'
        # Look for the standalone emitted marker, not its echoed source form.
        marker_seen = any(line.strip().endswith(marker) and '(cw' not in line.lower()
                          for line in transcript.splitlines())
        passed = process.returncode == 0 and not errors and marker_seen
        row = {'driver': name, 'exit': process.returncode, 'seconds': round(time.monotonic()-started, 3),
               'pass_marker': marker_seen, 'acl2_errors': len(errors), 'passed': passed,
               'transcript': str(target.relative_to(ROOT))}
        results.append(row)
        print(json.dumps(row), flush=True)
        for error in errors[:2]:
            print(error.text(), flush=True)
    (evidence / 'examples.json').write_text(json.dumps(results, indent=2)+'\n')
    return 0 if all(row['passed'] for row in results) else 1

if __name__ == '__main__':
    sys.exit(main())
