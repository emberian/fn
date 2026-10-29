"""The nightly report: one surface run's surface.json as a per-family table plus every non-ok row.

Usage: python3 -m fn2.tests.surface.nightly OUT [--known FILE] [--title TEXT]

OUT is a run_surface --out directory. FILE (JSON, a list of {"match": a test id's final part(s), e.g. `test_native_owner` (a suffix, or a
component followed by `.`; never a bare substring, so `owner` does not claim `owner_offlock`),
"class": "known fn1 red" | "unprovisioned" | "harness-side" | ..., "note": text}) names rows already
classified; the first matching entry classifies a row, and an unmatched non-ok row prints as
`unclassified`, which is the morning's only reading list (RELEASE-PLAN §2.5: rows are never chased
except reds that name a decision). Performance is published in the report, never a gate.
"""
import argparse
import json
from pathlib import Path


def short(test):
    parts = test.split('.')
    return '.'.join(parts[-3:]) if len(parts) > 3 else test


def first_line(text):
    for line in (text or '').splitlines():
        if line.strip():
            return line.strip()[:200]
    return ''


def classify(test, known):
    for entry in known:
        match = entry['match']
        if test.endswith(match) or match + '.' in test:
            return entry['class'], entry.get('note', '')
    return 'unclassified', ''


def report(out, known=(), title=None):
    data = json.loads((Path(out) / 'surface.json').read_text())
    totals = data['totals']
    rows = [f"# {title or 'Surface run'}: target {data['target']}, box {data['box']}", '',
            f"exit status {data['exit_status']}; {totals['tests']} tests, {totals['executed']} executed, "
            f"{totals['ok']} ok, {totals['fail']} not ok, {totals['skip']} skipped ({totals['not_run']} NOT RUN); "
            f"TestCase-call count {totals['testcase_calls']}.", '']
    for error in data.get('errors', ()):
        rows.append(f'Run error: {error}')
    rows += ['| family | status | tests | executed | ok | not ok | skip | NOT RUN | E | S | F | H | R |',
             '|---|---|---|---|---|---|---|---|---|---|---|---|---|']
    failures = []
    for family, result in data['families'].items():
        forms = result['forms']
        cells = []
        for form in ('E', 'S', 'F', 'H', 'R'):
            entry = forms.get(form, {})
            cells.append(f"{entry.get('status', '-')} {entry.get('ok', 0)}/{entry.get('executed', 0)}"
                         if entry.get('selected') else entry.get('status', '-'))
            for record in entry.get('records', ()):
                if record['outcome'] not in ('ok', 'skip'):
                    failures.append((family, form, record))
        rows.append(f"| {family} | {result['status']} | {result['tests']} | {result['executed']} | {result['ok']} | "
                    f"{result['fail']} | {result['skip']} | {result['not_run']} | " + ' | '.join(cells) + ' |')
    rows += ['', '## Non-ok rows', '']
    if not failures:
        rows.append('None.')
    else:
        rows += ['| family | form | test | outcome | class | first line |', '|---|---|---|---|---|---|']
        for family, form, record in failures:
            cls, note = classify(record['test'], known)
            text = first_line(record.get('exception')) or note
            rows.append(f"| {family} | {form} | {short(record['test'])} | {record['outcome']} | {cls} | "
                        f"{text.replace('|', '/')} |")
    reasons = totals.get('not_run_reasons', {})
    if reasons:
        rows += ['', '## NOT RUN, by reason', '']
        rows += [f'- {count}: {reason}' for reason, count in sorted(reasons.items(), key=lambda x: (-x[1], x[0]))]
    performance = [(family, row) for family, result in data['families'].items() for row in result.get('performance', ())]
    if performance:
        rows += ['', '## Performance rows (published, never a gate)', '']
        rows += [f"- {family}: {row['row']}: {row.get('status')}" for family, row in performance]
    return '\n'.join(rows) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('out', type=Path)
    parser.add_argument('--known', type=Path)
    parser.add_argument('--title')
    args = parser.parse_args(argv)
    known = json.loads(args.known.read_text()) if args.known else []
    print(report(args.out, known, args.title), end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
