#!/usr/bin/env python3
"""Read cert.pl wall times and non-overlapping ACL2 event summaries.

MAKE-EVENT, PROGN, ENCAPSULATE and CERTIFY-BOOK timings include children;
never add them to the primitive-event total. Include-book is reported
separately. The certify-book summary owns total prove/print/other time.
"""
from pathlib import Path
import argparse
import json
import re

ANSI = re.compile(r'\x1b\[[0-9;]*m')
BUILT = re.compile(r'Built \S+?/(books|tests|sim|meta/emit)/(\S+)\.cert \(([\d.]+)s\)')
TIME = re.compile(r'Time:\s+([\d.]+) seconds \(prove: ([\d.]+), print: ([\d.]+), other: ([\d.]+)\)')
PRIMITIVE = {'DEFTHM', 'DEFUN', 'DEFUNS', 'DEFCONST', 'DEFMACRO', 'DEFSTOBJ',
             'VERIFY-GUARDS', 'VERIFY-TERMINATION', 'DEFTHEORY', 'TABLE', 'IN-THEORY',
             'DEFATTACH', 'DEFEQUIV', 'DEFCONG', 'DEFLABEL'}


def book_metrics(path):
    source = path.read_text(errors='replace')
    events, includes, total = [], [], None
    for block in re.split(r'^Summary\s*$', source, flags=re.M)[1:]:
        form = re.search(r'Form:\s*\(\s*([^\s()]+)\s+([^\s()]+)', block)
        time = TIME.search(block)
        if not form or not time:
            continue
        kind, name = form.groups()
        times = dict(zip(('total_s', 'prove_s', 'print_s', 'other_s'), map(float, time.groups())))
        event = dict(kind=kind, name=name, **times)
        if kind == 'CERTIFY-BOOK':
            total = times
        elif kind == 'INCLUDE-BOOK':
            includes.append(event)
        elif kind in PRIMITIVE:
            events.append(event)
    return dict(certify=total, primitive_event_count=len(events),
                primitive_event_time_s=round(sum(e['total_s'] for e in events), 3),
                include_time_s=round(sum(e['total_s'] for e in includes), 3),
                max_event=max(events, key=lambda e: e['total_s'], default=None),
                slowest=sorted(events, key=lambda e: -e['total_s'])[:15])


def collect(root, log):
    source = ANSI.sub('', log.read_text(errors='replace'))
    built = {f'{directory}/{book}': float(seconds) for directory, book, seconds in BUILT.findall(source)}
    details = {}
    for book, wall in built.items():
        path = root / (book + '.cert.out')
        details[book] = dict(cert_pl_wall_s=wall, **(book_metrics(path) if path.exists() else {}))
    return dict(log=str(log), summary=re.findall(r'certify summary:.*', source),
                built_count=len(built), sum_cert_pl_wall_s=round(sum(built.values()), 3), books=details)


def compare(before, after):
    """Compare identical paths, separating new books from the common closure."""
    common = sorted(before['books'].keys() & after['books'].keys())
    added = sorted(after['books'].keys() - before['books'].keys())
    def totals(run, paths):
        entries = [run['books'][name] for name in paths]
        complete = all('primitive_event_count' in entry for entry in entries)
        maxima = [(name, run['books'][name].get('max_event')) for name in paths]
        maxima = [(name, event) for name, event in maxima if event]
        maximum = max(maxima, key=lambda pair: pair[1]['total_s'], default=None)
        return dict(book_count=len(paths),
                    sum_cert_pl_wall_s=round(sum(e['cert_pl_wall_s'] for e in entries), 3),
                    event_data_complete=complete,
                    primitive_event_count=sum(e['primitive_event_count'] for e in entries) if complete else None,
                    max_primitive_event=dict(book=maximum[0], **maximum[1]) if maximum else None)
    return dict(common_paths=common, before_common=totals(before, common),
                after_common=totals(after, common), added_paths=added,
                after_added=totals(after, added),
                before_only_paths=sorted(before['books'].keys() - after['books'].keys()),
                time_scope='sum of per-book cert.pl wall times, not elapsed run time or CPU time')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('log', type=Path)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--before', type=Path, help='saved baseline JSON; compare matching paths')
    args = parser.parse_args()
    result = collect(args.root, args.log)
    if args.before:
        result['comparison_to_before'] = compare(json.loads(args.before.read_text()), result)
    args.out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'books'}, indent=2))
    if 'books/commit-durable-all' in result['books']:
        print(json.dumps(result['books']['books/commit-durable-all'], indent=2))
