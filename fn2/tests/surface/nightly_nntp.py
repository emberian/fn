"""H's nightly row: the nntp family against fn2 under each carrier, summarized for main's morning read.

    python -m fn2.tests.surface.nightly_nntp OUT SHA     (OUT holds sim/ and native/, each a run_surface --out)

Writes OUT/table.md (per target: per-form status and every test's outcome) and OUT/summary.txt, one line:
the served surface (fn2_conn_interim.json at the tree under test: the verbs served, the interim rows left by
owner, BRICKS-20261031 section 3's burndown), then served / interim / WIRE opened-judged-unjudged /
disagreements per target, and NOT RUN rows grouped by owner.
"""
import collections
import json
import re
import sys
from pathlib import Path

# Who a NOT RUN reason waits on: the first pattern that matches the skip reason.
OWNERS = [
    (r'CONFIG init|no groups until D6', 'D6 (groups at init)'),
    (r'store STORE init|store needs', 'B/D (store init)'),
    (r'FNCT control socket', 'E1 (control socket)'),
    (r'--fn (model|store)\b', 'D (developer verbs)'),
    (r'never announced its listener', 'D (placeholder host start)'),
    (r'differential needs an fn2 owner', 'H (fn2 owner for the differential; D6, E2)'),
    (r'fixture driver owed|history driver owed', 'H (driver hook)'),
    (r'FN_RUN_|FIXTURES|hbox: ', 'opt-in / box fixtures'),
    (r'not yet serving', 'D/E (family not serving)'),
]


def owner(reason):
    return next((who for pattern, who in OWNERS if re.search(pattern, reason)), 'unassigned: ' + reason[:60])


def target_report(directory):
    report = json.loads((directory / 'surface.json').read_text())
    family = report['families'].get('nntp')
    s, rows, waits = None, [], collections.Counter()
    for form, row in (family or {}).get('forms', {}).items():
        for record in row['records']:
            name = record['test'].rsplit('.', 1)[-1]
            reason = record.get('skip_reason') or ''
            evidence = record.get('evidence', {})
            rows.append((form, name, record['outcome'], (record.get('exception') or reason).splitlines()[0][:160]
                         if (record.get('exception') or reason) else ''))
            if record['outcome'] == 'skip':
                for need in [o['requirement'] for o in evidence.get('owed_host', [])] or [reason]:
                    waits[owner(need)] += 1
            if form == 'S':
                served = evidence.get('served_checked') or {}
                owed = evidence.get('owed_interim') or {}
                wire = evidence.get('wire') or {}
                s = dict(outcome=record['outcome'], served=sum(served.values()),
                         interim=sum(v['replies'] for v in owed.values()),
                         interim_by_quest={q: sum(v['replies'] for v in owed.values() if v['quest'] == q)
                                           for q in {v['quest'] for v in owed.values()}},
                         wire=(wire.get('opened'), wire.get('judged'), wire.get('unjudged'), len(wire.get('refused') or {})),
                         disagreements=0 if record['outcome'] == 'ok' else 'see s-failure.json',
                         detail=(record.get('exception') or '').splitlines()[-1][:200] if record.get('exception') else '')
    return dict(target=report['target'], exit=report['exit_status'], errors=report['errors'],
                status={f: r['status'] for f, r in (family or {}).get('forms', {}).items()}, s=s, rows=rows,
                waits=waits)


def line(r):
    s = r['s'] or {}
    wire = s.get('wire') or (None,) * 4
    quests = ','.join(f'{q} {n}' for q, n in sorted((s.get('interim_by_quest') or {}).items()))
    head = (f"{r['target']}: S {s.get('outcome', 'absent')} served {s.get('served')} interim {s.get('interim')} ({quests}) "
            f"WIRE {wire[0]} opened/{wire[1]} judged/{wire[2]} unjudged/{wire[3]} refused, "
            f"disagreements {s.get('disagreements')}; exit {r['exit']}")
    return head + ('; ' + s['detail'] if s.get('detail') else '') + ('; errors ' + '; '.join(r['errors']) if r['errors'] else '')


def surface():
    """What serves at this tree: D's interim table, read where the S form reads it."""
    table = json.loads((Path(__file__).resolve().parent / 'fn2_conn_interim.json').read_text())
    left = collections.Counter(row['quest'] for row in table['interim'].values())
    return (f"serves {len(table['served_verbs'])} verbs ({' '.join(table['served_verbs'])}); "
            f"{sum(left.values())} interim rows left: " + ', '.join(f'{q} {n}' for q, n in sorted(left.items())))


def main(out, sha):
    out = Path(out)
    reports = [target_report(out / name) for name in ('sim', 'native') if (out / name / 'surface.json').exists()]
    waits = collections.Counter()
    for r in reports:
        waits += r['waits']
    table = [f'# H nightly {out.name} (dev {sha})', '', surface(), '']
    for r in reports:
        table += [f"## --target {r['target']} (exit {r['exit']})", '', line(r), '',
                  '| form | test | outcome | reason |', '|---|---|---|---|']
        table += [f'| {f} | {n} | {o} | {why} |' for f, n, o, why in r['rows']]
        table += ['', 'NOT RUN by owner: ' + ', '.join(f'{w} {n}' for w, n in r['waits'].most_common()), '']
    (out / 'table.md').write_text('\n'.join(table) + '\n')
    summary = (f'H nightly {out.name} {sha}: {surface()} | ' + ' | '.join(line(r) for r in reports) +
               ' | NOT RUN by owner (both targets): ' + ', '.join(f'{w} {n}' for w, n in waits.most_common()))
    (out / 'summary.txt').write_text(summary + '\n')
    print(summary)


if __name__ == '__main__':
    main(*sys.argv[1:3])
