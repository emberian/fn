#!/usr/bin/env python3
"""Summarize E1 evidence only; no simulator decisions are implemented here."""
import collections
import json
import re
from pathlib import Path

EXP = Path(__file__).resolve().parent
ROOT = EXP.parents[2]
SEEDS = (1, 20261028, 314159265)

def read_sexp(path):
    text = path.read_text()
    text = re.sub(r'#A\(\(\d+\) BASE-CHAR \. ("(?:\\.|[^"\\])*")\)', r'\1', text)
    tokens = re.findall(r'"(?:\\.|[^"\\])*"|[()]|[^\s()]+', text)
    pos = 0
    def read():
        nonlocal pos
        token = tokens[pos]; pos += 1
        if token == '(':
            result = []
            while tokens[pos] != ')': result.append(read())
            pos += 1
            return result
        if token.startswith('"'): return json.loads(token)
        if token == 'NIL': return None
        try: return int(token)
        except ValueError: pass
        try: return float(token.replace('d', 'e').replace('D', 'E'))
        except ValueError: return token
    result = read()
    assert pos == len(tokens), (path, pos, len(tokens))
    return result

def plist(value): return dict(zip((value or [])[::2], (value or [])[1::2]))
def label(value): return '(' + ' '.join(map(str, value)) + ')'
def load_reports():
    reports = []
    for mutant in ['ORIGINAL'] + [f'M{i}' for i in range(1, 7)]:
        for config in ('baseline', 'random', 'exhaustive'):
            for seed in SEEDS if config != 'exhaustive' else (1,):
                path = EXP / 'results' / f'{mutant}-{config}-{seed}.sexp'
                if not path.exists(): continue
                r = plist(read_sexp(path))
                r[':COUNTERS'] = plist(r[':COUNTERS'])
                r[':LABELS'] = {label(x[0]): x[-1] for x in r[':LABELS'] or []}
                r['path'] = str(path.relative_to(EXP))
                r['boundary'] = plist(r[':RESULT'][2:]).get(':BOUNDARY')
                r['status'], r['contract'] = r[':RESULT'][:2]
                r['hit'] = r['status'] == ':FOUND' and r['contract'] != ':BASELINE-LIVENESS'
                reports.append(r)
    return reports

def catalogue():
    text = (ROOT / 'fn2/books/machines-a.lisp').read_text().upper()
    labels = []
    for machine, body in re.findall(r'\(DEFMACHINE (\S+)\s+(.*?)(?=\(DEFMACHINE|\Z)', text, re.S):
        phases = re.search(r':STATES \((.*?)\)', body).group(1).split()
        obs = re.search(r':OBSERVES \((.*?)\)\s+:CONTINUATIONS', body, re.S).group(1)
        labels += [label([':RUN', machine, phase]) for phase in phases]
        labels += [label([':OBSERVE', machine, event]) for event in re.findall(r'\((:\S+) ', obs)]
    labels += ['(:ROUTER :FALLBACK)', '(:EXECUTOR :CLOCK)', '(:EXECUTOR :SIGNAL)']
    labels += [f'(:EXECUTOR :SERVICE {i})' for i in range(4)] + ['(:EXECUTOR :EMPTY-PRINCIPAL)']
    assert len(labels) == 39
    return labels

def main():
    reports = load_reports()
    (EXP / 'results/campaigns.json').write_text(json.dumps(reports, indent=2) + '\n')
    lines = ['# E1 complete campaign ledger', '', 'C/R are direct core/reference transitions; PC/PR are replayed core/reference transitions. G1/TRACE copies are counted, not subtracted. Trials are whole baseline runs, random choice-list runs, or enumerated prefixes. A liveness stop is an ORIGINAL finding, not a mutation hit. All seconds exclude loading.', '', '| Mutation | Configuration | Seed | Result / contract | Seconds | Trials | C / R / PC / PR | G1 / G2 | Boundary | Evidence |', '|---|---|---:|---|---:|---:|---|---|---:|---|']
    reach = ['', '## Reachability counters', '', 'Endpoints include duplicates and replay work. G1 counts include preflight/replayed transitions. Zero G2 means unexercised; rejected candidates are occurrence alternatives, not distinct states.', '', '| Mutation | Config | Seed | States reached | Prefixes enumerated | G1 | G2 | Rejected candidates | Illegal residual | Rejected prefixes | Non-earliest land selections |', '|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
    for r in reports:
        c = r[':COUNTERS']; path = r['path']
        finding = r['status'].removeprefix(':').lower() + '/' + r['contract'].removeprefix(':').lower()
        transitions = ' / '.join(str(c.get(k, 0)) for k in (':CORE', ':REFERENCE', ':REPLAYED-CORE', ':REPLAYED-REFERENCE'))
        evidence = path.replace('.sexp', '-schedule.sexp') if r['status'] == ':FOUND' else path
        lines.append(f"| {r[':MUTANT']} | {r[':CONFIG']} | {r[':SEED']} | {finding} | {r[':SECONDS']:.6f} | {r[':TRIALS']} | {transitions} | {c.get(':G1',0)} / {c.get(':G2',0)} | {r['boundary'] or '—'} | [record]({evidence}) |")
        reach.append('| ' + ' | '.join(map(str, [r[':MUTANT'], r[':CONFIG'], r[':SEED']] + [c.get(k, 0) for k in (':STATES-REACHED', ':PREFIXES-ENUMERATED', ':G1', ':G2', ':REJECTED-CANDIDATES', ':ILLEGAL-RESIDUAL', ':REJECTED-PREFIXES', ':NON-EARLIEST')])) + ' |')
    (EXP / 'CAMPAIGNS.md').write_text('\n'.join(lines + reach) + '\n')
    coverage = ['| G1 label | ORIGINAL random (3 seeds) | ORIGINAL exhaustive | All mutant campaigns |', '|---|---:|---:|---:|']
    for name in catalogue():
        counts = [sum(r[':LABELS'].get(name, 0) for r in reports if predicate(r)) for predicate in (
            lambda r: r[':MUTANT'] == 'ORIGINAL' and r[':CONFIG'] == 'random',
            lambda r: r[':MUTANT'] == 'ORIGINAL' and r[':CONFIG'] == 'exhaustive',
            lambda r: r[':MUTANT'] != 'ORIGINAL')]
        coverage.append('| `' + name.lower() + '` | ' + ' | '.join(str(n) if n else 'unexercised' for n in counts) + ' |')
    (EXP / 'results/coverage.md').write_text('\n'.join(coverage) + '\n')
    for r in reports:
        print(r[':MUTANT'], r[':CONFIG'], r[':SEED'], r['status'], r['contract'], f"{r[':SECONDS']:.6f}", r[':TRIALS'])
    print('REPORTS', len(reports))

if __name__ == '__main__': main()
