#!/usr/bin/env python3
"""Narrow consistency checks on the published E1 evidence, without rerunning ACL2."""
import hashlib
import json
import re
import subprocess
import summarize as s
p=s.EXP
f=json.loads((p/'freeze.json').read_text())
assert all(hashlib.sha256((p/'mutants'/name).read_bytes()).hexdigest()==h for name,h in f['mutants'].items())
rs=s.load_reports();assert len(rs)==49
for r in rs:
    assert sum(r[':LABELS'].values())==r[':COUNTERS'].get(':G1',0)
    assert set(r[':LABELS']).issubset(s.catalogue())
    if r['status']==':FOUND': assert (p/r['path'].replace('.sexp','-schedule.sexp')).exists()
final_processes=[]
for name in ['control-processes.json','mutant-processes.json']:
    final_processes += [r for r in json.loads((p/'results'/name).read_text()) if '-random-' not in r['stem']]
for name in ['control-processes-random.json','mutant-processes-random.json']:
    final_processes += json.loads((p/'results'/name).read_text())
assert len(final_processes)==49 and all(r['exit']==0 for r in final_processes)
for m in range(1,7):
    x=s.plist(s.read_sexp(p/'results'/f'M{m}-replay-1-M{m}-random.sexp'))
    assert x[':RESULT'][0]==':FOUND'
    original=next(r for r in rs if r[':MUTANT']==f'M{m}' and r[':CONFIG']=='random' and r[':SEED']==1)
    assert x[':RESULT'][1]==original['contract']
    assert s.plist(x[':RESULT'][2:])[':DETAIL']==s.plist(original[':RESULT'][2:])[':DETAIL']
for m in [3,5,6]:
    x=s.plist(s.read_sexp(p/'results'/f'ORIGINAL-replay-1-M{m}-random.sexp'))
    assert x[':RESULT']==[':COMPLETED',':REPLAY']
for m in [2,4]:
    x=s.plist(s.read_sexp(p/'results'/f'ORIGINAL-replay-1-M{m}-random-retry.sexp'))
    assert x[':RESULT'][0]==':INVALID-PREFIX'
assert subprocess.run(['git','diff','--quiet'],cwd=s.ROOT).returncode==0
for doc in p.glob('*.md'):
    for dest in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
        if not dest.startswith(('https:','http:','#')):
            assert (doc.parent/dest.split('#')[0]).exists(), (doc,dest)
print('E1 AUDIT: 49 final campaign records; 49 exit-zero processes; six frozen hashes match; all saved failures present; all six selected random replays reproduce exact failure detail; 39-label accounting reconciles; no tracked-source edits; document links resolve.')
