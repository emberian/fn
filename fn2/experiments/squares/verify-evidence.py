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
# Pass 2 deliberately changes the experiment reports and adds a new driver.
changed=subprocess.check_output(['git','diff','--name-only'],cwd=s.ROOT,text=True).splitlines()
assert all(x.startswith(('fn2/experiments/squares/','build/')) for x in changed)
for doc in p.glob('*.md'):
    for dest in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
        if not dest.startswith(('https:','http:','#')):
            assert (doc.parent/dest.split('#')[0]).exists(), (doc,dest)
print('E1 AUDIT: 49 final campaign records; 49 exit-zero processes; six frozen hashes match; all saved failures present; all six selected random replays reproduce exact failure detail; 39-label accounting reconciles; source edits confined to the experiment/build fence; document links resolve.')

# The second pass has a separate evidence namespace. Do not silently include
# development attempts, replays, or supplied-prefix construction in its matrix.
import importlib.util
spec=importlib.util.spec_from_file_location('e2_summary',p/'pass2/summarize.py')
e2=importlib.util.module_from_spec(spec);spec.loader.exec_module(e2)
all2=e2.load_reports();rs2=e2.measured(all2)
assert len(rs2)==100
source_record=json.loads((e2.P/'final-source-hashes.json').read_text())
assert source_record['kind']=='postmeasurement-source-record'
for name,digest in source_record['files'].items():
    assert hashlib.sha256((p/name).read_bytes()).hexdigest()==digest,name
frozen_runner=json.loads((e2.P/'measurement-freeze.json').read_text())['files']['runner.lsp']
assert hashlib.sha256((e2.P/'development-runner-before-invalid-fix.lsp').read_bytes()).hexdigest()==frozen_runner
processes={}
for phase in ('controls','main','local','data','retry'):
    for r in json.loads((e2.P/'results'/f'{phase}-processes.json').read_text()):
        processes[r['stem'].split('/')[-1]]=r
assert len(processes)==100 and all(x['exit']==0 for x in processes.values())
assert set(processes)=={r['path'].split('/')[-1][:-5] for r in rs2}
controls={r[':SEED']:r for r in rs2 if r[':CONFIG']=='baseline' and r[':MUTANT']=='ORIGINAL'}
def signature(result):
    return [result[1],s.plist(result[2:]).get(':BOUNDARY')] if result[0]==':FOUND' else None
for r in rs2:
    assert r['status'] in (':FOUND',':CENSORED'),r['path']
    assert r['total']<=200000
    assert sum(r[':LABELS'].values())==r[':COUNTERS'].get(':G1',0),r['path']
    assert set(r[':LABELS']).issubset(s.catalogue())
    if r['status']==':CENSORED':
        assert r['contract']==':TRANSITIONS' and r['total']==200000
    if r['hit']:
        assert (p/e2.evidence(r)).exists()
        detail=s.plist(r[':RESULT'][2:]);control=s.plist(detail[':ORIGINAL-CONTROL'])
        if r[':CONFIG']=='baseline':
            trial=detail[':TRIAL-SEED']
            expected=next(s.plist(x) for x in controls[r[':SEED']][':BASELINE-TRIALS'] if s.plist(x)[':TRIAL-SEED']==trial)
            assert control==expected
            assert control[':SIGNATURE']!=signature(r[':RESULT'])
            assert control[':COMPLETE'] or max(0,control[':LAST-BOUNDARY']-1)>=r['boundary']
        else:
            cr=control[':RESULT'];assert cr[0] in (':COMPLETED',':FOUND')
            assert signature(cr)!=signature(r[':RESULT'])
            if r[':MUTANT']=='M1':assert cr==[':COMPLETED',':ORIGINAL-DECLARATION-REJECTS-PAIR']
    if r[':CONFIG']=='baseline' and r[':MUTANT']!='ORIGINAL':
        for raw in r[':KNOWN-ORIGINAL'] or []:
            known=s.plist(raw);a=s.plist(known[':CANDIDATE']);b=s.plist(known[':CONTROL'])
            assert a[':TRIAL-SEED']==b[':TRIAL-SEED'] and a[':SIGNATURE']==b[':SIGNATURE']
    hs=r[':HORIZONS']
    if r[':CONFIG'] in ('iterative','dedup'):
        assert [h[':DEPTH'] for h in hs]==list(range(len(hs)))
        assert all(h[':COMPLETE'] for h in hs[:-1]) and not hs[-1][':COMPLETE']
        assert r[':DEEPEST-COMPLETED']==len(hs)-2
        assert sum(h[':PREFIXES'] for h in hs)==r[':TRIALS']
        assert sum(h[':STATES'] for h in hs)==e2.count(r,':STATES-REACHED')
        if r[':CONFIG']=='iterative':assert all(h[':DUPLICATES']==0 for h in hs)
    else:assert not hs
    assert e2.count(r,':G2-POSITIVE-WITH-BYTES')<=e2.count(r,':G2-POSITIVE')<=e2.count(r,':G2')
    if e2.count(r,':G2-POSITIVE'):
        positive=s.plist(r[':FIRST-POSITIVE']);ab=positive[':AB'];ba=positive[':BA']
        assert ab[0]==ba[0]==':LEGAL' and ab[1]==ba[1]
        assert ab[1][0]==':E1-CLIENT-OWN-STOP-V1'
        a,b=positive[':A'],positive[':B'];assert a[1]!=b[1] and a[5:7]!=b[5:7]
        if r[':DECLARATION']=='data':
            assert a[4] in (2,3) and b[4] in (2,3)
            assert a[3] in (1,2,3) and b[3] in (1,2,3)
    else:assert not r[':FIRST-POSITIVE']
replay_processes=json.loads((e2.P/'results/replay-processes.json').read_text())
assert len(replay_processes)==11 and all(x['exit']==0 for x in replay_processes)
for r in all2:
    if r[':CONFIG'] not in ('replay','positive-replay'):continue
    if r[':CONFIG']=='positive-replay':
        assert r[':RESULT']==[':COMPLETED',':EXACT-POSITIVE-REPLAY']
    elif r[':MUTANT']=='M1':
        assert r[':RESULT']==[':COMPLETED',':EXACT-DIAMOND-REPLAY']
    else:
        mode='baseline' if r[':PREFIX']=='baseline' else 'random'
        source=next(x for x in rs2 if x[':MUTANT']==r[':MUTANT'] and x[':CONFIG']==mode and x[':PROFILE']=='c1' and x[':PREFIX']=='initial' and x[':SEED']==r[':SEED'])
        assert signature(r[':RESULT'])==signature(source[':RESULT'])
        assert s.plist(r[':RESULT'][2:])[':DETAIL']==s.plist(source[':RESULT'][2:])[':DETAIL']
for doc in list((p/'pass2').glob('*.md'))+[p/'CAMPAIGNS.md',p/'E1-RESULTS.md',p/'NOTES-TO-A.md']:
    for dest in re.findall(r'\]\(([^)]+)\)',doc.read_text()):
        if not dest.startswith(('https:','http:','#')):
            assert (doc.parent/dest.split('#')[0]).exists(),(doc,dest)
positive=sum(e2.count(r,':G2-POSITIVE') for r in rs2 if r[':MUTANT']=='ORIGINAL' and r[':PROFILE']=='c2' and r[':CONFIG']=='random' and r[':PREFIX']=='initial')
print(f'E2 AUDIT: 100 final campaigns; 100 exit-zero processes; 11 exact replays; all hits qualified against ORIGINAL; horizon and 39-label accounting reconcile; {positive} positive ORIGINAL data diamonds from random initialization; frozen mutations and source fences intact; document links resolve.')
