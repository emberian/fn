#!/usr/bin/env python3
"""Pass-2 reporting only; simulator and contract decisions remain in Lisp."""
import importlib.util,json,re
from pathlib import Path
P=Path(__file__).resolve().parent
EXP=P.parent
spec=importlib.util.spec_from_file_location('e1_summary',EXP/'summarize.py');old=importlib.util.module_from_spec(spec);spec.loader.exec_module(old)
read_sexp=old.read_sexp;plist=old.plist
TRAN_KEYS=(':CORE',':REFERENCE',':REPLAYED-CORE',':REPLAYED-REFERENCE',':CONTROL-CORE',':CONTROL-REFERENCE',':CONTROL-REPLAYED-CORE',':CONTROL-REPLAYED-REFERENCE')
def load_reports():
 out=[]
 for path in sorted((P/'results').glob('*.sexp')):
  if path.name.endswith('-schedule.sexp') or path.name.startswith('development-'):continue
  r=plist(read_sexp(path))
  if ':CONFIG' not in r:continue
  r[':COUNTERS']=plist(r[':COUNTERS']);r[':LABELS']={old.label(x[0]):x[-1] for x in r[':LABELS'] or []}
  r[':HORIZONS']=[plist(x) for x in r[':HORIZONS'] or []]
  r['path']=str(path.relative_to(EXP));r['status']=r[':RESULT'][0];r['contract']=r[':RESULT'][1] if len(r[':RESULT'])>1 else None
  r['hit']=r['status']==':FOUND';r['boundary']=plist(r[':RESULT'][2:]).get(':BOUNDARY')
  r['total']=sum(r[':COUNTERS'].get(k,0) for k in TRAN_KEYS)
  out.append(r)
 return out
def measured(rs):return [r for r in rs if r[':CONFIG'] in ('baseline','random','iterative','dedup')]
def count(r,k):return r[':COUNTERS'].get(k,0)
def transitions(r):
 c=r[':COUNTERS'];return '/'.join(map(str,[c.get(k,0) for k in TRAN_KEYS[:4]]+[c.get(':CONTROL-CORE',0)+c.get(':CONTROL-REPLAYED-CORE',0),c.get(':CONTROL-REFERENCE',0)+c.get(':CONTROL-REPLAYED-REFERENCE',0)]))
def evidence(r):return r['path'].replace('.sexp','-schedule.sexp') if r['status'] in (':FOUND',':ORIGINAL-FINDING') else r['path']
def main():
 rs=measured(load_reports());(P/'results/campaigns.json').write_text(json.dumps(rs,indent=2)+'\n')
 lines=['# E1 pass 2 campaign ledger','','Main matrix: c1/default/initial. Supplied listener/send/data rows are local claims, not search from initialization. C2/data rows use a separate two-capability profile. 3b is bounded-retention exact-state deduplication. Times include original counterfactual replay, exclude loading. C/R/PC/PR/OC/OR are direct core/reference, replayed core/reference, and original-counterfactual core/reference totals. All six categories consume the same 200,000-transition budget.','', '| Mutation | Mode | Profile/declaration/start | Seed | Result/contract | Seconds | Trials | C/R/PC/PR/OC/OR | Boundary | Known ORIGINAL | Evidence |','|---|---|---|---:|---|---:|---:|---|---:|---:|---|']
 for r in rs:
  mode=r[':CONFIG'];scope='/'.join(r[k] for k in (':PROFILE',':DECLARATION',':PREFIX'))
  lines.append(f"| {r[':MUTANT']} | {mode} | {scope} | {r[':SEED']} | {r['status']}/{r['contract']} | {r[':SECONDS']:.6f} | {r[':TRIALS']} | {transitions(r)} | {r['boundary'] or '—'} | {count(r,':KNOWN-ORIGINAL-FINDINGS')} | [record]({evidence(r)}) |")
 lines+=['','## Horizon ledger','','Depth is suffix length for supplied-prefix rows. Repeated prefixes at successive horizons count again. A partial horizon stops at failure or censoring.','', '| Mutation | Mode | Profile/declaration/start | Depth | Fully completed | Prefixes attempted | States reached | Exact duplicates |','|---|---|---|---:|---|---:|---:|---:|']
 for r in rs:
  for h in r[':HORIZONS']:
   lines.append(f"| {r[':MUTANT']} | {r[':CONFIG']} | {r[':PROFILE']}/{r[':DECLARATION']}/{r[':PREFIX']} | {h[':DEPTH']} | {'yes' if h[':COMPLETE'] else 'no'} | {h[':PREFIXES']} | {h[':STATES']} | {h[':DUPLICATES']} |")
 lines+=['','## Reachability and G2','','Zero positive G2 is unexercised, not passing. States are visited endpoints including repeats, not distinct states. Baseline endpoint counts are not instrumented.','', '| Mutation | Mode | Profile/declaration/start | Seed | States | Prefixes | G1 | G2 | Positive | Positive with bytes | Refutations | Rejected candidates | Illegal residuals | Unqualified candidates | Cache clears |','|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|']
 for r in rs:
  vals=[r[':MUTANT'],r[':CONFIG'],f"{r[':PROFILE']}/{r[':DECLARATION']}/{r[':PREFIX']}",r[':SEED']]
  vals += [count(r,k) for k in (':STATES-REACHED',':PREFIXES-ENUMERATED',':G1',':G2',':G2-POSITIVE',':G2-POSITIVE-WITH-BYTES',':G2-REFUTATIONS',':REJECTED-CANDIDATES',':ILLEGAL-RESIDUAL',':UNQUALIFIED-CANDIDATES',':DEDUP-CACHE-CLEARS')]
  if r[':CONFIG']=='baseline':vals[4]='—';vals[5]='—'
  lines.append('| '+' | '.join(map(str,vals))+' |')
 lines+=['','## ORIGINAL baseline controls, by actual trial seed','','Completed known failures do not stop the campaign. A partial control authorizes comparison only through its recorded checked boundary.','', '| Campaign seed | Actual trial seed | Completed | First failure signature | Last fully checked boundary |','|---:|---:|---|---|---:|']
 for r in rs:
  if r[':MUTANT']=='ORIGINAL' and r[':CONFIG']=='baseline':
   for raw in r[':BASELINE-TRIALS'] or []:
    t=plist(raw);lines.append(f"| {r[':SEED']} | {t[':TRIAL-SEED']} | {bool(t[':COMPLETE'])} | {t[':SIGNATURE']} | {t[':LAST-BOUNDARY'] if t[':COMPLETE'] else max(0,t[':LAST-BOUNDARY']-1)} |")
 (EXP/'CAMPAIGNS.md').write_text('\n'.join(lines)+'\n')
 cols=[('C1 random',lambda r:r[':MUTANT']=='ORIGINAL' and r[':PROFILE']=='c1' and r[':PREFIX']=='initial' and r[':CONFIG']=='random'),('C1 iterative',lambda r:r[':MUTANT']=='ORIGINAL' and r[':PROFILE']=='c1' and r[':PREFIX']=='initial' and r[':CONFIG']=='iterative'),('C1 3b',lambda r:r[':MUTANT']=='ORIGINAL' and r[':PROFILE']=='c1' and r[':PREFIX']=='initial' and r[':CONFIG']=='dedup'),('C2/data ORIGINAL',lambda r:r[':MUTANT']=='ORIGINAL' and r[':PROFILE']=='c2'),('All mutants',lambda r:r[':MUTANT']!='ORIGINAL')]
 cov=['| Label | '+' | '.join(x[0] for x in cols)+' |','|---|'+'---:|'*len(cols)]
 for label in old.catalogue():
  values=[sum(r[':LABELS'].get(label,0) for r in rs if pred(r)) for _,pred in cols]
  cov.append('| `'+label.lower()+'` | '+' | '.join(str(n) if n else 'unexercised' for n in values)+' |')
 (P/'results/coverage.md').write_text('\n'.join(cov)+'\n')
 print('E2 SUMMARIZE',len(rs),'measured records')
 for r in rs:print(r[':MUTANT'],r[':CONFIG'],r[':PROFILE'],r[':PREFIX'],r[':SEED'],r['status'],r['contract'],round(r[':SECONDS'],6),'depth',r[':DEEPEST-COMPLETED'],'positive',count(r,':G2-POSITIVE'))
if __name__=='__main__':main()
