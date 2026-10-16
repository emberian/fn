#!/usr/bin/env python3
"""Fresh, serial hbox proof sessions; stop at the first refusal, never retry."""
from pathlib import Path
import sys, subprocess, json, hashlib, time
ROOT=Path(__file__).resolve().parents[2]
HERE=ROOT/'build/pin-value'
sys.path.insert(0,str(ROOT/'tools'))
import proof_repl as pr
CHANGED=subprocess.check_output(['git','-C',str(ROOT),'diff','--name-only','8c4c8c8d8','--','books','tests/acl2']).decode().splitlines()
BOOKS=[p[:-5] for p in CHANGED if p.endswith('.lisp')]
GRAPH={}
for book in BOOKS: GRAPH.update(pr.include_graph(ROOT,book))
ORDER=pr.dependency_order(GRAPH,BOOKS)
RESULTS=HERE/'gate-results.json'
data=json.loads(RESULTS.read_text()) if RESULTS.exists() else {}
def key(book):
 names=pr.include_graph(ROOT,book)
 return hashlib.sha256(b''.join(n.encode()+ (ROOT/(n+'.lisp')).read_bytes() for n in sorted(names))).hexdigest()
def run(args,log,seconds):
 cmd=['timeout',str(seconds),'python3',str(HERE/'repl.py'),*args]
 with log.open('w') as f:
  return subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=ROOT,timeout=seconds+30).returncode

def save(): RESULTS.write_text(json.dumps(data,indent=2)+'\n')
if '--seed' in sys.argv:
 for b,n in [('books/owner-config','pv2-owner-config'),('books/config-owner-live-open','pv2-live-open')]:
  data[b]={'result':'PASS fresh load; illegal-to-certify-message NIL','closure':key(b),'session':n,'load_log':'/tmp/pin-value-'+n+'.log','illegal_log':'/tmp/pin-value-'+n+'-illegal.log'}
 save(); print('seeded two completed fresh sessions'); raise SystemExit(0)
if '--list' in sys.argv:
 print('\n'.join(ORDER)); raise SystemExit(0)
for book in ORDER:
 closure=key(book)
 if data.get(book,{}).get('closure')==closure and data[book]['result'].startswith('PASS'): continue
 name='pv2-'+Path(book).name
 log=HERE/(name+'-load.log'); ilog=HERE/(name+'-illegal.log'); slog=HERE/(name+'-stop.log')
 print('START',book,flush=True)
 rc=run(['start',name,book,'--host','hbox','--load-timeout','1800','--certify-jobs','1'],log,2400)
 data[book]={'result':'RED load','closure':closure,'session':name,'load_log':str(log.relative_to(ROOT)),'start_exit':rc}
 save()
 if rc:
  print('RED',book,'exit',rc,'log',log,flush=True)
  raise SystemExit(rc)
 rc=run(['send',name,'(@ illegal-to-certify-message)','--full'],ilog,120)
 output=ilog.read_text()
 data[book]['illegal_log']=str(ilog.relative_to(ROOT))
 # Require the complete NIL answer immediately after the prompt, not a substring.
 nil=bool(__import__('re').search(r'ACL2\s*!>\s*NIL\s*\n',output))
 data[book]['result']='PASS fresh load; illegal-to-certify-message NIL' if rc==0 and nil else 'RED illegal-to-certify-message'
 save()
 stop=run(['stop',name],slog,120)
 data[book]['stop_exit']=stop; save()
 if rc or not nil or stop:
  print('RED',book,data[book]['result'],'stop',stop,flush=True); raise SystemExit(2)
 with (HERE/'STATE.md').open('a') as f: f.write('\nFresh hbox gate PASS: '+book+'; illegal-to-certify-message NIL; session stopped.\n')
 print('PASS',book,flush=True)
print('ALL FRESH SESSION GATES PASS',len(ORDER),flush=True)
