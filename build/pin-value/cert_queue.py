#!/usr/bin/env python3
"""Certify changed books ALONE in serial fresh house REPL sessions on hbox."""
from pathlib import Path
import sys,subprocess,json,hashlib,re
ROOT=Path(__file__).resolve().parents[2]; HERE=ROOT/'build/pin-value'
sys.path.insert(0,str(ROOT/'tools')); import proof_repl as pr
changed=subprocess.check_output(['git','-C',str(ROOT),'diff','--name-only','8c4c8c8d8','--','books','tests/acl2']).decode().splitlines()
books=[p[:-5] for p in changed if p.endswith('.lisp')]
graph={}
for b in books:graph.update(pr.include_graph(ROOT,b))
order=pr.dependency_order(graph,books)
path=HERE/'cert-results.json'; data=json.loads(path.read_text()) if path.exists() else {}
def save():path.write_text(json.dumps(data,indent=2)+'\n')
def key(book):return hashlib.sha256(b''.join(n.encode()+(ROOT/(n+'.lisp')).read_bytes() for n in sorted(pr.include_graph(ROOT,book)))).hexdigest()
def run(args,log,seconds):
 with log.open('w') as f:return subprocess.run(['timeout',str(seconds),'python3',str(HERE/'repl.py'),*args],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,timeout=seconds+30).returncode
if len(sys.argv)>1:order=[b for b in order if b==sys.argv[1]]
for book in order:
 closure=key(book)
 if data.get(book,{}).get('closure')==closure and data[book]['result'].startswith('PASS'):continue
 name='pvc-'+Path(book).name
 start=HERE/(name+'-start.log'); cert=HERE/(name+'-certify.log'); illegal=HERE/(name+'-illegal.log'); stop=HERE/(name+'-stop.log')
 print('CERTIFY START',book,flush=True)
 rc=run(['start',name,book,'--upto','#1','--host','hbox','--load-timeout','1800','--certify-jobs','1'],start,2400)
 data[book]={'result':'RED startup','closure':closure,'session':name,'start_log':str(start.relative_to(ROOT)),'start_exit':rc};save()
 if rc:raise SystemExit(rc)
 marker='PIN-VALUE-CERTIFIED-'+Path(book).name
 form=f'(ld (quote ((certify-book "{Path(book).name}" 0 t) (value-triple (cw "~%{marker}~%")))) :ld-error-action :return :ld-error-triples t)'
 rc=run(['send',name,form,'--limit','1800','--full'],cert,2400)
 text=cert.read_text(); success=rc==0 and bool(re.search(r'^'+re.escape(marker)+r'\s*$',text,re.M)) and not re.search(r'ACL2 Error|HARD ACL2 ERROR|\*+ FAILED \*+',text)
 data[book].update(result='RED certify',cert_log=str(cert.relative_to(ROOT)),cert_exit=rc);save()
 if not success:
  print('RED CERTIFY',book,'log',cert,flush=True)
  # Keep its session for diagnosis; the operator ends it before another starts.
  raise SystemExit(3)
 rc=run(['send',name,'(@ illegal-to-certify-message)','--full'],illegal,120)
 nil=rc==0 and bool(re.search(r'ACL2\s*!>\s*NIL\s*\n',illegal.read_text()))
 data[book].update(result='PASS CERTIFY-BOOK; illegal-to-certify-message NIL' if nil else 'RED diagnostic',illegal_log=str(illegal.relative_to(ROOT)));save()
 stop_rc=run(['stop',name],stop,120);data[book]['stop_exit']=stop_rc;save()
 if not nil or stop_rc:raise SystemExit(2)
 with (HERE/'STATE.md').open('a') as f:f.write('\nCERTIFY-BOOK PASS alone in fresh hbox session: '+book+'; illegal-to-certify-message NIL; stopped.\n')
 print('CERTIFY PASS',book,flush=True)
print('CERTIFY QUEUE COMPLETE',len(order),flush=True)
