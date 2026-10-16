#!/usr/bin/env python3
"""Check fresh per-book certificate evidence against this exact source closure."""
from pathlib import Path
import sys,subprocess,json,hashlib,re
ROOT=Path(__file__).resolve().parents[2]; HERE=ROOT/'build/pin-value'
sys.path.insert(0,str(ROOT/'tools'));import proof_repl as pr
books=[p[:-5] for p in subprocess.check_output(['git','-C',str(ROOT),'diff','--name-only','8c4c8c8d8','--','books','tests/acl2']).decode().splitlines() if p.endswith('.lisp')]
data=json.loads((HERE/'cert-results.json').read_text()); errors=[]
for book in books:
 row=data.get(book,{})
 if not row.get('result','').startswith('PASS CERTIFY-BOOK'):
  errors.append(book+': '+row.get('result','missing'));continue
 key=hashlib.sha256(b''.join(n.encode()+(ROOT/(n+'.lisp')).read_bytes() for n in sorted(pr.include_graph(ROOT,book)))).hexdigest()
 if row.get('closure')!=key:errors.append(book+': source closure changed after check')
 cert=(ROOT/row['cert_log']).read_text(); marker='PIN-VALUE-CERTIFIED-'+Path(book).name
 if len(re.findall(r'^'+re.escape(marker)+r'\s*$',cert,re.M))!=1:errors.append(book+': expected one successful CERTIFY-BOOK marker')
 if '* Step 4:  Write the certificate' not in cert:errors.append(book+': no certificate-write step')
 illegal=(ROOT/row['illegal_log']).read_text()
 if not re.search(r'ACL2\s*!>\s*NIL\s*\n',illegal):errors.append(book+': diagnostic not NIL')
 if row.get('stop_exit')!=0:errors.append(book+': session stop not confirmed')
for name in ['erase','host-attach','host-world','host-build','interface','cost','roots']:
 p=HERE/('pv2-'+name+'.exit')
 if not p.exists() or p.read_text().strip()!='0':errors.append(name+': static gate not exit 0')
print(f'{len(books)} changed books audited against their current source closures; {len(errors)} differences')
for e in errors:print(e)
raise SystemExit(bool(errors))
