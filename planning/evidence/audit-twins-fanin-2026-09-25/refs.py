import os
import sys,re,pickle,subprocess
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from split import *
aff=g['aff']
R=str(ROOT)
for n in sys.argv[1:]:
    n=n.lower()
    d=subprocess.run(['grep','-rniE','--include=*.lisp',r'^\s*\((def[a-z-]*)\s+'+re.escape(n)+r'(\s|$)',R+'/books',R+'/host',R+'/tests'],capture_output=True,text=True).stdout.strip().replace(R+'/','')
    print('==',n,'| def:',d or 'NONE')
    users=[b for b in toks if n in toks[b]]
    bk=[b for b in users if b.startswith('books/')]; ts=[b for b in users if b.startswith('tests/')]; hb=[b for b in users if b.startswith('host/')]
    print('   books',len(bk),sorted(bk)[:8]); print('   tests',len(ts),sorted(ts)[:5]); print('   hostbooks',hb)
    o=subprocess.run(['grep','-rnwi','--',n,R+'/host/native',R+'/tools',R+'/planning/proofs.json',R+'/planning/proof-events.json',R+'/planning/requirements.json',R+'/planning/current-view.json'],capture_output=True,text=True).stdout.replace(R+'/','').splitlines()
    for l in o[:6]: print('   ',l[:170])
    if d:
        b=d.split(':')[0][:-5]
        if b in aff: print('   defining book deps (dry-run count):',aff[b])
