import os
import sys, re, json, pickle
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools')); sys.path.insert(0,str(ROOT))
import os; os.chdir(ROOT)
import certify_books as cb
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__))); from clean import clean
roots=cb.default_books()
closure=cb.local_closure(roots)
books=sorted(closure)
# reverse edges
rev={b:set() for b in books}
for b,deps in closure.items():
    for d in deps: rev[d].add(b)
def trans_includers(b, rev=rev):
    seen=set(); st=[b]
    while st:
        x=st.pop()
        for y in rev.get(x,()):
            if y not in seen: seen.add(y); st.append(y)
    return seen
rootset=set(roots)
aff={b: len((trans_includers(b)|{b}) & rootset) for b in books}
walls=cb.archived_walls(books)
# source parsing
def strip(src):
    src=re.sub(r'#\|.*?\|#','',src,flags=re.S)
    out=[]
    for line in src.split('\n'):
        # remove ; comments outside strings roughly
        i=line.find(';')
        out.append(line if i<0 else line[:i])
    return '\n'.join(out)
DEF=re.compile(r'\(\s*(defun|defund|defun-sk|defund-sk|define|defmacro|defthm|defthmd|defconst|defabbrev|defrec|deftheory|defstub|defun-nx|defund-nx|defrule|defruled|defstobj|defn|defnd|defaggregate|defprod|deflist|defsection|defmacro-last)\s+([^\s()]+)',re.I)
TOK=re.compile(r"[A-Za-z0-9*+\-/<>=!?%&$^_:.]+")
defs={}; toks={}
for b in books:
    s=clean(cb.book_source(b).read_text(errors='replace'))
    defs[b]=[(k.lower(),n.lower()) for k,n in DEF.findall(s)]
    toks[b]=set(t.lower() for t in TOK.findall(s))
pickle.dump(dict(roots=roots,closure=closure,rev=rev,aff=aff,walls=walls,defs=defs,toks=toks),open(''+os.environ.get('FN_AUDIT_OUT','/tmp/fn-audit')+'/g.pkl','wb'))
big=sorted([b for b in books if aff[b]>100], key=lambda b:-aff[b])
for b in big: print(aff[b]-1 if b in rootset else aff[b], b, round(walls.get(b,-1),1), len(defs[b]))
print(len(roots), len(books))
