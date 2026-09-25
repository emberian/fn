import os
import sys,json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from split import *
aff=g['aff']
names={}
DEFN=DEFH
for b in closure:
    if not b.startswith('books/'): continue
    names[b]={m.group(2).lower() for m in DEFN.finditer(strip((ROOT/(b+'.lisp')).read_text(errors='replace')))}
def deps_without(B, removed):
    # roots reaching B when edges in removed (set of (includer,B')) are replaced by B''s includes
    cl={k:list(v) for k,v in closure.items()}
    for (i,b) in removed:
        cl[i]=[x for x in cl[i] if x!=b]+[y for y in closure[b] if y not in cl[i]]
    r={}
    for k,v in cl.items():
        for d in v: r.setdefault(d,set()).add(k)
    seen={B}; st=[B]
    while st:
        x=st.pop()
        for y in r.get(x,()):
            if y not in seen: seen.add(y); st.append(y)
    return len(seen&roots)
if __name__=='__main__':
    rows=[]
    for b in closure:
        if not b.startswith('books/') or aff[b]<=30: continue
        for i in rev[b]:
            if not i.startswith('books/'): continue
            if not (toks[i] & names[b]):
                after=deps_without(b,{(i,b)})
                nf=len(re.findall(r'\(\s*(?:defun|defund|defmacro|defconst|define|defstub)\s',strip((ROOT/(b+'.lisp')).read_text(errors='replace')),re.I)); rows.append((aff[b]-after,b,aff[b],after,i,aff[i],'fns',nf))
    rows.sort(reverse=True)
    for r in rows[:40]:
        if r[7]>0 and 'attach' not in r[1]: print(r)
    print('total zero-use include edges into books with >30 deps:',len(rows))
    print('what-if injection:',deps_without('books/injection',{('books/hybrid-carrier','books/injection'),('books/hybrid-store','books/injection')}))
    print('what-if hybrid-store:',deps_without('books/hybrid-store',{('books/topic-history-metadata','books/hybrid-store')}))
