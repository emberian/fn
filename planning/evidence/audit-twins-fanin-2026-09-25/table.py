import os
import sys, json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from split import *
aff=g['aff']
def est(S):
    S=set(S); memo={}
    def cp(b):
        if b in memo: return memo[b]
        best=0
        for d in closure[b]:
            # longest path through S only (deps in S)
            pass
        # predecessors in S via transitive closure
        st=list(closure[b]); seen=set(); preds=set()
        while st:
            x=st.pop()
            if x in seen: continue
            seen.add(x)
            if x in S: preds.add(x)
            else: st.extend(closure[x])
        memo[b]=walls.get(b,0)+max([cp(p) for p in preds],default=0)
        return memo[b]
    sys.setrecursionlimit(10000)
    c=max([cp(b) for b in S],default=0); s=sum(walls.get(b,0) for b in S)
    return round(max(c,s/2),1), round(c,1), round(s,1)
rows=[]
for b in sorted([b for b in aff if aff[b]>100 and b.startswith('books/')], key=lambda b:-aff[b]):
    r,users,names,intra,span=analyze(b)
    heavy_used={n for n in names if any(aff[u]>=100 for u in users[n])}
    # downward closure
    D=set(heavy_used); ch=True
    while ch:
        ch=False
        for n in list(D):
            for m in intra[n]:
                if m not in D: D.add(m); ch=True
    rest=[n for n in names if n not in D]
    R0=set().union(*[users[n] for n in rest]) if rest else set()
    post=((trans_includers(R0)|R0)&roots)|{b}
    pre=(trans_includers([b])&roots)|{b}
    used=sum(1 for n in names if users[n])
    rows.append(dict(book=b,deps=aff[b],names=len(names),used=used,unused=len(names)-used,shape=len(D),rest=len(rest),post=len(post),pre_est=est(pre)[0],post_est=est(post)[0],wall=round(walls.get(b,0),1)))
    print(json.dumps(rows[-1]),flush=True)
json.dump(rows,open(SP+'table.json','w'))
