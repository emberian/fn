def load(f):
    d={}
    for l in open(f):
        if l.startswith("TOTAL"): continue
        p=l.rstrip("\n").rsplit(" ",2)
        if len(p)<3: continue
        d[p[0]]=(int(p[1]),int(p[2]))
    return d
a=load('c1.tally.tsv'); b=load('c2.tally.tsv')
def table(prefix,top=12):
    keys=[k for k in set(a)|set(b) if k.startswith(prefix)]
    rows=[(b.get(k,(0,0))[0]-a.get(k,(0,0))[0],k,a.get(k,(0,0)),b.get(k,(0,0))) for k in keys]
    rows.sort(reverse=True)
    print("==",prefix, "total c1 %.2f c2 %.2f MB (delta %+.2f)"%(sum(a[k][0] for k in keys if k in a)/1e6,sum(b[k][0] for k in keys if k in b)/1e6,(sum(b[k][0] for k in keys if k in b)-sum(a[k][0] for k in keys if k in a))/1e6))
    for d,k,x,y in rows[:top]: print("%+8.3f MB  %-56s c1 %7.2f (%d)  c2 %7.2f (%d)"%(d/1e6,k[len(prefix):],x[0]/1e6,x[1],y[0]/1e6,y[1]))
    print("   shrunk:")
    for d,k,x,y in rows[-2:]: print("%+8.3f MB  %-56s c1 %7.2f  c2 %7.2f"%(d/1e6,k[len(prefix):],x[0]/1e6,y[0]/1e6))
import sys
for p,t in (("TYPE DYNAMIC|",14),("TYPE IMMOBILE|",6),("TYPE READ-ONLY|",4),("OWNER DYNAMIC|symbol|",6),("OWNER IMMOBILE|code|",10)):
    table(p,t)
