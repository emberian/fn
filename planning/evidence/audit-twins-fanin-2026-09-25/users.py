import os
import sys
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from split import *
book=sys.argv[1]
r,users,names,intra,span=analyze(book)
for n in sys.argv[2:]:
    n=n.lower()
    up={n}; ch=True
    while ch:
        ch=False
        for m in names:
            if m not in up and intra[m]&up: up.add(m); ch=True
    us=set().union(*[users[m] for m in up])
    print(n, span.get(n), 'upward',sorted(up-{n})[:10], 'users',sorted(((g['aff'][u],u) for u in us),reverse=True)[:8], 'closure', len((trans_includers(us)|us)&roots))
