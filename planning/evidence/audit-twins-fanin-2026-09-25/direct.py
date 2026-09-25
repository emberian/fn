import os
import sys,pickle
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from split import *
for book in sys.argv[1:]:
    r,users,names,intra,span=analyze(book)
    ns=set(names)
    print('==',book,'names',len(names))
    for d in sorted(rev[book], key=lambda d:-g['aff'][d]):
        used=sorted(ns & toks[d])
        print('  direct',d,'aff',g['aff'][d],'uses',len(used),used[:14])
    # names used by exactly the users, show changed name users
    for n in sys.argv[0:0]: pass
