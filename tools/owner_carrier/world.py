import re,glob,sys,os
sys.path.insert(0,os.path.dirname(__file__))
import sexp
S=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
def parse_list(s):
    n,_=sexp.read(s,0)
    def conv(n):
        if n.kind=='list': return [conv(k) for k in n.kids]
        return n.val.lower()
    return conv(n)
SIG={}
for line in open(S+'/sigs2.txt'):
    line=line.rstrip('\n')[6:]
    nodes=sexp.read_all(line)
    name=nodes[0].val.lower()
    def conv(n):
        if n.kind=='list': return [conv(k) for k in n.kids]
        if n.kind=='quote': return conv(n.kids[0])
        return n.val.lower()
    vals=[conv(n) for n in nodes[1:]]
    formals,ins,outs,cls,flags=vals
    SIG[name]=dict(formals=formals,ins=ins,outs=outs,cls=cls,touch=':touch' in flags,writer=':writer' in flags,entry=':entry' in flags)
T={n for n,v in SIG.items() if v['touch']}
W={n for n,v in SIG.items() if v['writer']}
def defs_in(root):
    out={}
    for f in sorted(glob.glob(root+'/host/*.lisp')+glob.glob(root+'/books/*.lisp')):
        src=open(f,errors='replace').read()
        try: forms=sexp.read_all(src)
        except Exception: continue
        def walk(forms):
            for n in forms:
                h=n.head()
                if h in ('defun','defund','defun-nx') and len(n.kids)>2:
                    nm=n.kids[1].val.lower()
                    if nm in T: out.setdefault(nm,[]).append((os.path.relpath(f,root),n))
                elif h in ('encapsulate','progn','local','mutual-recursion'):
                    walk([k for k in n.kids[1:] if k.kind=='list'])
        walk(forms)
    return out
