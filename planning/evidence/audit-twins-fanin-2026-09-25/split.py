import os
import sys, re, pickle, subprocess, json
from pathlib import Path
SP=os.environ.get('FN_AUDIT_OUT','/tmp/fn-audit')+'/'
ROOT=Path(__file__).resolve().parents[3]
g=pickle.load(open(SP+'g.pkl','rb'))
roots=set(g['roots']); rev=g['rev']; toks=g['toks']; walls=g['walls']; closure=g['closure']
TOK=re.compile(r"[A-Za-z0-9*+\-/<>=!?%&$^_:.]+")
DEFH=re.compile(r'\(\s*(def[\w-]*)\s+([^\s()]+)',re.I)
def forms(path):
    s=path.read_text(errors='replace'); out=[]; i=0; n=len(s); line=1; depth=0; start=None; sl=None
    while i<n:
        c=s[i]
        if c=='\n': line+=1
        if c==';':
            j=s.find('\n',i); i=n if j<0 else j; continue
        if c=='#' and i+1<n and s[i+1]=='|':
            j=s.find('|#',i); line+=s.count('\n',i,j); i=j+2; continue
        if c=='"':
            j=i+1
            while s[j]!='"':
                if s[j]=='\\': j+=1
                j+=1
            line+=s.count('\n',i,j); i=j+1; continue
        if c=='#' and i+1<n and s[i+1]=='\\': i+=3; continue
        if c=='(':
            if depth==0: start=i; sl=line
            depth+=1
        elif c==')':
            depth-=1
            if depth==0: out.append((sl,line,s[start:i+1]))
        i+=1
    return out
from clean import clean
def strip(t): return clean(t)
def trans_includers(bs):
    seen=set(bs); st=list(bs)
    while st:
        x=st.pop()
        for y in rev.get(x,()):
            if y not in seen: seen.add(y); st.append(y)
    return seen
def analyze(book, changed_lines=None, report=True):
    fs=forms(ROOT/(book+'.lisp'))
    names=[]; body={}; span={}
    for sl,el,t in fs:
        m=DEFH.match(t)
        if not m: continue
        head=m.group(1).lower()
        if head in ('defsection',): continue
        n=m.group(2).lower(); names.append(n); body[n]=set(x.lower() for x in TOK.findall(strip(t))); span[n]=(sl,el)
        # also in-theory / encapsulate names are ignored
    nameset=set(names)
    intra={n:(body[n]&nameset)-{n} for n in names}
    deps=trans_includers([book])-{book}
    users={n:{d for d in deps if n in toks[d]} for n in names}
    direct={d for d in rev[book]}
    res=dict(book=book,nnames=len(names),ndeps=len(deps & roots),ndirect=len(direct))
    # usage histogram
    cnt=sorted(((len(users[n]),n) for n in names),reverse=True)
    res['top']=cnt[:12]; res['unused']=[n for c,n in cnt if c==0]
    # direct includers that reference no own name
    res['direct_ref_none']=sorted(d for d in direct if not (toks[d]&nameset))
    if changed_lines is not None:
        C={n for n in names if any(span[n][0]<=l<=span[n][1] for l in changed_lines)}
        # upward closure
        U=set(C); changed=True
        while changed:
            changed=False
            for n in names:
                if n not in U and intra[n]&U: U.add(n); changed=True
        R0=set().union(*[users[n] for n in U]) if U else set()
        post=(trans_includers(R0)|R0)&roots
        res.update(changed=sorted(C),upward=len(U),shape=len(names)-len(U),post=len(post)+1,
                   post_wall=round(sum(walls.get(b,0) for b in post)+walls.get(book,0),1),
                   pre_wall=round(sum(walls.get(b,0) for b in (deps&roots))+walls.get(book,0),1))
    return res,users,names,intra,span
def changed(book, base):
    d=subprocess.run(['git','-C',str(ROOT),'diff','-U0',base,'HEAD','--',book+'.lisp'],capture_output=True,text=True).stdout
    ls=set()
    for m in re.finditer(r'^@@ -\S+ \+(\d+)(?:,(\d+))? @@',d,re.M):
        a=int(m.group(1)); c=int(m.group(2) or 1)
        ls.update(range(a,a+max(c,1)))
    return ls
if __name__=='__main__':
    base=sys.argv[1]
    for b in sys.argv[2:]:
        r,*_=analyze(b, changed(b,base))
        print(json.dumps(r,default=list))
