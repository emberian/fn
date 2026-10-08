#!/usr/bin/env python3.12
"""Rewrite e/d :in-theory hints of defthm forms into minimal-theory + the runes the
proof used (read from a proof_repl --full log). Usage:
  minthy.py BOOK LOG OUT [--min-ms N] [--skip NAME,...] [--only NAME,...]"""
import re,sys,json

def scan_forms(src):
    i=0;n=len(src);forms=[]
    while i<n:
        c=src[i]
        if c==';':
            while i<n and src[i]!='\n': i+=1
        elif src.startswith('#|',i):
            d=1;i+=2
            while i<n and d:
                if src.startswith('|#',i): d-=1;i+=2
                elif src.startswith('#|',i): d+=1;i+=2
                else: i+=1
        elif c=='(':
            s=i;j=end_of(src,i);forms.append((s,j,src[s:j]));i=j
        else: i+=1
    return forms

def end_of(src,i):
    n=len(src);d=0
    while i<n:
        c=src[i]
        if c==';':
            while i<n and src[i]!='\n': i+=1
            continue
        if src.startswith('#|',i):
            dd=1;i+=2
            while i<n and dd:
                if src.startswith('|#',i): dd-=1;i+=2
                elif src.startswith('#|',i): dd+=1;i+=2
                else: i+=1
            continue
        if c=='"':
            i+=1
            while src[i]!='"':
                if src[i]=='\\': i+=1
                i+=1
            i+=1;continue
        if src.startswith('#\\',i): i+=3;continue
        if c=='|':
            i+=1
            while src[i]!='|': i+=1
            i+=1;continue
        if c=='(': d+=1
        elif c==')':
            d-=1
            if d==0: return i+1
        i+=1
    raise ValueError('unbalanced')

def parse_log(log):
    # blocks: 'ok #N kind name: ACL2 time T s; prover steps S; elapsed' then Summary ... Rules: (...)
    res={}
    pos=[m.start() for m in re.finditer(r'^(ok|REFUSED)\s+#\d+ ',log,re.M)]
    pos.append(len(log))
    for a,b in zip(pos,pos[1:]):
        blk=log[a:b]
        m=re.match(r'(ok|REFUSED)\s+#(\d+) (\S+) ([^:]*): ACL2 time ([0-9.-]+) s; prover steps ([0-9,-]+)',blk)
        if not m: continue
        st,idx,kind,name,t,steps=m.groups()
        rules=None
        rm=re.search(r'^Rules: (.*?)\n(?:Hint-events|Splitter|Time:|Warnings|Prover steps)',blk,re.M|re.S)
        if rm:
            rules=rm.group(1)
        res[int(idx)]=dict(status=st,kind=kind,name=name.strip(),time=float(t) if t!='-' else 0.0,steps=int(steps.replace(',','')) if steps!='-' else 0,rules=rules)
    return res

def parse_runes(txt):
    txt=txt.strip()
    if txt=='NIL': return []
    # tokenise
    toks=re.findall(r'\(|\)|\.|[^\s()]+',txt)
    pos=0
    def rd():
        nonlocal pos
        t=toks[pos];pos+=1
        if t=='(':
            l=[]
            while toks[pos]!=')':
                l.append(rd())
            pos+=1
            return l
        return t
    return rd()

def rune_text(r):
    # r is list like [':DEFINITION','F'] or [':TYPE-PRESCRIPTION','F','.','1']
    if r[0].startswith(':FAKE-RUNE'): return None
    parts=[x.lower() if x!='.' else '.' for x in r]
    return '('+' '.join(parts)+')'

def find_in_theory(form):
    # return (start,end) of the value subform after :in-theory, if exactly one
    idx=[m.start() for m in re.finditer(r':in-theory\b',form)]
    if len(idx)!=1: return None
    j=idx[0]+len(':in-theory')
    while form[j].isspace(): j+=1
    if form[j]=='(' :
        return (idx[0],j,end_of(form,j))
    if form[j]=="'" and form[j+1]=='(':
        return (idx[0],j,end_of(form,j+1))
    return None

if __name__=='__main__':
    book,logf,out=sys.argv[1:4]
    minms=30
    skip=set();only=set()
    a=sys.argv[4:]
    k=0
    while k<len(a):
        if a[k]=='--min-ms': minms=int(a[k+1]);k+=2
        elif a[k]=='--skip': skip=set(a[k+1].split(','));k+=2
        elif a[k]=='--only': only=set(a[k+1].split(','));k+=2
        else: k+=1
    src=open(book).read()
    forms=scan_forms(src)
    log=open(logf).read()
    res=parse_log(log)
    # map form index (#N counts all top-level forms as the REPL does) -> forms[N-1]
    edits=[];changed=[]
    for N,info in res.items():
        if N-1>=len(forms): continue
        s,e,t=forms[N-1]
        if info['kind'] not in ('defthm','defun') or info['status']!='ok' or info['rules'] is None: continue
        nm=info['name']
        if nm in skip or (only and nm not in only): continue
        if info['time']*1000<minms: continue
        # local wrapper: form may be (local (defthm ...)); log reports kind of inner? keep as is
        loc=find_in_theory(t)
        if not loc: continue
        try: rl=parse_runes(info['rules'])
        except Exception as ex: continue
        runes=[rune_text(r) for r in rl if isinstance(r,list)]
        runes=[r for r in runes if r]
        # drop runes that minimal-theory already has: keep all, harmless
        lines=[];cur=''
        for r in sorted(runes):
            if len(cur)+len(r)+1>66 and cur: lines.append(cur);cur=r
            else: cur=(cur+' '+r) if cur else r
        if cur: lines.append(cur)
        ind=' '*30
        body=('\n'+ind).join(lines)
        new="(union-theories (theory 'minimal-theory)\n"+ind[:-1]+"'("+body+"))"
        a0,vs,ve=loc
        # preserve quote form: if original was '( ...) then value began with quote
        tv=t[:vs].rstrip()
        t2=t[:a0]+':in-theory '+new+t[ve:]
        edits.append((s,e,t2,nm));changed.append(nm)
    out_src=src
    for s,e,t2,nm in sorted(edits,reverse=True):
        out_src=out_src[:s]+t2+out_src[e:]
    open(out,'w').write(out_src)
    print(json.dumps(changed))
