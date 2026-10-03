import sys,os,re,collections
sys.path.insert(0,os.path.dirname(__file__))
from world import *
ST='fn-owner-st'
HAND_NEW={  # helper -> new formals, new outs
 'fn-owner-ocfg':(['fn-owner-st'],None),
 'fn-owner-core':(['fn-owner-st'],None),
 'fn-owner-store':(['fn-owner-st'],None),
 'fn-owner-retain-carry':(['fn-owner-st'],None),
 'fn-owner-retain-statep':(['fn-owner-st'],None),
 'fn-owner-install-ocfg':(['oc','fn-owner-st'],'O'),
 'fn-owner-install-open-ocfg':(['oc','fn-owner-st'],'O'),
 'fn-owner-retain-carry-put':(['carry','fn-owner-st'],'O'),
}
HAND=set(HAND_NEW)
DROP=set()   # non-entry functions whose STATE formal goes (unused after the move)
def uses_state(t):
    return bool(re.search(r'(?<![\w-])state(?![\w-])',t) or re.search(r'\((value|er|value-triple)\s',t))
def cls(n):
    if n in HAND: return HAND_NEW[n][1] or 'R'
    if n in W: return 'O' if SIG[n]['outs']==['state'] else 'M'
    return 'R'
def new_formals(n):
    if n in HAND: return HAND_NEW[n][0]
    f=SIG[n]['formals']; out=[]
    for x in f:
        if x=='state':
            out.append(ST)
            if n in DROP: continue
        out.append(x)
    return out
def new_outs(n):
    c=cls(n); o=SIG[n]['outs']
    if c=='O': return [ST]
    if c=='M':
        r=[]
        for x in o:
            if x=='state': r.append(ST)
            r.append(x)
        return r
    return o
FLAGS=[]
UNUSED=set()
class Ctx:
    def __init__(s,fn,src): s.fn=fn; s.src=src; s.c=cls(fn)
def text(n,src): return src[n.start:n.end]
def rebuild(n,src,kt):
    # n list; kt: list of texts for kids
    out=[src[n.start:n.kids[0].start] if n.kids else src[n.start:n.end-1]]
    for i,k in enumerate(n.kids):
        out.append(kt[i])
        nxt=n.kids[i+1].start if i+1<len(n.kids) else n.end
        out.append(src[k.end:nxt])
    if not n.kids: out.append(')')
    return ''.join(out)
def is_sym(n,v): return n is not None and n.kind=='atom' and n.val.lower()==v
def qsym(n):
    if n.kind=='quote' and n.val=="'" and n.kids[0].kind=='atom': return n.kids[0].val.lower()
    if n.kind=='list' and n.head()=='quote' and len(n.kids)==2 and n.kids[1].kind=='atom': return n.kids[1].val.lower()
    return None
GLOB={'fn-owner':'ocfg','fn-owner-retain-carry':'carry'}
def callhead(n):
    return n.head() if n.kind=='list' else None
def xf(n,ctx,tail):
    src=ctx.src
    if n.kind=='atom':
        if tail=='O' and n.val.lower()=='state': return ST
        if tail=='M' and n.val.lower()=='state':
            FLAGS.append((ctx.fn,'bare state tail in M writer'))
        return text(n,src)
    if n.kind=='quote':
        return text(n,src)
    h=n.head()
    if h is None:
        return rebuild(n,src,[xf(k,ctx,False) for k in n.kids])
    k=n.kids
    # owner global accesses
    if h in ('boundp-global','f-boundp-global','get-global','f-get-global') and len(k)==3 and qsym(k[1]) in GLOB:
        g=GLOB[qsym(k[1])]
        if is_sym(k[2],'state'): arg=ST
        elif ctx.fn=='<event>': arg=xf(k[2],ctx,False)
        else:
            FLAGS.append((ctx.fn,'owner global read of a non-literal state')); return text(n,src)
        if h in ('boundp-global','f-boundp-global'):
            if g=='ocfg': return '(fn-owner-boundp %s)'%arg
            FLAGS.append((ctx.fn,'boundp of carry')); return text(n,src)
        return '(fn-owner-ocfg %s)'%arg if g=='ocfg' else '(fn-owner-retain-carry %s)'%arg
    if h in ('put-global','f-put-global') and len(k)==4 and qsym(k[1]) in GLOB:
        FLAGS.append((ctx.fn,'direct put of owner global')); return text(n,src)
    if h=='declare':
        return text(n,src)
    if h in ('let','let*'):
        kt=[text(k[0],src)]
        bl=k[1]
        bt=[]
        if bl.kind=='list':
            for b in bl.kids:
                if b.kind=='list' and len(b.kids)==2:
                    v=b.kids[0]; e=b.kids[1]
                    ch=callhead(e)
                    tcl=tail_class(e)
                    if is_sym(v,'state') and tcl=='O':
                        bt.append(rebuild(b,src,[ST,xf(e,ctx,'O')]))
                    elif is_sym(v,'state') and tcl=='M':
                        FLAGS.append((ctx.fn,'let-bound M writer '+ch)); bt.append(rebuild(b,src,[text(v,src),xf(e,ctx,False)]))
                    else:
                        bt.append(rebuild(b,src,[text(v,src),xf(e,ctx,False)]))
                else: bt.append(xf(b,ctx,False))
            kt.append(rebuild(bl,src,bt))
        else: kt.append(text(bl,src))
        for i in range(2,len(k)):
            kt.append(xf(k[i],ctx,tail if i==len(k)-1 else False))
        return rebuild(n,src,kt)
    if h in ('mv-let','stobj-let'):
        off=1 if h=='mv-let' else 2
        vars_=k[off]; e=k[off+1]
        vt=text(vars_,src)
        vnames=[x.val.lower() for x in vars_.kids if x.kind=='atom']
        tcl=tail_class(e) if 'state' in vnames else None
        etc=False
        if tcl=='M':
            vk=[text(x,src) for x in vars_.kids]
            vk=[ (ST+' state' if x.lower()=='state' else x) for x in vk]
            vt=rebuild(vars_,src,vk); etc='M'
        elif tcl=='O':
            FLAGS.append((ctx.fn,'mv-let over O writer'))
        kt=[text(k[0],src)]+([text(k[1],src)] if h=='stobj-let' else [])+[vt,xf(e,ctx,etc)]
        off=off+2
        for i in range(off,len(k)):
            kt.append(xf(k[i],ctx,tail if i==len(k)-1 else False))
        return rebuild(n,src,kt)
    if False:
        return rebuild(n,src,kt)
    if h=='if':
        return rebuild(n,src,[text(k[0],src),xf(k[1],ctx,False)]+[xf(x,ctx,tail) for x in k[2:]])
    if h=='cond':
        kt=[text(k[0],src)]
        for cl in k[1:]:
            if cl.kind=='list':
                kt.append(rebuild(cl,src,[xf(x,ctx,tail if (j==len(cl.kids)-1 and j>0) else False) for j,x in enumerate(cl.kids)]))
            else: kt.append(text(cl,src))
        return rebuild(n,src,kt)
    if h=='case':
        kt=[text(k[0],src),xf(k[1],ctx,False)]
        for cl in k[2:]:
            if cl.kind=='list' and cl.kids:
                kt.append(rebuild(cl,src,[text(cl.kids[0],src)]+[xf(x,ctx,tail if j==len(cl.kids)-1 else False) for j,x in enumerate(cl.kids) if j>0]))
            else: kt.append(text(cl,src))
        return rebuild(n,src,kt)
    if h=='with-local-stobj':
        return rebuild(n,src,[text(k[0],src),text(k[1],src),xf(k[2],ctx,tail)]+[text(x,src) for x in k[3:]])
    if h=='value' and tail=='M':
        return '(mv nil %s %s state)'%(xf(k[1],ctx,False),ST)
    if h=='value' and tail=='O':
        FLAGS.append((ctx.fn,'value tail in O writer'))
    if h=='mv' and tail=='M':
        kt=[xf(x,ctx,False) for x in k]
        if is_sym(k[-1],'state'):
            kt[-1]=ST+' state'
        else: FLAGS.append((ctx.fn,'mv tail not ending in state'))
        return rebuild(n,src,kt)
    # generic call
    kt=[text(k[0],src)]
    args=k[1:]
    if h in T or h in HAND:
        oldf=SIG[h]['formals'] if h in SIG else None
        nf=new_formals(h)
        if oldf is None or len(oldf)!=len(args):
            if args: FLAGS.append((ctx.fn,'arity '+h))
            kt+= [xf(a,ctx,False) for a in args]
        else:
            replace = h in HAND or h in DROP
            for f,a in zip(oldf,args):
                t=xf(a,ctx,False)
                if f=='state':
                    if is_sym(a,'state'):
                        t = ST if replace else ST+' '+t
                    elif ctx.fn=='<event>':
                        # a theorem's state argument is a term (another
                        # call's result): it denotes the carrier now when
                        # the callee reads only the carrier
                        t = t if replace else ST+' '+t
                    else:
                        FLAGS.append((ctx.fn,'state arg not literal in call of '+h))
                kt.append(t)
            res=rebuild(n,src,kt)
            return wrap_tail(res,h,ctx,tail)
    else:
        kt+=[xf(a,ctx,False) for a in args]
    res=rebuild(n,src,kt)
    return wrap_tail(res,h,ctx,tail)
def wrap_tail(res,h,ctx,tail):
    if not tail or tail=='R': return res
    hc=cls(h) if (h in T or h in HAND) else 'R'
    if tail==hc: return res
    outs=new_outs(h) if h in SIG or h in HAND else None
    if outs is None:
        return res  # macro or unknown: value/mv handled; others assumed fine
    if 'state' not in outs and ST not in outs:
        return res
    if tail=='M' and hc=='R':
        vs=[('s5-v%d'%i if o=='nil' else o) for i,o in enumerate(outs)]
        if len(vs)==1:
            return '(let ((state %s)) (mv nil nil %s state))'%(res,ST) if False else (FLAGS.append((ctx.fn,'tail bare-state call '+h)) or res)
        ret=[]
        for v in vs:
            if v=='state': ret.append(ST); 
            ret.append(v)
        return '(mv-let (%s) %s (mv %s))'%(' '.join(vs),res,' '.join(ret))
    FLAGS.append((ctx.fn,'tail class mismatch %s->%s %s'%(tail,hc,h)))
    return res
def xf_defun(n,src):
    k=n.kids; name=k[1].val.lower()
    ctx=Ctx(name,src)
    kt=[text(k[0],src),text(k[1],src)]
    # formals
    fk=[text(x,src) for x in k[2].kids]
    nf=new_formals(name)
    kt.append('('+' '.join(nf)+')')
    rest=k[3:]
    body=rest[-1]
    decls=[]
    for x in rest[:-1]:
        if x.kind=='list' and x.head()=='declare':
            parts=[text(x.kids[0],src)]
            for d in x.kids[1:]:
                if d.kind=='list' and d.head()=='xargs':
                    xs=[text(d.kids[0],src)]
                    i=1; had=False
                    while i<len(d.kids):
                        key=d.kids[i].val.lower() if d.kids[i].kind=='atom' else ''
                        val=d.kids[i+1] if i+1<len(d.kids) else None
                        if key==':stobjs':
                            had=True
                            if val.kind=='atom':
                                names=[val.val.lower()]
                            else: names=[y.val.lower() for y in val.kids]
                            if 'state' in names: names.insert(names.index('state'),ST)
                            if name in HAND or name in DROP: names=[y for y in names if y!='state']
                            xs+=[':stobjs','('+' '.join(names)+')']
                        elif key==':guard':
                            xs+=[':guard',xf(val,ctx,False)]
                        else:
                            xs+=[text(d.kids[i],src)]+([text(val,src)] if val is not None else [])
                        i+=2
                    if not had: xs+=[':stobjs',ST if name in DROP else '(%s state)'%ST]
                    parts.append(rebuild(d,src,xs) if len(xs)==len(d.kids) else '('+' '.join(xs)+')')
                else: parts.append(text(d,src))
            decls.append(rebuild(x,src,parts) if len(parts)==len(x.kids) else '('+' '.join(parts)+')')
        else: decls.append(text(x,src))
    bt=xf(body,ctx,ctx.c)
    ignorable=''
    alltext=' '.join(decls)+' '+bt
    rest_text=re.sub(r':stobjs\s*(\([^)]*\)|[\w-]+)','',bt+' '+' '.join(decls))
    if 'state' in nf and not uses_state(rest_text):
        ignorable='(declare (ignorable state))'
        UNUSED.add(name)
    kt+=decls
    if ignorable: kt.append(ignorable)
    kt.append(bt)
    # reassemble keeping gaps: rebuild from kid list positions for first 3 + rest
    out=[src[n.start:k[0].start]]
    allk=list(k)
    texts=kt[:3]+kt[3:]
    # map texts onto kids; ignorable inserted before body
    pieces=[]
    for i,kid in enumerate(allk):
        if i<3: pieces.append(kt[i])
        elif kid is body:
            if ignorable: pieces.append(ignorable+'\n  '+bt)
            else: pieces.append(bt)
        else: pieces.append(decls[i-3])
    return rebuild(n,src,pieces)
DEAD=['fn-owner-ocfg-of-other-global-put','fn-owner-bound-of-other-global-put',
 'fn-owner-retain-carry-of-other-global-put','fn-owner-installed-ocfg-effect',
 'fn-owner-installed-owner-bound','fn-owner-installed-other-global-effect',
 'fn-owner-installed-other-global-bound','fn-owner-installed-state-p1',
 'fn-owner-install-keeps-the-obligation-view','fn-owner-open-state-p1',
 'fn-owner-open-keeps-the-obligation-view',
 'fn-owner-callback-owner-bound-of-other-put',
 'fn-owner-retain-carry-put-preserves-state-p1',
 'fn-owner-retain-carry-put-frames-global-association',
 'fn-owner-retain-carry-of-other-global-update-by-definition',
 'fn-owner-ocfg-of-other-global-update-by-definition',
 ]
# Theorems about the owner globals' place in STATE: false or vacuous over the
# carrier (the stobj discipline is their frame).  Deleted, and dropped from
# every hint that names them.
DELETE=['fn-orr-open-owner-association','fn-orr-open-other-association',
 'fn-orr-writer-enter-frame','fn-orr-writer-leave-frame',
 'fn-ocd-get-owner-of-other-put']
DELETE+=['fn-ocd-writer-owner-frame']
# Local restatements of the carrier's own installer facts: deleted, their
# uses renamed to books/owner-carrier.lisp's.
RENAME={'fn-ocd-get-owner-of-retain-carry-put':'fn-owner-ocfg-of-retain-carry-put',
 'fn-ocd-get-owner-of-open-install':'fn-owner-open-ocfg-effect',
 'fn-ocd-get-owner-of-install':'fn-owner-ocfg-of-install-ocfg',
 'fn-orr-installed-open-ocfg':'fn-owner-open-ocfg-effect'}
DEAD+=DELETE
DELETE+=list(RENAME)
EVENTS=('defthm','defthmd','thm','assert-event','defthm-nx','must-fail','must-succeed','defthm?')
def xf_event(n,src):
    ctx=Ctx('<event>',src); ctx.c='R'
    t=xf(n,ctx,False)
    # A hint that enabled the old accessors (state-global reads) would now
    # open the carrier's field access under its installer rules: drop them.
    t=re.sub(r"(?<=[\s'(])fn-owner-(ocfg|retain-carry|boundp)(?=[\s)])(?<!\(fn-owner-ocfg)",lambda m:'' if True else m.group(0),t) if False else t
    t=re.sub(r"(?<![(\w-])fn-owner-(ocfg|retain-carry|boundp)(?![\w-])",'',t)
    for a,b in RENAME.items():
        t=re.sub(r'(?<![\w-])'+re.escape(a)+r'(?![\w-])',b,t)
    for d in DEAD:
        t=re.sub(r'\n[ \t]*'+re.escape(d)+r'[ \t]*(?=\n)','',t)
        t=re.sub(r'(?<![\w-])'+re.escape(d)+r'(?![\w-])','',t)
    return t
def mentions(n):
    if n.kind=='atom': return n.val.lower() in T or n.val.lower() in HAND
    return any(mentions(k) for k in (n.kids or []))
def transform_file(path,names,events=True):
    src=open(path).read()
    forms=sexp.read_all(src)
    edits=[]
    def walk(fs):
        for n in fs:
            h=n.head()
            if h in ('defun','defund','defun-nx') and n.kids[1].val.lower() in names:
                edits.append((n.start,n.end,xf_defun(n,src)))
            elif h in EVENTS and len(n.kids)>1 and n.kids[1].kind=='atom' and n.kids[1].val.lower() in DELETE:
                edits.append((n.start,n.end,''))
            elif h=='local' and len(n.kids)==2 and n.kids[1].head() in EVENTS and n.kids[1].kids[1].kind=='atom' and n.kids[1].kids[1].val.lower() in DELETE:
                e=n.end
                while e<len(src) and src[e] in ' \t': e+=1
                if src[e:e+2]=='\n\n': e+=1
                edits.append((n.start,e,''))
            elif events and h in EVENTS and mentions(n):
                edits.append((n.start,n.end,xf_event(n,src)))
            elif h in ('encapsulate','progn','local','mutual-recursion'):
                walk([x for x in n.kids[1:] if x.kind=='list'])
    walk(forms)
    for s,e,t in sorted(edits,reverse=True):
        src=src[:s]+t+src[e:]
    return src,len(edits)

def tail_class(e):
    """The writer class of the tail calls of expression E: 'M' or 'O' if some
    tail position calls a writer of that class, else None."""
    found=set()
    def go(n):
        if n.kind!='list': return
        h=n.head(); k=n.kids
        if h is None: return
        if h in ('let','let*'): go(k[-1]); return
        if h=='mv-let': go(k[-1]); return
        if h=='stobj-let': go(k[-1]); return
        if h=='with-local-stobj': go(k[2]); return
        if h=='if': go(k[2]); go(k[3]) if len(k)>3 else None; return
        if h=='cond':
            for cl in k[1:]:
                if cl.kind=='list' and len(cl.kids)>1: go(cl.kids[-1])
            return
        if h=='case':
            for cl in k[2:]:
                if cl.kind=='list' and len(cl.kids)>1: go(cl.kids[-1])
            return
        if h in T or h in HAND:
            c=cls(h)
            if c in ('M','O'): found.add(c)
    go(e)
    if len(found)>1: FLAGS.append(('?','mixed tail classes'))
    return found.pop() if found else None
