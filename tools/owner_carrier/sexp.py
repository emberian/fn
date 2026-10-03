# Positional s-expression reader for ACL2 source (comments preserved by splicing).
class Node:
    __slots__=('kind','val','start','end','kids','prefix')
    def __init__(s,kind,val,start,end,kids=None,prefix=None):
        s.kind=kind; s.val=val; s.start=start; s.end=end; s.kids=kids; s.prefix=prefix
    def head(s):
        if s.kind=='list' and s.kids and s.kids[0].kind=='atom': return s.kids[0].val.lower()
        return None
    def __repr__(s):
        return f'<{s.kind} {s.val!r} {s.start}:{s.end}>'
DELIM=set('()\'`,"; \t\n\r')
def skip_ws(src,i):
    n=len(src)
    while i<n:
        c=src[i]
        if c in ' \t\n\r\f': i+=1
        elif c==';':
            j=src.find('\n',i); i=n if j<0 else j+1
        elif src.startswith('#|',i):
            depth=1;i+=2
            while depth and i<n:
                if src.startswith('|#',i): depth-=1;i+=2
                elif src.startswith('#|',i): depth+=1;i+=2
                else: i+=1
            if depth: raise ValueError('unterminated block comment')
        else: break
    return i
def read(src,i):
    i=skip_ws(src,i)
    if i>=len(src): return None,i
    c=src[i]
    if c=='(':
        start=i;i+=1;kids=[]
        while True:
            i=skip_ws(src,i)
            if i>=len(src): raise ValueError('eof in list at %d'%start)
            if src[i]==')':
                return Node('list',None,start,i+1,kids),i+1
            if src[i]=='.' and i+1<len(src) and src[i+1] in DELIM:
                kids.append(Node('atom','.',i,i+1)); i+=1; continue
            k,i=read(src,i); kids.append(k)
    if c==')': raise ValueError('unexpected ) at %d'%i)
    if c in "'`" or c==',':
        start=i
        p=c
        if c==',' and i+1<len(src) and src[i+1]=='@': p=',@'
        i+=len(p)
        k,i=read(src,i)
        if k is None: raise ValueError('quote without expression')
        return Node('quote',p,start,i,[k]),i
    if c=='"':
        start=i;i+=1
        while i < len(src) and src[i]!='"':
            i+= 2 if src[i]=='\\' else 1
        if i >= len(src): raise ValueError('unterminated string at %d'%start)
        return Node('atom',src[start:i+1],start,i+1),i+1
    if src.startswith('#\\',i):
        start=i;i+=3
        while i<len(src) and src[i] not in DELIM: i+=1
        return Node('atom',src[start:i],start,i),i
    if src.startswith("#'",i) or src.startswith('#.',i) or src.startswith('#+',i) or src.startswith('#-',i):
        start=i;i+=2
        if src[start+1] in '+-':
            k,i=read(src,i)
        k,i=read(src,i)
        return Node('quote',src[start:start+2],start,i,[k]),i
    start=i
    while i<len(src):
        if src[i]=='|':
            j=src.index('|',i+1); i=j+1; continue
        if src[i]=='\\': i+=2; continue
        if src[i] in DELIM: break
        i+=1
    return Node('atom',src[start:i],start,i),i
def read_all(src):
    out=[];i=0
    while True:
        k,i=read(src,i)
        if k is None: return out
        out.append(k)
