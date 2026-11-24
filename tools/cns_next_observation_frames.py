"""Request distinct-column frames for the actual sequential NEXT PUT bindings."""
from lisp_rewrite import Atom,Lst,match,parse,write
TABLE='fn2-cns-sources'
PREFIX=TABLE+'-'
def atom(n,s):return isinstance(n,Atom) and n.low==s
def pairs(text):
    p=parse(text)
    fs=[m.node for m in match(None,p,deep=False,head='defun') if m.node.items[1].low=='fn2-cns-source-next-children']
    assert len(fs)==1
    roots=[m.node.items[1] for m in match(None,fs,deep=True,head=TABLE) if len(m.node.items)==2 and isinstance(m.node.items[1],Lst) and atom(m.node.items[1].items[0],'let*')]
    assert len(roots)==1,'expected the actual final sequential table binding'
    out=set()
    def walk(n,dirty):
        if not isinstance(n,Lst) or not n.items:return set(dirty)
        xs=n.items;head=xs[0].low if isinstance(xs[0],Atom) else ''
        if head=='let*':
            state=set(dirty)
            for binding in xs[1].items:
                changed=walk(binding.items[1],state)
                if atom(binding.items[0],TABLE):state=changed
            for body in xs[2:]:walk(body,state)
            return state
        if head==PREFIX+'put':
            state=set(dirty);assert atom(xs[1],'s')
            for assignment in xs[2:]:
                assert isinstance(assignment,Lst) and len(assignment.items)==2
                walk(assignment.items[1],state);state.add(assignment.items[0].low)
            return state
        if head=='if':
            walk(xs[1],dirty)
            return walk(xs[2],dirty)|walk(xs[3],dirty)
        if head.startswith(PREFIX) and len(xs)==3 and atom(xs[-1],TABLE):
            assert atom(xs[1],'s'),'only actual same-row reads are supported'
            reader=head[len(PREFIX):]
            out.update((reader,w) for w in dirty if reader!=w)
        for x in (xs[1:] if isinstance(xs[0],Atom) else xs):walk(x,dirty)
        return set(dirty)
    walk(roots[0],set())
    return sorted(out)
def declaration(r,w):return f'(defcolumns-observation-frame {PREFIX}{r}-after-{w} {TABLE} {r} {w})'
def transform(text):
    expected=pairs(text);p=parse(text)
    existing=[m.node for m in match(None,p,deep=False,head='defcolumns-observation-frame') if m.node.items[1].low!=PREFIX+'hash-offset-after-unit-hashed']
    if existing:
        assert [text[n.start:n.end] for n in existing]==[declaration(*x) for x in expected],'requested frame inventory differs'
        return text,0
    fn=next(m.node for m in match(None,p,deep=False,head='defun') if m.node.items[1].low=='fn2-cns-source-next-children')
    return write(text,[(fn.start,fn.start,'\n'.join(declaration(*x) for x in expected)+'\n\n')]),len(expected)
if __name__=='__main__':
    import sys
    from pathlib import Path
    path=Path(sys.argv[1]);text,n=transform(path.read_text());path.write_text(text);print(n)
