"""Move the existing atomic three-edge tail behind source-specific admission."""
import lisp_rewrite as lr

def extract(source):
    found=lr.match('(defun fn2-release-evidence-claim-children ?*body)',lr.parse(source).forms,deep=False)
    if len(found)!=1:raise ValueError('expected actual live evidence admission')
    fn=found[0].node;body=fn.items[-1]
    if getattr(body.items[0],'low','')!='b*':raise ValueError('expected actual binding body')
    bindings=body.items[1].items
    points=[]
    for i,b in enumerate(bindings):
        lhs=b.items[0]
        if hasattr(lhs,'items') and len(lhs.items)>1 and getattr(lhs.items[0],'low','')=='mv' and getattr(lhs.items[1],'low','')=='pair':points.append(i)
    if len(points)!=1:raise ValueError('expected one atomic ownership tail')
    at=points[0]
    prefix='\n'.join(source[b.start:b.end] for b in bindings[:at])
    tail='\n'.join(source[b.start:b.end] for b in bindings[at:])
    result=source[body.items[2].start:body.items[2].end]
    if tail.count('fn2-alloc-edge-add-transition')!=3:raise ValueError('three actual edge mutations changed')
    return fn,prefix,tail,result
