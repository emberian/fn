"""Extend a known pure child-call cone with explicit readonly source carriers.
Refuses arity drift, ambiguous declarations and missing core projection scopes.
No Lisp is evaluated; carrier values are never computed by Python.
"""
import lisp_rewrite as lr
def walk(n,parents=()):
    if hasattr(n,'items'):
        yield n,parents
        for x in n.items:yield from walk(x,(*parents,n))
def head(n):return getattr(n.items[0],'low','') if hasattr(n,'items') and n.items else ''
def expand(source,plan):
    parsed=lr.parse(source);edits=[];bindings={}
    for form in parsed.forms:
      for n,parents in walk(form):
        h=head(n)
        if h=='defun' and getattr(n.items[1],'low','') in plan:
            name=n.items[1].low;old,extra=plan[name]
            if len(n.items[2].items)!=old:raise ValueError(name+': definition arity drift')
            edits.append((n.items[2].end-1,n.items[2].end-1,' '+' '.join(extra)))
            xargs=[m.node for m in lr.match('(xargs ?*args)',[n])]
            if len(xargs)!=1:raise ValueError(name+': xargs shape')
            xa=xargs[0];props={xa.items[i].low:xa.items[i+1] for i in range(1,len(xa.items),2)}
            so=props[':stobjs'];guard=props[':guard']
            if not hasattr(so,'items') or head(guard)!='and':raise ValueError(name+': explicit carrier/guard shape')
            edits.append((so.end-1,so.end-1,' '+' '.join(extra)))
            edits.append((guard.end-1,guard.end-1,' '+' '.join('('+x+'-wfp '+x+')' for x in extra)))
        elif h in plan:
            old,extra=plan[h]
            if len(n.items)-1!=old:raise ValueError(h+': call arity drift')
            edits.append((n.end-1,n.end-1,' '+' '.join(extra)))
            df=next((a for a in reversed(parents) if head(a)=='defun'),None)
            if df is not None and getattr(df.items[1],'low','') in plan:continue
            # Existing test/core projections receive only missing read children.
            scope=next((a for a in reversed(parents) if head(a)=='stobj-let'),None)
            macro=next((a for a in reversed(parents) if head(a)=='fn2-epv-wrapper'),None)
            formal={x.low for x in df.items[2].items} if df is not None else set()
            if scope is None and macro is None:
                if all(x in formal for x in extra):continue
                raise ValueError(h+': missing projection scope')
            children=scope.items[1] if scope is not None else macro.items[3]
            known={x.low for x in df.items[2].items} if df is not None else set()
            known.update(x.items[0].low for x in children.items)
            for a in parents:
                if head(a)=='with-local-stobj':known.add(a.items[1].low)
            missing=[x for x in extra if x not in known]
            key=(children.start,children.end)
            bindings.setdefault(key,[])
            bindings[key]=list(dict.fromkeys([*bindings[key],*missing]))
        elif h.endswith('-preserves') and len(n.items)>2 and getattr(n.items[1],'low','') in plan:
            name=n.items[1].low;old,extra=plan[name];args=n.items[2]
            if len(args.items)!=old:raise ValueError(name+': preservation signature drift')
            edits.append((args.end-1,args.end-1,' '+' '.join(extra)))
            props={n.items[i].low:n.items[i+1] for i in range(3,len(n.items),2)}
            if ':hyps' in props:
                hyps=props[':hyps'];edits.append((hyps.end-1,hyps.end-1,' '+' '.join('('+x+'p '+x+') ('+x+'-wfp '+x+')' for x in extra)))
    for (start,end),names in bindings.items():
        if names:edits.append((end-1,end-1,' '+' '.join('('+x+' (fn2-core-'+x[4:]+' fn2-core))' for x in names)))
    return lr.write(source,edits)
