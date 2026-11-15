"""Project only the three production cursor-start sites onto the shared Ref ctor."""
from pathlib import Path
import lisp_rewrite as lr

def project(name, source):
    p=lr.parse(source); edits=[]
    target={'machines-c-groups.lisp':'fn2-xl-run-next','machines-c-successor.lisp':'fn2-succ-resolve-next','range.lisp':'fn2-range-advance-run'}[name]
    hits=lr.match('(defun '+target+' ?args ?*body)',p.forms)
    if len(hits)!=1: raise ValueError('missing unique production start '+target)
    fn=hits[0].node
    starts=lr.match('(fn2-run-cursor-start ?*args)',[fn])
    if len(starts)!=1: raise ValueError('expected one resident-only start '+target)
    if name=='machines-c-groups.lisp':
        call='(fn2-run-cursor-start-installed tx r rb qk qs qg fn2-run-installed fn2-run-cursors)'
        args=hits[0].captures['args']; edits.append((args.items[3].start,args.items[3].start,'qk qs qg '))
        shapes=lr.match('(fn2-idc-fn-shape fn2-xl-run-next ?args ?*body)',p.forms)
        if len(shapes)!=1: raise ValueError('missing unique start frame')
        args=shapes[0].captures['args']; edits.append((args.items[3].start,args.items[3].start,'qk qs qg '))
        calls=lr.match('(fn2-xl-run-next tx sid rb ?*args)',p.forms)
        if len(calls)!=1: raise ValueError('missing unique actual XL caller')
        args=calls[0].node.items; edits.append((args[4].start,args[4].start,'qk qs qg '))
    elif name=='machines-c-successor.lisp':
        owner=lambda f,default: f'(if (equal (fn2-succ-slots-oset s fn2-succ-slots) 1) (fn2-succ-slots-{f} s fn2-succ-slots) {default})'
        call='(fn2-run-cursor-start-installed tx r (+ b0 *fn2-idc-rb*) '+owner('sk','*fn2-idc-owner-kind*')+' '+owner('ss','*fn2-idc-owner-slot*')+' '+owner('sg','*fn2-idc-owner-gen*')+' fn2-run-installed fn2-run-cursors)'
    else:
        rb=starts[0].node.items[8]
        call='(fn2-run-cursor-start-installed c r '+source[rb.start:rb.end]+' qk qs qg fn2-run-installed fn2-run-cursors)'
        # Preserve the query SID boundary: constructor derives wire schema from R.
        check=lr.match('((unless (< r (fn2-run-installed-rows fn2-run-installed))) ?*body)',[fn])
        if len(check)!=1: raise ValueError('missing range row bound')
        n=check[0].node.items[0].items[1]
        edits.append((n.start,n.end,'(and (< r (fn2-run-installed-rows fn2-run-installed)) (equal (fn2-run-installed-schema r fn2-run-installed) sid))'))
    edits.append((starts[0].start,starts[0].end,call))
    out=lr.write(source,edits)
    # Opaque frame runes follow the implementation subject; names only.
    # This replacement is deliberately restricted to the changed function/frame.
    for hit in lr.match('(defun '+target+' ?*body)',lr.parse(out).forms):
        sub=out[hit.start:hit.end].replace('(disable fn2-run-cursor-start ','(disable fn2-run-cursor-start-installed ')
        out=out[:hit.start]+sub+out[hit.end:]
    refs=[]
    def walk(n):
        yield n
        if isinstance(n,lr.Lst):
            for a in n.items: yield from walk(a)
        elif isinstance(n,lr.Pre): yield from walk(n.node)
    for f in lr.parse(out).forms:
        for n in walk(f):
            if isinstance(n,lr.Atom) and n.low=='fn2-run-cursor-start':
                refs.append((n.start,n.end,'fn2-run-cursor-start-installed'))
    return lr.write(out,refs)

def check(name, source):
    target={'machines-c-groups.lisp':'fn2-xl-run-next','machines-c-successor.lisp':'fn2-succ-resolve-next','range.lisp':'fn2-range-advance-run'}[name]
    fn=lr.match('(defun '+target+' ?*body)',lr.parse(source).forms)
    if len(fn)!=1 or len(lr.match('(fn2-run-cursor-start-installed ?*args)',[fn[0].node]))!=1 or lr.match('(fn2-run-cursor-start ?*args)',[fn[0].node]):
        raise ValueError('production function must use one shared full Ref constructor')

if __name__=='__main__':
    for name in ['machines-c-groups.lisp','machines-c-successor.lisp','range.lisp']:
        p=Path('books')/name;p.write_text(project(name,p.read_text()))
