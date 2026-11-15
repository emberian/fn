"""Generate the actual allocator's bounded LIVE identity-index carrier fields.

This transformation edits defcolumns and its actual initializer/freeze gate;
it never evaluates Lisp or supplies an allocator decision.
"""
from pathlib import Path
import sys
import lisp_rewrite as lr

SCALARS = [
 ('active',1,'Recovery owns the LIVE index and closes ordinary physical mutation while it is maintained.'),
 ('phase',8,'Private clear/idle/probe/ready/refused lookup continuation; not persisted authority.'),
 ('owner-kind',8,'Actual reconstruction owner kind retaining the index.'),
 ('owner-slot',32,'Actual reconstruction owner row retaining the index.'),
 ('owner-gen',60,'Rejects a recycled reconstruction owner.'),
 ('source-generation',60,'Exact authenticated source investigation bound to every pending operation.'),
 ('op',8,'Private adopt/free/check/insert operation whose receipt is being prepared.'),
 ('extent',32,'Exact target extent of the pending LIVE identity operation.'),
 ('previous',32,'Actual free-chain predecessor passed to the shared adopt transition.'),
 ('old-state',8,'Actual target state captured before probing and rechecked before mutation.'),
 ('old-epoch',60,'Actual target epoch captured before probing.'),
 ('old-counter',60,'Actual target allocation counter captured before probing.'),
 ('new-state',8,'Exact expected state after the original allocator or projection transition.'),
 ('new-epoch',60,'Exact expected epoch after the original transition.'),
 ('new-counter',60,'Exact expected allocation counter after the original transition.'),
 ('cut',60,'Caller-derived persisted coverage cut rechecked by the shared release preflight; never durability evidence.'),
 ('probe',32,'Next actual bucket to inspect; one bucket per executable step.'),
 ('visited',32,'Number of buckets already inspected in this full bounded probe.'),
 ('tombstone',32,'First reusable tombstone in this probe, or the allocator absent sentinel.'),
 ('bucket',32,'Exact admitted bucket bound to the ready pending tuple.'),
 ('count',32,'Number of USED buckets, equal to current nonFREE identities at stable boundaries.'),
]
ARRAYS = [
 ('states',2,'Explicit EMPTY/USED/TOMBSTONE states; identity zero/zero is never an empty marker.'),
 ('epochs',60,'One LIVE identity epoch per bucket; capacity derives exactly from extent rows.'),
 ('counters',60,'One LIVE allocation counter per bucket, including zero.'),
 ('extents',32,'The unique extent named by each USED epoch/counter key.'),
]

def specs():
    result = []
    for name,bits,why in SCALARS:
        result.append(f'(fn2-alloc-identity-{name} :type (unsigned-byte {bits}) :initially 0 :why "{why}")')
    for name,bits,why in ARRAYS:
        result.append(f'(fn2-alloc-identity-{name} :type (array (unsigned-byte {bits}) (0)) :initially 0 :resizable t :why "{why}")')
    return result

def rewrite(source):
    forms=lr.parse(source).forms
    cols=lr.match('(defcolumns fn2-extents ?*body)',forms,deep=False)[0].node
    pos=next(i for i,x in enumerate(cols.items) if isinstance(x,lr.Atom) and x.low==':extra-fields')
    extras=cols.items[pos+1]
    old={x.items[0].low:x for x in extras.items if isinstance(x,lr.Lst) and x.items}
    present=[name for name in old if name.startswith('fn2-alloc-identity-')]
    if present:
        for spec in specs():
            name=lr.parse(spec).forms[0].items[0].low
            if name not in old or not lr.match(spec,[old[name]],deep=False):
                raise ValueError('existing identity field differs: '+name)
        if len(present)!=len(specs()): raise ValueError('unexpected identity field')
        return source
    addition='\n   '+'\n   '.join(specs())
    source=source[:extras.end-1]+addition+source[extras.end-1:]
    needle='(fn2-extents (fn2-alloc-columns-init n fn2-extents))'
    if source.count(needle)!=1: raise ValueError('actual allocator initializer changed')
    init='\n         '+'\n         '.join(
        [f'(fn2-extents (resize-fn2-alloc-identity-{name} n fn2-extents))' for name,_,_ in ARRAYS]
        +[f'(fn2-extents (update-fn2-alloc-identity-{name} 0 fn2-extents))' for name in ('active','phase','op','count')])
    source=source.replace(needle,needle+init,1)
    frozen='(not (equal (fn2-alloc-freeze-phase fn2-extents) 0)))'
    if source.count(frozen)!=1: raise ValueError('actual allocator freeze gate changed')
    source=source.replace(frozen,'(or (not (equal (fn2-alloc-freeze-phase fn2-extents) 0))\n     (equal (fn2-alloc-identity-active fn2-extents) 1)))',1)
    lr.parse(source)
    return source

if __name__=='__main__':
    path=Path(sys.argv[1] if len(sys.argv)>1 else 'books/alloc.lisp')
    path.write_text(rewrite(path.read_text()))
