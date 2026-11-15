"""Wire pending intake into the actual root1 family, preserving projections."""
from pathlib import Path
import lisp_rewrite as lr

def rewrite(source):
    forms=lr.parse(source).forms
    if lr.match('(fn2-checkpoint-summary-live-begin ?*args)',forms):raise ValueError('already wired')
    edits=[]
    # Change declared mutable outputs; the family generator drains call/MV ABI.
    for name,carrier in [('fn2-checkpoint-root1-begin','fn2-checkpoint-summary'),('fn2-checkpoint-root1-work','fn2-checkpoint-summary-sources'),('fn2-checkpoint-root1-step','fn2-checkpoint-summary-sources')]:
        candidates=[m.node for m in lr.match(f'({name} ?*args)',forms) if all(hasattr(x,'low') for x in m.node.items)]
        rows=[n for n in candidates if len(n.items)>2 and n.items[1].low=='fn2-checkpoint-root1']
        if len(rows)!=1:raise ValueError('output declaration missing '+name)
        n=rows[0];edits.append((n.items[-1].end,n.items[-1].end,' '+carrier))
    begin=lr.match('(fn2-checkpoint-root1-operation fn2-checkpoint-root1-begin ?*body)',forms,deep=False)[0].node
    borrow=lr.match('((mv code fn2-run-loads) (fn2-checkpoint-source-reader-borrow ?*args))',[begin])[0].node
    edits.append((borrow.start,borrow.start,'''((mv code fn2-checkpoint-summary)
       (fn2-checkpoint-summary-live-begin token kind owner gen fn2-checkpoint-summary fn2-checkpoint-build fn2-csnapshot))
      ((unless (eq code :ok)) (fn2-checkpoint-root1-mv code))
      '''))
    work=lr.match('(fn2-checkpoint-root1-operation fn2-checkpoint-root1-work ?*body)',forms,deep=False)[0].node
    emit=lr.match('((mv ?*outputs) (fn2-checkpoint-metadata-manifest-emit ?*args))',[work])[0].node
    edits.append((emit.end,emit.end,'''
         ((when (eq code :ok))
          (b* (((mv captured fn2-checkpoint-summary fn2-checkpoint-summary-sources)
                (fn2-checkpoint-summary-live-record fn2-checkpoint-summary fn2-checkpoint-summary-sources
                 fn2-checkpoint-build fn2-csnapshot fn2-checkpoint-source fn2-checkpoint-metadata-manifest fn2-fields fn2-pool))
               (fn2-checkpoint-root1 (if (eq captured :captured)
                 (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-select* fn2-checkpoint-root1)
                 (fn2-checkpoint-root1-set-phase 0 *fn2-checkpoint-root1-phase-uncertain* fn2-checkpoint-root1))))
           (fn2-checkpoint-root1-mv (if (eq captured :captured) :more captured))))'''))
    result=lr.write(source,edits)
    return result.replace('(include-book "checkpoint-source-loader")','(include-book "checkpoint-source-loader")\n(include-book "checkpoint-summary-live-catalog")')
if __name__=='__main__':
    p=Path(__file__).resolve().parents[1]/'books/checkpoint-metadata-driver.lisp'
    p.write_text(rewrite(p.read_text()))
