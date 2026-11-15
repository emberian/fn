"""Thread the real stable-use table through the owning live payload class."""
from pathlib import Path
import lisp_rewrite as lr
PROOF = 'fn2-checkpoint-payload-proofs'
ROOT = Path(__file__).resolve().parents[1]

def append_to(text, lists):
    edits = []
    for node in lists:
        if not any(isinstance(x, lr.Atom) and x.low == PROOF for x in node.items):
            edits.append((node.end-1, node.end-1, ' '+PROOF))
    return lr.write(text, edits), len(edits)

def rewrite(text, stem):
    parsed = lr.parse(text)
    targets = []
    if stem in ('checkpoint-payload-state', 'checkpoint-payload'):
        fn = 'fn2-checkpoint-payload-'+('begin' if stem.endswith('state') else 'step')
        for m in lr.match('(defun '+fn+' ?args ?*body)', parsed.forms, deep=False):
            targets.append(m.captures['args'])
            body = m.node
            for a in lr.match('(xargs ?*before :stobjs ?tables ?*after)', [body]): targets.append(a.captures['tables'])
            if stem.endswith('state'):
                for a in lr.match('(mv ?*args)', [body]): targets.append(a.node)
        for m in lr.match('(fn2-checkpoint-payload-preserves '+fn+' ?args ?*rest)', parsed.forms, deep=False):
            targets.append(m.captures['args'])
        if stem == 'checkpoint-payload':
            for m in lr.match('(defmacro fn2-checkpoint-payload-step-mv ?args ?*rest)', parsed.forms, deep=False):
                for a in lr.match('(mv ?*args)', [m.node]): targets.append(a.node)
    elif stem == 'checkpoint-metadata-driver':
        for m in lr.match('(defconst *fn2-checkpoint-root1-children* ?value)', parsed.forms, deep=False):
            targets.append(m.captures['value'].node)
        for name in ('payload-start', 'closure', 'step'):
            for m in lr.match('(fn2-checkpoint-root1-'+name+' ?*args)', parsed.forms):
                if any(isinstance(a,lr.Atom) and a.low == 'fn2-checkpoint-root1' for a in m.node.items[1:]): targets.append(m.node)
        for name in ('begin','step'):
            for m in lr.match('(fn2-checkpoint-payload-'+name+' ?*args)', parsed.forms): targets.append(m.node)
        for m in lr.match('((mv ?*outs) ?call)', parsed.forms):
            call=m.captures['call']
            if isinstance(call,lr.Lst) and call.items and isinstance(call.items[0],lr.Atom) and call.items[0].low in ('fn2-checkpoint-payload-begin','fn2-checkpoint-payload-step'):
                targets.append(m.node.items[0])
    return append_to(text, targets)



def typed_guards(text):
    """Add TYPE beside shape in this actual helper domain, not its claims."""
    parsed=lr.parse(text);edits=[]
    for m in lr.match('(xargs ?*before :guard ?guard ?*after)', parsed.forms):
        guard=m.captures['guard']
        if not isinstance(guard,lr.Lst) or not guard.items or not isinstance(guard.items[0],lr.Atom) or guard.items[0].low!='and':continue
        for term in guard.items[1:]:
            if not isinstance(term,lr.Lst) or len(term.items)!=2:continue
            head,arg=term.items
            if not isinstance(head,lr.Atom) or not head.low.endswith('-wfp') or not isinstance(arg,lr.Atom):continue
            pred=head.text[:-4]+'p'
            if any(isinstance(t,lr.Lst) and len(t.items)==2 and isinstance(t.items[0],lr.Atom) and t.items[0].low==pred.lower() for t in guard.items):continue
            edits.append((term.start,term.start,'('+pred+' '+arg.text+') '))
    return lr.write(text,edits),len(edits)


def preservation(text, name, outputs, extra_args=()):
    """Generate contracts from actual defun input carriers; retain readonly P/WFP."""
    parsed=lr.parse(text)
    match=lr.match('(defun '+name+' ?args ?*body)',parsed.forms,deep=False)[0]
    args=text[match.captures['args'].start:match.captures['args'].end]
    decl=lr.match('(xargs ?*before :stobjs ?tables ?*after)',[match.node])[0]
    tables=[a.text for a in decl.captures['tables'].items]
    hyps='\n        '.join('('+t+'p '+t+') ('+t+'-wfp '+t+')' for t in tables)
    specs=[]
    for table,pos in outputs:
        prefix='-'+table[4:].upper()
        specs.extend(['("'+prefix+'-TYPE" '+table+'p '+str(pos)+')',
                      '("'+prefix+'-WFP" '+table+'-wfp '+str(pos)+')',
                      '("'+prefix+'-ROWS" '+table+'-rows '+str(pos)+' :frame '+table+')'])
        if table==PROOF:specs.append('("'+prefix+'-HASHES" '+table+'-hashes-length '+str(pos)+' :frame '+table+')')
    return '\n(fn2-checkpoint-payload-proofs-preserves '+name+'\n '+args+'\n :hyps ('+hyps+')\n :specs ('+'\n         '.join(specs)+'))\n'


if __name__ == '__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--write', action='store_true');args=p.parse_args()
    for stem in ('checkpoint-payload-state','checkpoint-payload','checkpoint-metadata-driver',
                 'checkpoint-payload-proof-state','checkpoint-payload-proof'):
        path=ROOT/'books'/(stem+'.lisp');text=path.read_text()
        out,n=rewrite(text,stem)
        if stem!='checkpoint-metadata-driver':
            out,typed=typed_guards(out);n+=typed
        print(stem,n)
        if args.write:path.write_text(out)
