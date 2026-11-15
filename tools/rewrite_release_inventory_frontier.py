"""Thread one canonical captured inventory through the actual frontier face."""
from pathlib import Path
import lisp_rewrite as lr
NAME='fn2-checkpoint-restore-events-frontier-step'
TABLE='fn2-checkpoint-restore-release-inventory'
OUTPUTS=('fn2-checkpoint-restore-reader','fn2-checkpoint-restore-events','fn2-checkpoint-restore-reach','fn2-fc','fn2-fc-context','fn2-b3','fn2-fields','fn2-pool','fn2-digests')
def append(node,text,edits):
    if TABLE not in [x.low for x in node.items if isinstance(x,lr.Atom)]:edits.append((node.end-1,node.end-1,' '+text))
def rewrite(text):
    parsed=lr.parse(text);edits=[]
    for match in lr.match('(defun '+NAME+' ?args ?*body)',parsed.forms,deep=False):
        append(match.captures['args'],TABLE,edits)
        for x in lr.match('(xargs ?*before :stobjs ?tables ?*after)',[match.node]):append(x.captures['tables'],TABLE,edits)
        for x in lr.match('(xargs ?*before :guard ?guard ?*after)',[match.node]):
            g=x.captures['guard']
            if TABLE+'p' not in text[g.start:g.end]:edits.append((g.end-1,g.end-1,' ('+TABLE+'p '+TABLE+') ('+TABLE+'-wfp '+TABLE+')'))
        for x in lr.match('(mv ?code ?*values)',[match.node]):
            values=x.captures['values']
            if [a.low for a in values if isinstance(a,lr.Atom)]==list(OUTPUTS):edits.append((x.node.end-1,x.node.end-1,' '+TABLE))
    for match in lr.match('(fn2-checkpoint-restore-events-preserves '+NAME+' ?args ?*rest)',parsed.forms,deep=False):
        append(match.captures['args'],TABLE,edits)
        items=match.node.items
        for key in (':hyps',':specs'):
            at=next(i for i,a in enumerate(items) if isinstance(a,lr.Atom) and a.low==key);node=items[at+1]
            if TABLE in text[node.start:node.end]:continue
            extra=('('+TABLE+'p '+TABLE+') ('+TABLE+'-wfp '+TABLE+')' if key==':hyps' else
                   '("-RELEASE-INVENTORY-TYPE" '+TABLE+'p 10) ("-RELEASE-INVENTORY-WFP" '+TABLE+'-wfp 10) ("-RELEASE-INVENTORY-ROWS" '+TABLE+'-rows 10 :frame '+TABLE+')')
            edits.append((node.end-1,node.end-1,' '+extra))
    for match in lr.match('(defcost fn2-boot-checkpoint-events-frontier-step ?*rest)',parsed.forms,deep=False):
        items=match.node.items;at=next(i for i,a in enumerate(items) if isinstance(a,lr.Atom) and a.low==':tables');node=items[at+1]
        core='fn2-core-'+TABLE[4:]
        if core not in [a.low for a in node.items if isinstance(a,lr.Atom)]:edits.append((node.end-1,node.end-1,' '+core))
    return lr.write(text,edits),len(edits)
if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    root=Path(__file__).resolve().parents[1]
    for name in ('checkpoint-restore-events','checkpoint-restore-events-boot'):
        path=root/'books'/(name+'.lisp');out,count=rewrite(path.read_text());print(name,count)
        if args.write:path.write_text(out)
