"""Append exact retained terminal states/field to the actual master schema."""
from pathlib import Path
import lisp_rewrite as lr
PHASES=(':teardown-dispose-begin',':teardown-dispose-step')
def rewrite(text):
    p=lr.parse(text);edits=[]
    for m in lr.match('(defmachine fn2-checkpoint-master ?*rest)',p.forms,deep=False):
        items=m.node.items
        for i,item in enumerate(items):
            if not isinstance(item,lr.Atom):continue
            if item.low not in (':states',':fields',':arms'):continue
            node=items[i+1]
            if item.low==':fields':
                if not any(isinstance(a,lr.Lst) and a.items and isinstance(a.items[0],lr.Atom) and a.items[0].low=='teardown-debt-generation' for a in node.items):
                    edits.append((node.end-1,node.end-1,' (teardown-debt-generation :u60)'))
            else:
                present={a.low for a in node.items if isinstance(a,lr.Atom)} if item.low==':states' else {a.items[0].low for a in node.items if isinstance(a,lr.Lst) and a.items and isinstance(a.items[0],lr.Atom)}
                add=[phase for phase in PHASES if phase not in present]
                if add:edits.append((node.end-1,node.end-1,' '+' '.join(add if item.low==':states' else ['('+a+')' for a in add])))
    return lr.write(text,edits),len(edits)
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
    f=Path(__file__).resolve().parents[1]/'books/checkpoint-master-state.lisp';s,n=rewrite(f.read_text());print(n)
    if a.write:f.write_text(s)
