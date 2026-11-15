"""Thread canonical archive and release aggregate through actual holder gates."""
from pathlib import Path
import lisp_rewrite as lr
TABLES=('fn2-event-archive','fn2-release-evidence-candidates')
def rewrite(text):
    parsed=lr.parse(text);targets=[]
    for m in lr.match('(defun ?name ?args ?*body)',parsed.forms,deep=False):
        name=m.captures['name'].low
        if name in ('fn2-checkpoint-dispose-held-p','fn2-cdh-body'):
            targets.append(m.captures['args'])
            for a in lr.match('(xargs ?*before :stobjs ?tables ?*after)',[m.node]):targets.append(a.captures['tables'])
    for name in ('fn2-checkpoint-dispose-held-p','fn2-cdh-body'):
        for m in lr.match('('+name+' ?*args)',parsed.forms):targets.append(m.node)
    for m in lr.match('(fn2-run-with-local ?tables ?body)',parsed.forms):targets.append(m.captures['tables'])
    for m in lr.match('(mv ?*args)',parsed.forms):
        if any(isinstance(a,lr.Atom) and a.low=='fn2-retirement-control' for a in m.node.items):targets.append(m.node)
    edits=[]
    for node in targets:
        existing={a.low for a in node.items if isinstance(a,lr.Atom)}
        add=[t for t in TABLES if t not in existing]
        if add:edits.append((node.end-1,node.end-1,' '+' '.join(add)))
    return lr.write(text,edits),len(edits)
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');args=p.parse_args()
    root=Path(__file__).resolve().parents[1]
    for f in ('books/checkpoint-dispose-holders.lisp','tests/checkpoint-dispose-holders-unit.lisp'):
        path=root/f;out,n=rewrite(path.read_text());print(f,n)
        if args.write:path.write_text(out)
