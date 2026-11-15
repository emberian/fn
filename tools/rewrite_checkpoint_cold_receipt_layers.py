"""Move exact shared generator/receipt definitions to lower B books, no twins."""
from pathlib import Path
import lisp_rewrite as lr
CLASSES=(
 ('checkpoint-metadata-driver','checkpoint-child-contracts',('columns',),
  ('fn2-checkpoint-root1-child-hyps','fn2-checkpoint-root1-child-tables','fn2-checkpoint-root1-child-specs')),
 ('checkpoint-bank-cold','checkpoint-bank-cold-state',('checkpoint-publication-state',),
  ('fn2-checkpoint-bank-cold-capacityp','fn2-checkpoint-bank-cold-ready-p',
   'fn2-checkpoint-bank-cold-snapshot','fn2-checkpoint-bank-cold-event','fn2-checkpoint-bank-cold-word')),
 ('checkpoint-bank-protection','checkpoint-bank-protection-state',('checkpoint-bank-closure-state',),
  ('fn2-checkpoint-bank-protection','fn2-checkpoint-bank-protection-source-word','fn2-checkpoint-bank-protection-sources-p')))

def extract(text,names,lower,includes):
    parsed=lr.parse(text); selected=[]
    for name in names:
        matches=lr.match('(?head '+name+' ?*rest)',parsed.forms,deep=False,
                         where=lambda m:m.captures['head'].low in ('defun','defcolumns'))
        if len(matches)!=1:raise ValueError((name,len(matches)))
        selected.append(matches[0])
    selected.sort(key=lambda m:m.start)
    leaf='; Canonical readonly cold evidence/receipt definitions, shared by boot\n; and terminal disposal. No capture, selection, mutation or readiness input.\n(in-package "ACL2")\n'
    leaf+=''.join('(include-book "'+i+'")\n' for i in includes)
    leaf+='(fn2-book-layer :b)\n\n'+'\n\n'.join(text[m.start:m.end] for m in selected)+'\n'
    edits=[(m.start,m.end,'') for m in selected]
    package=lr.match('(in-package ?name)',parsed.forms,deep=False)[0]
    edits.append((package.end,package.end,'\n(include-book "'+lower+'")'))
    return lr.write(text,edits),leaf

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');p.add_argument('--only');args=p.parse_args()
    root=Path(__file__).resolve().parents[1]/'books'
    for high,low,includes,names in CLASSES:
        if args.only and high!=args.only:continue
        path=root/(high+'.lisp');out,leaf=extract(path.read_text(),names,low,includes)
        print(high,'->',low,len(names))
        if args.write:
            if (root/(low+'.lisp')).exists():raise ValueError('refuse overwrite '+low)
            path.write_text(out);(root/(low+'.lisp')).write_text(leaf)
