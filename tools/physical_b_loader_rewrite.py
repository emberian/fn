"""Append physical-loader stripes without replacing current B declarations."""
from pathlib import Path
import json
import lisp_rewrite as lr
DATA=json.loads((Path(__file__).parent/'fixtures/physical-b-loader-geometry.json').read_text())
def named(text,name):
    found=[x for x in lr.parse(text).forms if isinstance(x,lr.Lst) and len(x.items)>1 and getattr(x.items[1],'low','')==name]
    if len(found)!=1:raise ValueError('one actual B event '+name)
    return found[0]
def project_loader_prefix(text):
    """Consume the target's actual sealer map, including canonical paired2W."""
    helper=lr.match('(defun fn2-b-sealer-hash-row ?*args)',lr.parse(text).forms,deep=False)
    if len(helper)>1:raise ValueError('duplicate actual sealer row provider')
    sealer='(fn2-b-sealer-hash-row profile)' if helper else '(+ 3 (fn2-b-upload-windows profile))'
    n=named(text,'fn2-b-run-loader-row');body=n.items[-1]
    expected='(+ 1 '+sealer+' (nfix cursor))'
    if helper and n.start<helper[0].node.start:
        # Canonical paired2W defines its sealer map after upload contexts.
        # Move only this generated consumer beyond that actual provider.
        replacement=text[n.start:body.start]+expected+text[body.end:n.end]
        return lr.write(text,[(n.start,n.end,''),(helper[0].node.end,helper[0].node.end,'\n'+replacement)])
    return lr.write(text,[(body.start,body.end,expected)])
def project(text):
    if '(defun fn2-b-run-loader-row ' in text:return project_loader_prefix(text)
    # Existing read geometry is needed by the new format floor. Move exactly
    # these original events ahead of format allocation, not a later forward
    # reference copied from a historical B file.
    names=['fn2-b-cursor-rows','fn2-b-cns-rows','fn2-b-auth-rows','fn2-b-read-rows',
           'fn2-b-cursor-rows-natp','fn2-b-cns-rows-natp','fn2-b-auth-rows-natp','fn2-b-read-rows-natp']
    moved=[];edits=[]
    for name in names:
        n=named(text,name);moved.append(text[n.start:n.end]);edits.append((n.start,n.end,''))
    text=lr.write(text,edits)
    anchor=named(text,'fn2-b-upload-windows')
    events=DATA['new_events'];addition='\n'.join(moved)+'\n\n(defconst *fn2-b-query-read-rows* 2)\n'
    addition+='\n'.join(v for k,v in events.items() if k!='fn2-b-run-loader-row')+'\n\n'
    text=lr.write(text,[(anchor.start,anchor.start,addition)])
    anchor=named(text,'fn2-b-upload-windows')
    text=lr.write(text,[(anchor.end,anchor.end,'\n'+events['fn2-b-run-loader-row']+'\n')])
    edits=[]
    for name in ('fn2-b-ctl-slot','fn2-b-format-floor'):
        n=named(text,name);body=n.items[-1]
        if getattr(body.items[0],'low','')!='+':raise ValueError('additive current format geometry '+name)
        edits.append((body.end-1,body.end-1,' (fn2-b-run-cursor-rows profile)'))
    text=lr.write(text,edits)
    old='(include-book "profile")'
    if text.count(old)!=1:raise ValueError('one actual profile dependency')
    return project_loader_prefix(text.replace(old,old+'\n(include-book "run-active-geometry")',1))

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('file',type=Path);a=p.parse_args();a.file.write_text(project(a.file.read_text()))
