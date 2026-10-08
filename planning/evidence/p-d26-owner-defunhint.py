#!/usr/bin/env python3.12
"""Add termination and guard hints (minimal theory + used runes) to named defuns that have none.
usage: defunhint.py BOOK LOG OUT name1,name2,..."""
import sys,re
import importlib.util,os
_spec=importlib.util.spec_from_file_location('minthy',os.path.join(os.path.dirname(os.path.abspath(__file__)),'p-d26-owner-minthy.py'))
minthy=importlib.util.module_from_spec(_spec);_spec.loader.exec_module(minthy)
book,logf,out,names=sys.argv[1:5]
names=names.split(',')
src=open(book).read()
res=minthy.parse_log(open(logf).read())
forms=minthy.scan_forms(src)
edits=[]
for s,e,t in forms:
    m=re.match(r'\(defun (\S+)',t)
    if not m or m.group(1) not in names: continue
    nm=m.group(1)
    info=[i for i in res.values() if i['name']==nm][0]
    if ':hints' in t or ':guard-hints' in t: print('skip (has hints)',nm); continue
    rl=minthy.parse_runes(info['rules'])
    runes=[minthy.rune_text(r) for r in rl if isinstance(r,list)]
    runes=[r for r in runes if r and not re.match(r'\((:definition|:induction|:type-prescription|:executable-counterpart) '+re.escape(nm)+r'[ )]',r)]
    lines=[];cur=''
    for r in sorted(runes):
        if len(cur)+len(r)+1>62 and cur: lines.append(cur);cur=r
        else: cur=(cur+' '+r) if cur else r
    if cur: lines.append(cur)
    ind=' '*6
    th="(union-theories (theory 'minimal-theory)\n"+ind+"'("+('\n'+ind+' ').join(lines)+"))"
    tn=nm+'-hint-rules'
    deft='(local\n (deftheory '+tn+'\n  '+th+'))\n\n'
    hint='(("Goal" :in-theory (theory (quote '+tn+'))))'
    selfr=[r for r in sorted(rr for rr in [minthy.rune_text(x) for x in rl if isinstance(x,list)] if rr) if re.match(r'\((:definition|:induction|:type-prescription|:executable-counterpart) '+re.escape(nm)+r'[ )]',r)]
    ghint='(("Goal" :in-theory (union-theories (theory (quote '+tn+'))\n                                  (quote ('+' '.join(selfr)+')))))'

    dm=re.search(r'\(declare \(xargs',t)
    if not dm: print('no xargs',nm); continue
    xs=dm.start()+len('(declare ')
    xe=minthy.end_of(t,xs)
    new=deft+t[:xe-1]+'\n                  :hints '+hint+'\n                  :guard-hints '+ghint+t[xe-1:]
    edits.append((s,e,new,nm))
o=src
for s,e,new,nm in sorted(edits,reverse=True):
    o=o[:s]+new+o[e:]
open(out,'w').write(o)
print([x[3] for x in edits])
