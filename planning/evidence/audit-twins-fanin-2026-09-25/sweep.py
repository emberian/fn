import os
import sys,re,json,pickle,glob
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from split import *
R=ROOT
FUN={'defun','defund','defun-sk','define','defmacro','defun-nx','defund-nx','defabbrev','defn','defnd','defconst','defstub'}
THM={'defthm','defthmd','defrule','defruled'}
defs={}   # name -> (book,line,kind)
fbody={}  # name -> tokens
thms={}   # name -> (book,line,tokens)
allfiles=sorted(glob.glob(str(R/'books/*.lisp')))+sorted(glob.glob(str(R/'host/*.lisp')))+sorted(glob.glob(str(R/'tests/acl2/*.lisp')))
filetoks={}
for f in allfiles:
    rel=f[len(str(R))+1:-5]
    try: fs=forms(Path(f))
    except Exception as e: print('parse fail',rel,e,file=sys.stderr); continue
    ft=set()
    for sl,el,t in fs:
        m=DEFH.match(t)
        tk=set(x.lower() for x in TOK.findall(strip(t)))
        ft|=tk
        if not m: continue
        k=m.group(1).lower(); n=m.group(2).lower()
        if k in FUN and rel.startswith('books/'): defs[n]=(rel,sl,k); fbody[n]=tk
        elif k in FUN: fbody.setdefault(n,tk)
        if k in THM: thms[n]=(rel,sl,tk)
        if k in FUN and not rel.startswith('books/'):
            fbody[rel+'::'+n]=tk
    filetoks[rel]=ft
native={}
for f in glob.glob(str(R/'host/native/*.lisp')):
    s=re.sub(r';[^\n]*','',Path(f).read_text(errors='replace'))
    for x in TOK.findall(s): native.setdefault(x.lower(),set()).add(f[len(str(R))+1:])
tools=set()
for f in glob.glob(str(R/'tools/*.py')):
    tools|=set(x.lower() for x in TOK.findall(Path(f).read_text(errors='replace')))
ev=json.load(open(R/'planning/proof-events.json'))['targets']
cited={e['name'].lower() for t in ev for e in t['events'] if e.get('kind')=='theorem'}
# callers
callers={n:set() for n in defs}
for fn,tk in fbody.items():
    for n in tk & defs.keys():
        base=fn.split('::')[-1]
        if base!=n: callers[n].add(fn)
thmusers={n:set() for n in defs}
for tn,(b,l,tk) in thms.items():
    for n in tk & defs.keys(): thmusers[n].add(tn)
out={}
for n,(b,l,k) in defs.items():
    hostbooks=sorted({f for f in filetoks if f.startswith('host/') and n in filetoks[f]})
    out[n]=dict(book=b,line=l,kind=k,callers=sorted(callers[n]),thms=len(thmusers[n]),cited=sorted(t for t in thmusers[n] if t in cited),
               native=sorted(native.get(n,())),hostbooks=hostbooks,tools=n in tools,
               tests=sorted(f for f in filetoks if f.startswith('tests/') and n in filetoks[f]))
json.dump(dict(fun=out,cited=sorted(cited),bydef=[(t,thms[t][0],thms[t][1],t in cited) for t in thms if 'by-definition' in t or t.endswith('-unfolds')]),open(SP+'sweep.json','w'))
dead=[n for n,o in out.items() if o['kind']!='defconst' and not o['callers'] and not o['native'] and not o['hostbooks'] and not o['cited']]
orph=[n for n in dead if out[n]['thms']==0 and not out[n]['tests'] and not out[n]['tools']]
print('defs',len(out),'cited thms',len(cited),'dead(no caller/host/cited)',len(dead),'orphan',len(orph))
print('bydef',len(json.load(open(SP+'sweep.json'))['bydef']))
# liveness: roots = native refs, host-book refs, cited theorem mentions
live=set(n for n,o in out.items() if o['native'] or o['hostbooks'] or o['cited'])
for fn,tk in fbody.items():
    if fn.startswith('host/'): live |= (tk & defs.keys())
# also consts used anywhere live -> treated by closure
work=list(live)
while work:
    f=work.pop()
    for m in (fbody.get(f,set()) & defs.keys()):
        if m not in live: live.add(m); work.append(m)
deadset=[n for n in out if n not in live and out[n]['kind'] not in ('defconst',)]
from collections import defaultdict
byb=defaultdict(list)
for n in deadset: byb[out[n]['book']].append(n)
aff=g['aff']
rows=sorted(((aff.get(b,0),b,len(v)) for b,v in byb.items()))
json.dump(dict(dead={b:sorted(v) for b,v in byb.items()}),open(SP+'dead.json','w'))
print('live',len(live),'dead',len(deadset),'books',len(byb))
for a,b,c in rows: print(a,b,c, sorted(byb[b])[:6])
