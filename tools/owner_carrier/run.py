import sys,collections
sys.path.insert(0,'/private/tmp/claude-501/-Users-ember-dev-fn/adb603dc-e723-4892-b9cd-9db2dc0e97a0/scratchpad/xf')
import xf
D=xf.defs_in('.')
byfile=collections.defaultdict(set)
for n,v in D.items():
    if n in xf.HAND: continue
    byfile[v[0][0]].add(n)
import glob
for f in glob.glob('books/*.lisp')+glob.glob('host/*.lisp')+glob.glob('tests/acl2/*.lisp'):
    byfile.setdefault(f,set())
for it in range(20):
    xf.UNUSED.clear(); xf.FLAGS.clear()
    out={}
    for f,names in byfile.items():
        r=xf.transform_file(f,names)[0]
        if r!=open(f).read(): out[f]=r
    new={n for n in xf.UNUSED if not xf.SIG[n]['entry'] and xf.cls(n)!='M' and 'state' not in xf.new_outs(n)}
    if new<=xf.DROP: break
    xf.DROP|=new
print('iterations',it,'drop',len(xf.DROP),'ignorable left',len(xf.UNUSED-xf.DROP),'flags',xf.FLAGS)
if '--write' in sys.argv:
    for f,s in out.items(): open(f,'w').write(s)
