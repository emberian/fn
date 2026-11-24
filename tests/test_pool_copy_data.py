"""Actual-body bounded controls; these are not kernel admission claims."""
from pathlib import Path
from fractions import Fraction
import copy,itertools,subprocess,sys,unittest
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'tools'))
from lisp_rewrite import parse,match,Lst,Atom,Pre,flat
BASE='ebce9812bf97ea5222a855755aa22e0e9918d2fa'
def tree(n):
 if isinstance(n,Lst):return [tree(x) for x in n.items]
 if isinstance(n,Pre):return ['quote',tree(n.node)]
 try:return int(n.text)
 except ValueError:return n.low

def nat(x):return type(x) is int and x>=0
def nfix(x):return x if nat(x) else 0
def truth(x):return x is not None and x is not False
def nth(i,xs):
 i=nfix(i);return xs[i] if isinstance(xs,list) and i<len(xs) else None
def update(i,v,xs):
 i=nfix(i);out=list(xs) if isinstance(xs,list) else [];out.extend([None]*max(0,i+1-len(out)));out[i]=v;return out

class Actual:
 def __init__(self):
  pool=parse(ROOT/'books/pool.lisp');decl=tree(match(None,pool,deep=False,head='defcolumns')[0].node)
  self.cols={x[0]:i for i,x in enumerate(decl[2])};self.rows=len(self.cols);self.data=self.rows+1
  self.constants={'t':True,'nil':None}
  for field,typ in decl[2]:
   if isinstance(typ,list) and typ[0]==':enum':self.constants.update({f'*{typ[1]}-{x[1:]}*':i for i,x in enumerate(typ[2])})
  self.functions={}
  for p in (pool,parse(ROOT/'books/pool-copy.lisp')):
   for m in match(None,p,deep=False,head='defun'):
    f=tree(m.node);self.functions[f[1]]=(f[2],f[-1])
 def call(self,name,*args):
  names,body=self.functions[name];assert len(names)==len(args);return self.ev(body,dict(zip(names,args)))
 def ev(self,x,env):
  if not isinstance(x,list):
   if type(x) is not str:return x
   if x.startswith(':'):return x
   return self.constants[x] if x in self.constants else env[x]
  op,*a=x
  if op=='quote':return a[0]
  if op=='if':return self.ev(a[1] if truth(self.ev(a[0],env)) else a[2],env)
  if op=='cond':
   for case in a:
    if truth(self.ev(case[0],env)):return self.ev(case[1],env)
   return None
  if op in ('let','let*'):
   local=env.copy()
   for k,v in a[0]:local[k]=self.ev(v,local if op=='let*' else env)
   return self.ev(a[-1],local)
  if op=='b*':
   local=env.copy()
   for pattern,value in a[0]:
    if isinstance(pattern,list) and pattern[0] in ('unless','when'):
     yes=truth(self.ev(pattern[1],local))
     if yes==(pattern[0]=='when'):return self.ev(value,local)
    else:
     result=self.ev(value,local)
     if isinstance(pattern,list):
      assert pattern[0]=='mv'
      for k,v in zip(pattern[1:],result):local[k]=v
     else:local[pattern]=result
   return self.ev(a[-1],local)
  if op in ('and','or'):
   values=[truth(self.ev(v,env)) for v in a];return all(values) if op=='and' else any(values)
  if op=='not':return not truth(self.ev(a[0],env))
  values=[self.ev(v,env) for v in a]
  if op in ('equal','eq','='):return values[0]==values[1]
  if op=='natp':return nat(values[0])
  if op=='unsigned-byte-p':return nat(values[1]) and values[1]<2**values[0]
  if op=='zp':return not nat(values[0]) or values[0]==0
  if op in ('<','<='):return values[0]<values[1] if op=='<' else values[0]<=values[1]
  if op=='+':return sum(values)
  if op=='-':return -values[0] if len(values)==1 else values[0]-values[1]
  if op=='max':return max(values)
  if op=='mv':return tuple(values)
  if op=='fn2-pool-rows':return nth(self.rows,values[0])
  if op=='fn2-pool-data-length':return len(nth(self.data,values[0]) or [])
  if op=='fn2-pool-datai':return nth(values[0],nth(self.data,values[1]))
  if op=='update-fn2-pool-datai':return update(self.data,update(values[0],values[1],nth(self.data,values[2])),values[2])
  if op.startswith('fn2-pool-set-'):
   field=op[len('fn2-pool-set-'):];i,v,pool=values;return update(self.cols[field],update(i,v,nth(self.cols[field],pool)),pool)
  if op.startswith('fn2-pool-') and op[len('fn2-pool-'):] in self.cols:return nth(values[0],nth(self.cols[op[len('fn2-pool-'):]],values[1]))
  return self.call(op,*values)
 def pool(self,data,base=-1,fill=1):
  p=[[0,0] for _ in self.cols]+[2,list(data)]
  for field,value in {'state':self.constants['*fn2-pool-state-workspace*'],'base':base,'cap':4,'fill':fill}.items():p[self.cols[field]]=[value,value]
  return p
 def copy(self,p,n=2):return self.call('fn2-rd-copy',n,0,0,0,0,0,0,1,0,0,0,0,0,p)

class CopyData(unittest.TestCase):
 def test_original_runtime_guards_and_contract_unchanged(self):
  before=subprocess.check_output(['git','show',BASE+':books/pool-copy.lisp'],cwd=ROOT,text=True)
  old=parse(before).forms;new=parse(ROOT/'books/pool-copy.lisp').forms
  added=[n for n in new if isinstance(n,Lst) and flat(n.items[0]) in ('defthm','local')]
  self.assertEqual([flat(n) for n in old],[flat(n) for n in new if n not in added])
  final=match(None,new,deep=False,head='defthm')[-1].node
  self.assertEqual(flat(final.items[2]),'(equal (fn2-pool-data-length (mv-nth 1 (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool))) (fn2-pool-data-length fn2-pool))')
 def test_connected_reader_frames_preserve_all_existing_forms(self):
  before=subprocess.check_output(['git','show',BASE+':books/machines-c-read.lisp'],cwd=ROOT,text=True)
  new=parse(ROOT/'books/machines-c-read.lisp').forms
  added=[x for x in new if flat(x)=='(include-book "pool-dimensions")' or (isinstance(x,Lst) and x.items and flat(x.items[0])=='fn2-pool-dimensions')]
  self.assertEqual(len(added),3)
  self.assertEqual([flat(x) for x in parse(before).forms],[flat(x) for x in new if x not in added])
  self.assertEqual({flat(x) for x in added if flat(x)!='(include-book "pool-dimensions")'},
   {'(fn2-pool-dimensions fn2-rd-octets :observations (:data) :opaque (fn2-rd-copy fn2-rd-entry-row))',
    '(fn2-pool-dimensions fn2-read-octets-children :observations (:rows :data) :opaque (fn2-rd-octets))'})
 def test_actual_byte_and_length_boundaries(self):
  actual=Actual();count=0
  for data,base,fill,idx,byte in itertools.product([[],[None],[0],[255],[-1],[256],[7,8]],[-3,-1,0,1,3],[0,1,2,4],[0,1,2],[None,-1,0,255,256]):
   p=actual.pool(data,base,fill);result=actual.call('fn2-pool-write',1,0,idx,byte,0,0,0,p)
   if data:self.assertEqual(len(nth(actual.data,result[1])),len(data))
   if not(nat(byte) and byte<256):self.assertEqual(result[1],p)
   code,value=actual.call('fn2-pool-read',0,0,idx,0,0,0,p)
   if code==':ok' and nat(value) and value<256:self.assertTrue(data)
   count+=1
  self.assertEqual(count,2100)
  copies=0
  for data,sbase,dbase,fill,n in itertools.product([[],[None],[0],[255],[-1],[256],[7,8]],[-3,-1,0,1,3],[-3,-1,0,1,3],[0,1,2,4],range(4)):
   p=actual.pool(data,sbase,fill);p[actual.cols['base']]=[sbase,dbase]
   self.assertEqual(len(nth(actual.data,actual.copy(p,n)[1])),len(data));copies+=1
  self.assertEqual(copies,2800)
 def test_malformed_empty_counterparts_and_required_byte_flow(self):
  actual=Actual();p=actual.pool([])
  self.assertEqual(p[actual.rows],2)
  self.assertTrue(all(len(p[i])==p[actual.rows] for i in actual.cols.values()))
  self.assertLess(p[actual.cols['base']][0],0)  # WFP shape, but not :u60/P.
  self.assertEqual(actual.call('fn2-pool-read',0,0,0,0,0,0,p),(':ok',None))
  self.assertEqual(len(nth(actual.data,actual.call('fn2-pool-write',1,0,0,7,0,0,0,p)[1])),1)
  self.assertEqual(actual.copy(p)[1],p)
  # A real-body mutation dropping WRITE's byte check destroys COPY's law.
  args,body=actual.functions['fn2-pool-write'];body=copy.deepcopy(body)
  checks=body[-1][2][0][1]
  self.assertEqual(checks[0],'and');self.assertIn(['unsigned-byte-p',8,'byte'],checks)
  checks.remove(['unsigned-byte-p',8,'byte']);actual.functions['fn2-pool-write']=(args,body)
  self.assertEqual(len(nth(actual.data,actual.copy(p)[1])),1)
if __name__=='__main__':unittest.main()
