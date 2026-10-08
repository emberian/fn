"""Bind physical/refinement teeth to the proved terms, including outer LETs."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as rw

def claim(file,name):
 s=(ROOT/'books'/file).read_text();n=rw.match('_',rw.parse(s).forms,head='defthm',name=name,deep=False)[0].node.items[2]
 env={}
 def render(t,scope):
  if isinstance(t,rw.Atom):return scope.get(t.low,s[t.start:t.end])
  if isinstance(t,rw.Pre):return s[t.start:t.end]
  return '('+' '.join(render(i,scope) for i in t.items)+')'
 while n.items[0].low in ['let','let*']:
  scope=dict(env)
  for binding in n.items[1].items:
   scope[binding.items[0].low]=render(binding.items[1],scope if n.items[0].low=='let*' else env)
  env=scope;n=n.items[2]
 if n.items[0].low=='implies':return render(n.items[1],env),render(n.items[2],env)
 return None,render(n,env)

prefix='''; Additional teeth for physical persistence and the concrete dispatcher projection.
(in-package "ACL2")
(include-book "gc-pipeline-durable-tests")
(include-book "gc-pipeline-tests")
(include-book "../../books/defkeystone")
(defconst *gcpt-last* (fn-lg-last-trailer '((90)) *gcp-genesis*))
(defconst *gcpt-ks* (fn-lgk-make '((90)) *gcpt-last* 512 4 '((66)) '((65)) 1 :appended))
(defconst *gcpt-p* (fn-lgk-pipe-make *gcpt-ks* nil))
(defconst *gcpt-base*
 (fn-bs-make 512 (list (cons 0 (append (fn-lg-log '((90)) *gcp-genesis* 512)
                                     (make-list 2048 :initial-element 0)))) nil
  (list (list :write 0 512 (fn-lg-log '((65)) *gcpt-last* 512))) 1))
(defconst *gcpt-written*
 (mv-let (word after) (fn-lgk-pipe-physical-append *gcpt-base* *gcpt-p* 0 2560 :ok)
  (declare (ignore word)) after))
(defconst *gcpt-tail* (nthcdr 1 (fn-bs-pending *gcpt-written*)))
(defconst *gcpt-fenced*
 (mv-let (word after) (fn-bs-pipe-fsync-prefix *gcpt-written* 0 1 :ok)
  (declare (ignore word)) after))
(defconst *gcpt-image* (fn-bs-crash *gcpt-fenced* nil))
(defconst *gcpt-empty* (fn-bs-make 512 (list (cons 0 nil)) nil nil 1))
(defconst *gcpt-bad-written* (fn-bs-pipe-with-pending *gcpt-empty* (fn-bs-pending *gcpt-written*)))
(assert-event (and (equal (fn-lgk-acked *gcpt-ks*) 1)
 (fn-lgk-pipe-store-linkp *gcpt-written* *gcpt-base* *gcpt-ks* *gcpt-tail* 0 *gcp-genesis* 100)))
'''
base='((bs *gcpt-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*) (ino 0) (genesis *gcp-genesis*) (max 100))'
append='((bs *gcpt-base*) (p *gcpt-p*) (h \'((90) (65) (66))) (ino 0) (extent 2560) (outcome :ok) (genesis *gcp-genesis*) (max 100))'
rows=[('fn-lgk-pipe-physical-append-establishes-link','fn-lgk-pipe-physical-append',append,append.replace('(bs *gcpt-base*)','(bs *gcpt-empty*)')),
('fn-lgk-pipe-prefix-fence-safe','fn-bs-pipe-fsync-prefix',base,base.replace('(bs *gcpt-written*)','(bs *gcpt-bad-written*)')),
('fn-lgk-pipe-prefix-failure-keeps-durable-prefix','fn-bs-pipe-fsync-prefix',base[:-1]+' (outcome \'(:eio)))',base[:-1].replace('(bs *gcpt-written*)','(bs *gcpt-bad-written*)')+' (outcome \'(:eio)))'),
('fn-lgk-pipe-ack-keeps-store-safe','fn-lgk-pipe-ack',
 "((bs *gcp-fenced*) (p (fn-lgk-pipe-make *gcp-kf* t)) (h '((65) (66))) (n 1) (ino 0) (genesis *gcp-genesis*) (max 100))",
 "((bs *gcp-base*) (p *gcp-acked*) (h '((65) (66))) (n 1) (ino 0) (genesis *gcp-genesis*) (max 100))"),
('fn-lgk-pipe-promotion-restores-relation','fn-lgk-pipe-physical-append',append.replace(' (outcome :ok)',''),append.replace(' (outcome :ok)','').replace('(bs *gcpt-base*)','(bs *gcpt-empty*)'))]
text=prefix
for name,subject,w,b in rows:
 h,c=claim('store-log-pipeline-durable.lisp',name)
 text+=f'''\n(defteeth {name}
 :claim (((:relation {h})) {c}) :subject {subject}
 :witness {w} :breaks ((:relation {b}))
 :mutations (:not-applicable "The relation removal exercises loss of the durable prefix; explicit early-ACK and prefix-cut must-fails are in gc-pipeline-durable-tests."))\n'''
name='fn-lgk-pipe-prefix-fence-crash-recovers-acknowledged';h,c=claim('store-log-pipeline-durable.lisp',name)
w=base[:-1]+' (image *gcpt-image*) (next-txid 4))';b=w.replace('(image *gcpt-image*)','(image *gcpt-empty*)')
def ground(term,bindings):
 env={b.items[0].low:bindings[b.items[1].start:b.items[1].end] for b in rw.parse(bindings).forms[0].items}
 def go(n):
  if isinstance(n,rw.Atom):return env.get(n.low,term[n.start:n.end])
  if isinstance(n,rw.Pre):return term[n.start:n.end]
  return '('+' '.join(go(i) for i in n.items)+')'
 return go(rw.parse(term).forms[0])
positive=ground('(and '+h+' '+c+')',w)
negative=ground('(and (not '+h+') (not '+c+'))',b)
text+=f'''\n(defthm gcpt-crash-positive-flat
 {positive}
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff (s *gcpt-fenced*) (image *gcpt-image*) (choices nil)))
          :in-theory (disable fn-bs-crash-imagep))))
(defthm gcpt-crash-removal-flat
 {negative}
 :rule-classes nil
 :hints (("Goal" :use ((:instance {name}
   (bs *gcpt-written*) (base *gcpt-base*) (ks *gcpt-ks*) (tail *gcpt-tail*)
   (ino 0) (genesis *gcp-genesis*) (max 100) (image *gcpt-empty*) (next-txid 4)))
   :in-theory (disable fn-bs-crash-imagep))))
(defteeth {name}
 :claim (((:relation-and-image {h})) {c}) :subject fn-bs-pipe-fsync-prefix
 :witness {w} :witness-lemma gcpt-crash-positive-flat
 :breaks ((:relation-and-image {b} :lemma gcpt-crash-removal-flat))
 :mutations (:not-applicable "The image removal loses an actually acknowledged record; the positive ACK is one, not zero."))
'''
name='fn-ocp-gc-host-step-commutes-with-projection';h,c=claim('owner-commit-durability-concrete.lisp',name);assert h is None
text+=f'''\n(defteeth {name}
 :claim (() {c}) :subject fn-ocp-gc-host-step
 :witness ((x *gc-pipelined*) (event '(:reader))) :breaks nil
 :mutations ((:drop-reader-effect
  (:conclusion (equal (fn-ocp-gc-project (fn-ocp-gc-host-step x event))
   (update-nth 8 nil (fn-ocp-gc-host-step (fn-ocp-gc-project x) event))))
  ((x *gc-pipelined*) (event '(:reader)))
  :fault "A concrete dispatcher that drops the reader cut differs in its effects.")))
(value-triple :physical-and-projection-teeth-passed)
'''
(ROOT/'tests/acl2/gc-pipeline-refinement-teeth.lisp').write_text(text)
