"""Local aligned-word/composition proof source for the shared fetch worker.

Only proof events/hints change. The exact runtime logical/exec bodies and the
public refinement formula remain unchanged. All new proof events are UNRUN.
"""
from pathlib import Path
import lisp_rewrite as lr

def node(s,p):
 m=lr.match(p,lr.parse(s).forms,deep=False)
 if len(m)!=1:raise ValueError((p,len(m)))
 return m[0].node

SUPPORT='''; Local proof support: a backend pool read never uses the continuation
; status :MORE. Thus worker concatenation cannot mistake an error for yield.
(local (defthm fn2-rec-byte-at-not-more
 (not (equal (mv-nth 0 (fn2-rec-byte-at slot gen off okind oslot ogen fn2-pool)) :more))
 :hints (("Goal" :in-theory (enable fn2-rec-byte-at fn2-pool-read fn2-pool-readable-code fn2-pool-handle-code)))))
(local (defthm fn2-rec-byte-at-u8
 (unsigned-byte-p 8 (mv-nth 1 (fn2-rec-byte-at slot gen off okind oslot ogen fn2-pool)))
 :hints (("Goal" :in-theory (enable unsigned-byte-p)))))
(local (defthm fn2-rec-fetch-aligned-state
 (implies (and (natp k) (<= k 8)) (fn2-rec-fetch-state-p (* 4 k) 0))
 :hints (("Goal" :in-theory (enable fn2-rec-fetch-state-p)))))
(local (defthm fn2-rec-fetch-bytes-shape
 (implies (and (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests))
  (and (fn2-digestsp (mv-nth 3 (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (fn2-digests-wfp (mv-nth 3 (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (equal (fn2-digests-rows (mv-nth 3 (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests))) (fn2-digests-rows fn2-digests))))
 :hints (("Goal" :induct (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)
                 :in-theory (enable fn2-rec-fetch-bytes fn2-digest-rowp)))))
(local (defthm fn2-rec-fetch-bytes-bound
 (implies (and (natp left) (fn2-rec-fetch-state-p next acc))
  (and (fn2-rec-fetch-state-p
         (mv-nth 1 (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests))
         (mv-nth 2 (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (<= next (mv-nth 1 (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)))
       (<= (mv-nth 1 (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)) 32)
       (<= (- (mv-nth 1 (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)) next) left)))
 :hints (("Goal" :induct (fn2-rec-fetch-bytes left next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)
                 :in-theory (enable fn2-rec-fetch-bytes fn2-rec-fetch-state-p)))))
(local (defthm fn2-rec-fetch-bytes-compose
 (implies (and (natp n) (natp m) (fn2-rec-fetch-state-p next acc)
               (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
               (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests) (natp off))
  (equal (mv-list 4 (fn2-rec-fetch-bytes (+ n m) next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests))
   (mv-list 4
    (mv-let (code after partial fn2-digests)
     (fn2-rec-fetch-bytes n next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)
     (if (eq code :more)
      (fn2-rec-fetch-bytes m after partial dst slot gen off okind oslot ogen fn2-pool fn2-digests)
      (mv code after partial fn2-digests))))))
 :hints (("Goal" :induct (fn2-rec-fetch-bytes n next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)
                 :in-theory (enable fn2-rec-fetch-bytes fn2-digest-rowp)))
 :rule-classes nil))

'''


def four_rhs(source):
 fn=node(source,'(defun fn2-rec-fetch ?*body)')
 logic=fn.items[-1]
 reads=lr.match('(b* ?bindings ?*body)',[logic])[0].captures['bindings'].items
 # Use the original read expressions and exact original word/update terms.
 prefix=reads[:5]
 word=[n for n in reads if isinstance(n,lr.Lst) and getattr(n.items[0],'low',None)=='word']
 update=[n for n in reads if isinstance(n,lr.Lst) and getattr(n.items[0],'low',None)=='fn2-digests']
 if len(word)!=1 or len(update)!=1:raise ValueError('original one-word model drift')
 text='(b* ('+'\n       '.join(source[n.start:n.end] for n in prefix)
 partial='0'
 for i in range(4):
  text+='\n       ((unless (eq c'+str(i)+' :ok)) (mv c'+str(i)+' (+ (* 4 k) '+str(i)+') '+partial+' fn2-digests))'
  partial='(mv-nth 1 (fn2-layout-byte :u32 '+str(i)+' '+partial+' 0 0 0 b'+str(i)+'))'
 text+='\n       '+source[word[0].start:word[0].end]+'\n       '+source[update[0].start:update[0].end]+')\n  (mv (if (= k 7) :ok :more) (+ (* 4 k) 4) 0 fn2-digests))'
 return text


def aligned(source):
 rhs=four_rhs(source)
 guard='''(and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool)
               (fn2-digestsp fn2-digests) (fn2-digest-rowp dst fn2-digests)
               (natp k) (< k 8) (natp off))'''
 call='(fn2-rec-fetch-bytes 4 (* 4 k) 0 dst slot gen off okind oslot ogen fn2-pool fn2-digests)'
 cases=' '.join('(< k '+str(i)+')' for i in range(1,9))
 result='''; This local four-byte view is extracted from the unchanged original
; first-word reads/update. Partial accumulator terms use the SAME byte codec.
(local (defthm fn2-rec-fetch-four-result
 (implies '''+guard+'''
  (equal (mv-list 4 '''+call+''') (mv-list 4 '''+rhs+''')))
 :hints (("Goal" :cases ('''+cases+''')
                 :in-theory (enable fn2-rec-fetch-bytes fn2-rec-fetch-state-p fn2-layout-byte fn2-layout-kind-code ash)))
 :rule-classes nil))
'''
 for i,label in enumerate(['code','next','acc','digests']):
  result+='''(local (defthm fn2-rec-fetch-four-'''+label+'''
 (implies '''+guard+'''
  (equal (mv-nth '''+str(i)+' '+call+''') (mv-nth '''+str(i)+' '+rhs+''')))
 :hints (("Goal" :use ((:instance fn2-rec-fetch-four-result))
                 :in-theory (disable fn2-rec-fetch-bytes)))))
'''
 result+='''; Split only the current aligned word; the recursive old API supplies
; the induction hypothesis for the remaining original words/carrier effects.
(local (defthm fn2-rec-fetch-remaining-split
 (implies '''+guard+'''
  (equal (mv-list 4 (fn2-rec-fetch-bytes (- 32 (* 4 k)) (* 4 k) 0 dst slot gen off okind oslot ogen fn2-pool fn2-digests))
   (mv-list 4
    (mv-let (code next acc fn2-digests) '''+call+'''
     (if (eq code :more)
      (fn2-rec-fetch-bytes (- 28 (* 4 k)) next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)
      (mv code next acc fn2-digests))))))
 :hints (("Goal" :use ((:instance fn2-rec-fetch-bytes-compose (n 4) (m (- 28 (* 4 k))) (next (* 4 k)) (acc 0)))
                 :in-theory (disable fn2-rec-fetch-bytes)))
 :rule-classes nil))
'''
 # The carrier/code projections are the exact uses needed by the public API.
 for i,label in [(0,'code'),(3,'digests')]:
  result+='''(local (defthm fn2-rec-fetch-remaining-'''+label+'''
 (implies '''+guard+'''
  (equal (mv-nth '''+str(i)+''' (fn2-rec-fetch-bytes (- 32 (* 4 k)) (* 4 k) 0 dst slot gen off okind oslot ogen fn2-pool fn2-digests))
         (mv-nth '''+str(i)+'''
          (mv-let (code next acc fn2-digests) '''+call+'''
           (if (eq code :more)
            (fn2-rec-fetch-bytes (- 28 (* 4 k)) next acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)
            (mv code next acc fn2-digests))))))
 :hints (("Goal" :use ((:instance fn2-rec-fetch-remaining-split))
                 :in-theory (disable fn2-rec-fetch-bytes)))))
'''
 result+='''(local (defthm fn2-rec-fetch-bytes-done-code
 (equal (mv-nth 0 (fn2-rec-fetch-bytes left 32 acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)) :ok)
 :hints (("Goal" :in-theory (enable fn2-rec-fetch-bytes)))))
(local (defthm fn2-rec-fetch-bytes-done-digests
 (equal (mv-nth 3 (fn2-rec-fetch-bytes left 32 acc dst slot gen off okind oslot ogen fn2-pool fn2-digests)) fn2-digests)
 :hints (("Goal" :in-theory (enable fn2-rec-fetch-bytes)))))
'''
 return result+'\n'


def with_hint(source,name,hint):
 n=node(source,'(defthm '+name+' ?*body)')
 if lr.match('(:hints ?*body)',[n]):raise ValueError('existing hint drift '+name)
 if any(getattr(x,'low',None)==':hints' for x in n.items):raise ValueError('existing hint property drift '+name)
 return lr.write(source,[(n.end-1,n.end-1,'\n '+hint)])


def rewrite(source):
 if '(local (defthm fn2-rec-fetch-bytes-compose' in source:return source
 anchor=node(source,'(defun fn2-rec-fetch-step ?*body)')
 source=lr.write(source,[(anchor.start,anchor.start,SUPPORT)])
 source=with_hint(source,'fn2-rec-fetch-step-progress-bound', ''':hints (("Goal" :use ((:instance fn2-rec-fetch-bytes-bound (left (min budget (- 32 next)))))
                        :in-theory (enable fn2-rec-fetch-step fn2-rec-fetch-state-p)))''')
 source=with_hint(source,'fn2-rec-fetch-step-result-state', ''':hints (("Goal" :use ((:instance fn2-rec-fetch-bytes-bound (left (min budget (- 32 next)))))
                        :in-theory (enable fn2-rec-fetch-step)))''')
 source=with_hint(source,'fn2-rec-fetch-step-zero', ''':hints (("Goal" :in-theory (enable fn2-rec-fetch-step fn2-rec-fetch-bytes fn2-rec-fetch-state-p)))''')
 source=with_hint(source,'fn2-rec-fetch-step-shape', ''':hints (("Goal" :in-theory (enable fn2-rec-fetch-step)))''')
 anchor=node(source,'(defthm fn2-rec-fetch-exec-refines ?*body)')
 source=lr.write(source,[(anchor.start,anchor.start,aligned(source))])
 source=with_hint(source,'fn2-rec-fetch-exec-refines', ''':hints (("Goal" :induct (fn2-rec-fetch k dst slot gen off okind oslot ogen fn2-pool fn2-digests)
                        :in-theory (e/d (fn2-rec-fetch fn2-rec-fetch-step fn2-digest-rowp)
                                        (fn2-rec-fetch-bytes fn2-rec-fetch-state-p))))''')
 anchor='(include-book "layout")'
 if source.count(anchor)!=1:raise ValueError('canonical layout include drift')
 source=source.replace(anchor,anchor+'\n(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))',1)
 return source

if __name__=='__main__':
 p=Path(__file__).resolve().parents[1]/'books/pool-digest.lisp'
 p.write_text(rewrite(p.read_text()))
