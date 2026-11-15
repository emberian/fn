"""Narrow actual cursor port, preserving current request/ARTICLE lifetimes."""
from pathlib import Path
import subprocess
import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym

def named_lists(text):
 return {sym(n.items[0]):n for f in lr.parse(text).forms for n in nodes(f) if isinstance(n,lr.Lst) and n.items and sym(n.items[0])}
def port_cursor(text,donor):
 if '(run-load-start ' in text:raise ValueError('already ported')
 d=named_lists(donor);p=lr.parse(text);edits=[]
 def old(n):return donor[n.start:n.end]
 include=next(n for n in p.forms if isinstance(n,lr.Lst) and len(n.items)>1 and sym(n.items[0])=='include-book' and isinstance(n.items[1],lr.Str) and n.items[1].text=='"article-manifest"')
 edits.append((include.end,include.end,'\n(include-book "machines-c-read-loader")'))
 sub=next(n for n in p.forms if isinstance(n,lr.Lst) and len(n.items)>2 and sym(n.items[0])=='defmachine-arms' and any(sym(a)==':subarms' for a in n.items))
 i=next(i for i,a in enumerate(sub.items) if sym(a)==':subarms');sublist=sub.items[i+1]
 arms='\n'.join(old(d[name]) for name in ('run-load-start','run-load-step','run-load-read','run-load-drain'))
 # A physical read/copy has a full declared unit charge, even when the
 # external run allowance is smaller. Refuse before issuing on short credit.
 arms=arms.replace('(natp budget) (< 0 budget)','(natp budget) (<= *fn2-commit-unit-bytes* budget)')
 edits.append((sublist.start+1,sublist.start+1,'\n'+arms+'\n'))
 # Every actual query read's MISS gets the invoking read row, without
 # changing current :more, observer or source-error branches.
 count=0
 for f in p.forms:
  for n in nodes(f):
   if not isinstance(n,lr.Lst) or len(n.items)<3 or sym(n.items[0])!=':do':continue
   call=n.items[2]
   if not isinstance(call,lr.Lst) or not call.items or sym(call.items[0]) not in {'fn2-read-lookup','fn2-read-next','fn2-read-scan-next','fn2-read-identity','fn2-read-seek-step'}:continue
   idx=next((i for i,a in enumerate(n.items) if sym(a)==':case'),None)
   if idx is None:raise ValueError('query read has no case')
   clauses=n.items[idx+1]
   if any(isinstance(c,lr.Lst) and c.items and isinstance(c.items[0],lr.Lst) and any(sym(a)==':miss' for a in c.items[0].items) for c in clauses.items):raise ValueError('existing MISS route')
   at=next((c.start for c in clauses.items if isinstance(c,lr.Lst) and c.items and sym(c.items[0])==':otherwise'),clauses.end-1)
   row=text[call.items[1].start:call.items[1].end]
   edits.append((at,at,f'((:miss) (:set (load-read {row})) (:goto run-load-start))\n             '));count+=1
 if count!=10:raise ValueError('expected ten actual query sites, got '+str(count))
 # Replace only the old SELECT terminal inside the current parent-observer
 # wrapper, never its generation/cancel/acquire/parse branches.
 terminal='(:next :seek) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t)'
 if text.count(terminal)!=1:raise ValueError('SELECT terminal changed')
 tail='''(:do (admit complete) (fn2-run-page-bundle-reserve (* *fn2-b-query-read-rows* row-slot) *fn2-cursor-kind* id row-generation)
    :effects ((:acquire (:storage-window))) :accept () :case
    (((:ok) (:set (query-bundle *fn2-cursor-query-bundle-held*) (load-release 0) (load-refuse (if (equal complete 1) 0 1)))
             (:next (:if (equal complete 1) :seek :finish))
             (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
     ((:exhausted) (:set (reply (fn2-cursor-reply-of ptag :no-projection))) (:goto refuse))
     (:otherwise (:stop :machine-phase))))'''
 at=text.index(terminal);edits.append((at,at+len(terminal),tail))
 # Actual top-level seek/render phases retain their current remaining cases.
 i=next(i for i,a in enumerate(sub.items) if sym(a)==':arms');top=sub.items[i+1]
 for arm in top.items:
  if not isinstance(arm,lr.Lst) or not arm.items:continue
  phase=sym(arm.items[0])
  if phase in {':seek',':render'}:
   cond=next(a for a in arm.items if isinstance(a,lr.Lst) and a.items and sym(a.items[0])==':cond')
   at=cond.items[0].end
   edits.append((at,at,'\n    ((and (equal row-load-active 1) (equal row-cancel 1)) (:next :finish) (:charge :steps *fn2-work-transition* :runnable t))\n    ((equal row-load-active 1) (:goto run-load-step))'))
  if phase==':finish':
   raw="""(:finish :on-refusal ((:stop :machine-phase))
   ;; No decode or re-enumeration is reachable after terminal drain begins.
   ;; Pending0 precedes ARTICLE, page, catalog and READ-reference cleanup.
   (:if (not (equal row-pending 0))
    ((:wait :completion :steps *fn2-work-small*))
    ((:cond
      ((equal row-lease *fn2-cursor-lease-held*)
       (:do (lc) (fn2-cursor-lease-release row-lslot row-lgen) :accept (:ok :retired)
        :why ":retired: the ARTICLE scratch lease reached its generation limit")
       (:set (lease *fn2-cursor-lease-none*) (lslot *fn2-none*) (lgen 0))
       (:charge :steps *fn2-work-transition* :runnable t))
      ((equal row-query-bundle *fn2-cursor-query-bundle-held*)
       (:if (< row-load-release *fn2-b-query-loader-jobs*)
        ((:goto run-load-drain)) ((:stop :machine-phase))))
      (t
       ;; Every loader is IDLE/windows0/catalog-lease0 before CLOSE clears
       ;; retained references. The whole-response parent remains live here.
       (:do (rc1) (fn2-read-release (* *fn2-b-query-read-rows* row-slot)) :accept (:ok))
       (:do (rc2) (fn2-read-release (+ 1 (* *fn2-b-query-read-rows* row-slot))) :accept (:ok))
       (:if (equal row-load-refuse 1)
        ((:set (load-refuse 0) (reply (fn2-cursor-reply-of row-tag :no-projection))) (:goto refuse))
        ((:next :draining) (:charge :steps *fn2-work-transition* :runnable t))))))))"""
   edits.append((arm.start,arm.end,raw))
 # ARTICLE is a separate lease within the query's one storage-window rank.
 for f in p.forms:
  for n in nodes(f):
   if not isinstance(n,lr.Lst) or len(n.items)<3 or sym(n.items[0])!=':do':continue
   call=n.items[2]
   if not isinstance(call,lr.Lst) or not call.items or sym(call.items[0])!='fn2-cursor-lease-release':continue
   if any(a<=n.start and n.end<=b for a,b,_ in edits if b>a):continue # FINISH replaced above
   idx=next((i for i,a in enumerate(n.items) if sym(a)==':effects'),None)
   if idx is not None:edits.append((n.items[idx].start,n.items[idx+1].end,''))
 return lr.write(text,edits)

def port_kind(text):
 if '(query-bundle ' in text:raise ValueError('already ported')
 p=lr.parse(text);machine=next(n for n in p.forms if isinstance(n,lr.Lst) and len(n.items)>1 and sym(n.items[0])=='defmachine')
 def value(k):return machine.items[next(i for i,a in enumerate(machine.items) if sym(a)==k)+1]
 fields=value(':fields');taken=value(':taken');clears=taken.items[next(i for i,a in enumerate(taken.items) if sym(a)==':clear')+1]
 edits=[(fields.end-1,fields.end-1,'\n          (query-bundle (:enum fn2-cursor-query-bundle (:none :held)))\n          (load-active :bool) (load-read :u32) (load-cursor :u32) (load-release :u32) (load-refuse :bool)'),(clears.end-1,clears.end-1,' query-bundle load-active load-read load-cursor load-release load-refuse')]
 for n in nodes(value(':holds')):
  if isinstance(n,lr.Lst) and len(n.items)==3 and sym(n.items[0])==':storage-window':
   edits.append((n.start,n.end,'(:storage-window :while (query-bundle :held))'))
 return lr.write(text,edits)
def port_observer(text):
 old='(equal (fn2-cursor-lease slot fn2-cursor-table) *fn2-cursor-lease-none*)'
 if text.count(old)!=1:raise ValueError('request release lease preflight changed')
 return text.replace(old,old+"\n                    (equal (fn2-cursor-query-bundle slot fn2-cursor-table) *fn2-cursor-query-bundle-none*)\n                    (equal (fn2-cursor-load-active slot fn2-cursor-table) 0)")

if __name__=='__main__':
 donor=subprocess.check_output(['git','show','bdbf7e9bb:books/cursor.lisp'],text=True)
 p=Path('books/cursor.lisp');p.write_text(port_cursor(p.read_text(),donor))
 p=Path('books/cursor-kind.lisp');p.write_text(port_kind(p.read_text()))
 p=Path('books/assembly-callbacks-d-cursor.lisp');s=p.read_text();s=s.replace('(defmachine-arms fn2-cursor :wrappers)','(fn2-read-loader-core-faces)\n(defmachine-arms fn2-cursor :wrappers)');p.write_text(s)

 p=Path('books/cursor-source-observer.lisp');p.write_text(port_observer(p.read_text()))
