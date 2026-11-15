"""Finish NNTP admission/rank projection without changing resident algorithms."""
from pathlib import Path
import lisp_rewrite as lr
from read_observer_rewrite import nodes,sym

def port(text):
 if '(fn2-cursor-physical-count)' in text:raise ValueError('already projected')
 p=lr.parse(text);edits=[]
 for f in p.forms:
  if isinstance(f,lr.Lst) and len(f.items)>1 and sym(f.items[0])=='defun' and sym(f.items[1])=='fn2-cursor-lease-class-of':edits.append((f.start,f.end,''))
  if isinstance(f,lr.Lst) and len(f.items)>1 and sym(f.items[0])=='include-book' and isinstance(f.items[1],lr.Str) and f.items[1].text=='"machines-c-read-loader"':edits.append((f.end,f.end,'\n(include-book "cursor-physical-admission")'))
 # New helpers are lower, their costs remain this kind's actual book-local
 # declarations so the ordinary machine face emitter discovers them.
 at=text.index('(defcost fn2-cursor-lease-class ')
 costs='''(defcost fn2-cursor-physical-count :child fn2-run-installed-physical-count
 :doc "Actual installed physical root count; read only after the request parent is held.")
(defcost fn2-cursor-article-query-reserve :child fn2-cursor-article-query-reserve-children :answers t
 :tables (fn2-core-reads fn2-core-id-decides fn2-core-run-loads fn2-core-run-cursors fn2-core-checkpoint-summary fn2-core-checkpoint-summary-leases fn2-core-pool)
 :effects :per-use
 :doc "Atomically acquire ARTICLE scratch then the shared physical query recipe, or roll back before refusal.")
'''
 edits.append((at,at,costs))
 # Nested physical admission after actual parent acquisition and parsing.
 for f in p.forms:
  for n in nodes(f):
   if not isinstance(n,lr.Lst) or len(n.items)<3 or sym(n.items[0])!=':do':continue
   call=n.items[2]
   if not isinstance(call,lr.Lst) or not call.items:continue
   if sym(call.items[0])=='fn2-run-page-bundle-reserve':
    raw=text[n.start:n.end].replace('(query-bundle *fn2-cursor-query-bundle-held*)','(query-bundle *fn2-cursor-query-bundle-held*) (storage-hold *fn2-cursor-storage-hold-held*)')
    article='''(:do (admit complete ls lg) (fn2-cursor-article-query-reserve (* *fn2-b-query-read-rows* row-slot) *fn2-cursor-kind* id row-generation)
     :effects ((:acquire (:storage-window))) :accept () :case
     (((:ok) (:set (query-bundle *fn2-cursor-query-bundle-held*) (storage-hold *fn2-cursor-storage-hold-held*)
                   (lease *fn2-cursor-lease-held*) (lslot ls) (lgen lg) (load-release 0) (load-refuse (if (equal complete 1) 0 1)))
              (:next (:if (equal complete 1) :seek :finish)) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
      ((:exhausted) (:set (reply (fn2-cursor-reply-of ptag :no-projection))) (:goto refuse))
      ((:recovery-required) (:set (lease *fn2-cursor-lease-held*) (lslot ls) (lgen lg) (storage-hold *fn2-cursor-storage-hold-held*)) (:stop :machine-phase))
      (:otherwise (:stop :machine-phase))))'''
    repl='''(:let physical (fn2-cursor-physical-count))
   (:cond ((equal physical 0) (:next :seek) (:charge :bytes 512 :steps *fn2-work-transition* :runnable t))
          ((fn2-cursor-article-scratch-p ptag) '''+article+''')
          (t '''+raw+'''))'''
    edits.append((n.start,n.end,repl))
   # Restore original rank effect on ARTICLE releases only in resident paths;
   # physical paths retain scratch until FINISH under the aggregate rank.
   if sym(call.items[0])=='fn2-cursor-lease-release':
    if any(isinstance(a,lr.Atom) and a.low==':effects' for a in n.items):continue
    # FINISH has its own conditional release projection below.
    if n.start>text.index('(:finish :on-refusal',text.index(':arms\n')):continue
    edits.append((call.end,call.end,' :effects ((:release (:storage-window)))'))
 # Guard nonterminal ARTICLE release branches by resident mode, preserving
 # scratch for physical HDR/XPAT fallback across all article rows.
 for f in p.forms:
  for n in nodes(f):
   if not isinstance(n,lr.Lst) or not n.items:continue
   if sym(n.items[0]) in {'art-fail','art-end'}:
    old='(equal row-lease *fn2-cursor-lease-held*)';pos=text.index(old,n.start,n.end)
    edits.append((pos,pos+len(old),'(and '+old+' (not (equal row-query-bundle *fn2-cursor-query-bundle-held*)))'))
   if sym(n.items[0])=='art-lease':
    cond=next(a for a in n.items if isinstance(a,lr.Lst) and a.items and sym(a.items[0])==':cond')
    tbranch=cond.items[-1];edits.append((tbranch.start,tbranch.start,'((equal row-query-bundle *fn2-cursor-query-bundle-held*) (:goto art-refuse))\n            '))
    old='(lease *fn2-cursor-lease-held*)';pos=text.index(old,n.start,n.end)
    edits.append((pos+len(old),pos+len(old),' (storage-hold *fn2-cursor-storage-hold-held*)'))
   if sym(n.items[0])=='run-load-drain':
    old='(query-bundle *fn2-cursor-query-bundle-none*)';pos=text.index(old,n.start,n.end)
    edits.append((pos+len(old),pos+len(old),' (storage-hold *fn2-cursor-storage-hold-none*)'))
 # Resident ARTICLE releases clear the aggregate rank; the physical FINISH
 # branch releases only scratch and leaves the query's rank held.
 for f in p.forms:
  for n in nodes(f):
   if not isinstance(n,lr.Lst) or not n.items:continue
   if sym(n.items[0]) in {'art-fail','art-end'}:
    old='(lease *fn2-cursor-lease-none*)';pos=text.index(old,n.start,n.end)
    edits.append((pos+len(old),pos+len(old),' (storage-hold *fn2-cursor-storage-hold-none*)'))
   if sym(n.items[0])==':finish':
    call=next(a for a in nodes(n) if isinstance(a,lr.Lst) and len(a.items)>2 and sym(a.items[0])==':do' and isinstance(a.items[2],lr.Lst) and a.items[2].items and sym(a.items[2].items[0])=='fn2-cursor-lease-release')
    raw=text[call.start:call.end]
    resident=raw.replace(':accept',':effects ((:release (:storage-window))) :accept',1)
    edits.append((call.start,call.end,'(:if (equal row-query-bundle *fn2-cursor-query-bundle-held*)\n        ('+raw+')\n        ('+resident+' (:set (storage-hold *fn2-cursor-storage-hold-none*))))'))
 return lr.write(text,edits)

def kind(text):
 p=lr.parse(text);edits=[]
 for f in p.forms:
  for n in nodes(f):
   if isinstance(n,lr.Lst) and len(n.items)==3 and sym(n.items[0])==':storage-window':edits.append((n.start,n.end,'(:storage-window :while (storage-hold :held))'))
 fields=next(n for f in p.forms for n in nodes(f) if isinstance(n,lr.Lst) and n.items and sym(n.items[0])=='query-bundle')
 edits.append((fields.end,fields.end,'\n          (storage-hold (:enum fn2-cursor-storage-hold (:none :held)))'))
 m=next(f for f in p.forms if isinstance(f,lr.Lst) and f.items and sym(f.items[0])=='defmachine')
 taken=m.items[next(i for i,a in enumerate(m.items) if sym(a)==':taken')+1]
 clear=taken.items[next(i for i,a in enumerate(taken.items) if sym(a)==':clear')+1];edits.append((clear.end-1,clear.end-1,' storage-hold'))
 return lr.write(text,edits)
if __name__=='__main__':
 p=Path('books/cursor.lisp');p.write_text(port(p.read_text()))
 p=Path('books/cursor-kind.lisp');p.write_text(kind(p.read_text()))
 p=Path('books/cursor-source-observer.lisp');s=p.read_text();s=s.replace('(equal (fn2-cursor-load-active slot fn2-cursor-table) 0)','(equal (fn2-cursor-load-active slot fn2-cursor-table) 0)\n                    (equal (fn2-cursor-storage-hold slot fn2-cursor-table) *fn2-cursor-storage-hold-none*)');p.write_text(s)
