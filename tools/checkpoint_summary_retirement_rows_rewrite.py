"""Share exact source identity and retirement over active/pending catalog rows."""
from pathlib import Path
import lisp_rewrite as lr
TARGETS={'books/checkpoint-summary-leases.lisp':{
 'fn2-checkpoint-summary-run-source-p':'fn2-checkpoint-summary-row-run-source-p',
 'fn2-checkpoint-summary-retire-begin':'fn2-checkpoint-summary-row-retire-begin'},
 'books/checkpoint-summary-retire.lisp':{'fn2-checkpoint-summary-retire-row':'fn2-checkpoint-summary-row-retire-row'}}
CALLEES={'fn2-checkpoint-summary-run-source-p':'fn2-checkpoint-summary-row-run-source-p','fn2-checkpoint-cbase-promised-p':'fn2-checkpoint-cbase-row-promised-p'}
def rewrite(source,targets):
 forms=lr.parse(source).forms;ed=[]
 for old,new in targets.items():
  n=lr.match(f'(defun {old} ?*body)',forms,deep=False)[0].node
  text=source[n.start:n.end];inner=lr.parse(text).forms[0];ee=[]
  ee.append((inner.items[1].start,inner.items[1].end,new))
  args=inner.items[2];ee.append((args.start+1,args.start+1,'s '))
  for m in lr.match('(?head ?*args)',[inner]):
   call=m.node;h=getattr(call.items[0],'low','')
   if h.startswith('fn2-checkpoint-summary-') and len(call.items)>2 and getattr(call.items[1],'low','')=='0' and any(getattr(x,'low','')=='fn2-checkpoint-summary' for x in call.items[2:]):
    ee.append((call.items[1].start,call.items[1].end,'s'))
   if h in CALLEES:
    ee.append((call.items[0].start,call.items[0].end,CALLEES[h]));ee.append((call.items[0].end,call.items[0].end,' s'))
  row=lr.match('(< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))',[inner])
  for m in row:ee.append((m.start,m.end,'(and (natp s) (< s 2) (< s (fn2-checkpoint-summary-rows fn2-checkpoint-summary)))'))
  # RETIRE-ROW did not formerly test summary dimensions itself.
  if not row:
   body=inner.items[-1]
   first=lr.match('((unless ?test) ?*body)',[body])[0].node
   pred=first.items[0].items[1]
   ee.append((pred.start,pred.start,'(and (natp s) (< s 2) (< s (fn2-checkpoint-summary-rows fn2-checkpoint-summary)) '));ee.append((pred.end,pred.end,')'))
  shared=lr.write(text,ee)
  decl=source[n.items[3].start:n.items[3].end]
  formals=text[args.start:args.end]
  wrapper=f'(defun {old} {formals}\n {decl}\n ({new} 0 '+ ' '.join(x.low for x in args.items)+'))'
  ed.append((n.start,n.end,shared+'\n'+wrapper))
 return lr.write(source,ed)
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 for name,targets in TARGETS.items():
  p=root/name;p.write_text(rewrite(p.read_text(),targets))
