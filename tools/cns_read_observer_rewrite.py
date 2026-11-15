#!/usr/bin/env python3
"""Project CNS metadata-observer lifetime onto a named current callback source.

Only selected CNS declarations/arms and streamed FETCH MID handoff change.
CTL, input transport, physical retention and unrelated definitions are preserved.
Source transformation is not ACL2 admission.
"""
from pathlib import Path
import argparse
import lisp_rewrite as lr

ROOT=Path(__file__).resolve().parents[1]
GATE='''(:do (META-CODE META-RECEIPT) (fn2-cns-request-acquire id row-generation)
    :accept (:ok) :case (((:admission) (:charge :steps *fn2-work-transition* :runnable t))))
   (:set (observer-serial META-RECEIPT))'''
DROP='''(:do (META-DROP) (fn2-cns-request-release id row-generation) :accept (:ok))
   (:set (observer-serial 0))'''
COST='''(defcost fn2-cns-request-acquire :answers (:ok :admission :fault) :faults (:fault)
 :tables (fn2-core-reads fn2-core-c-source-control fn2-core-c-source-readers)
 :doc "Admit the exact CNS metadata operation and bind its one nested READ; existing receipts drain under PENDING.")
(defcost fn2-cns-request-release :answers (:ok :fault) :faults (:fault)
 :tables (fn2-core-reads fn2-core-ranges fn2-core-range-sources fn2-core-seeks fn2-core-succ-txns
          fn2-core-run-cursors fn2-core-run-paths fn2-core-fields fn2-core-c-source-control fn2-core-c-source-readers)
 :doc "Close the owned READ then relinquish its metadata parent before commit/upload/transport waits.")
'''
MIDCOST='''(defcost fn2-cns-stream-source-check-mid :answers (:ok :bad) :bytes 4096 :own-writes (mid-checked)
 :tables (fn2-cns-table fn2-core-reads fn2-core-ranges fn2-core-range-sources fn2-core-seeks fn2-core-run-cursors
          fn2-core-run-paths fn2-core-succ-txns fn2-core-fields fn2-core-pool fn2-core-c-source-control fn2-core-c-source-readers)
 :doc "Record the actual selected occurrence/MID comparison before physical-source retention replaces the C observer.")
'''
def gate(site):return GATE.replace('META-CODE','meta-code-'+site).replace('META-RECEIPT','meta-receipt-'+site)
def drop(site):return DROP.replace('META-DROP','meta-drop-'+site)
def head(n):
 return n.items[0].low if isinstance(n,lr.Lst) and n.items and isinstance(n.items[0],lr.Atom) else ''
def sym(n):return n.low if isinstance(n,lr.Atom) else ''
def walk(n):
 yield n
 if isinstance(n,lr.Lst):
  for x in n.items:yield from walk(x)
 elif isinstance(n,lr.Pre):yield from walk(n.node)
def value(n,key):
 for i,x in enumerate(n.items[:-1]):
  if sym(x)==key:return n.items[i+1]
 raise ValueError('missing '+key)
def named(forms,h,name):
 matches=[n for f in forms for n in walk(f) if head(n)==h and len(n.items)>1 and sym(n.items[1])==name
          and (h!='defmachine-arms' or any(sym(x)==':arms' for x in n.items))]
 if len(matches)!=1:raise ValueError(f'{h} {name}: {len(matches)} matches')
 return matches[0]
def text(p,n):return p.text[n.start:n.end]
def append_items(edits,node,source):edits.append((node.end-1,node.end-1,' '+source))
def source_handoff(source):
 """Keep the live C observer until transitive physical retention is complete.

 A manifest root claim is not a descendant closure. Cancellation retains the
 same receipt until bounded source cleanup reaches actual HANDOFF.
 """
 p=lr.parse(source);body=named(p.forms,'defmachine-arms','fn2-cns')
 arms={head(n):n for n in value(body,':arms').items};subs={head(n):n for n in value(body,':subarms').items}
 if ':source' not in arms:return source
 edits=[]
 item=subs['item']
 calls=[n for n in walk(item) if head(n)==':do' and head(n.items[2])=='fn2-cns-request-release']
 for call in calls:
  sets=[n for n in walk(item) if head(n)==':set' and n.start>call.end and any(head(x)=='observer-serial' for x in n.items[1:])]
  if len(calls)!=1 or not sets:raise ValueError('unexpected ITEM metadata drop')
  clear=min(sets,key=lambda n:n.start)
  edits.append((call.start,clear.end,''))
 # A captured but refused item can reach these cleanup subarms before SOURCE.
 # Their SOURCE-bound branch must retain the observer until HANDOFF as well.
 for name in ('cancel','page-fail','page-cancel'):
  sub=subs[name]
  if head(sub.items[3])==':if' and head(sub.items[3].items[1])=='fn2-cns-source-boundp':continue
  call=sub.items[3];clear=sub.items[4]
  if not(head(call)==':do' and head(call.items[2])=='fn2-cns-request-release' and head(clear)==':set'):
   raise ValueError('unexpected source cancellation drop '+name)
  edits.append((call.start,clear.end,'(:if (fn2-cns-source-boundp id row-generation row-ctl row-ctl-gen row-request)\n         ()\n         ('+text(p,call)+'\n          '+text(p,clear)+'))'))
 case=next(n for n in arms[':source'].items if head(n)==':case')
 def clause(name):return next(n for n in case.items[2:] if isinstance(n,lr.Lst) and head(n.items[0])==name)
 for name,site in ((':covered','source-covered'),(':handoff','source-handoff')):
  branch=clause(name)
  if any(head(n)=='fn2-cns-request-release' for n in walk(branch)):continue
  step=branch.items[1]
  why=('All authenticated manifest descendants now have exact retained claims; release C before any prefix.'
       if name==':covered' else 'Abort/preheader cleanup has released every source claim; retire its retained C observation before the workspace.')
  code='; '+why+'\n     (:if (posp row-observer-serial)\n          ('+drop(site).replace('\n   ','\n           ')+')\n          ())\n     '
  edits.append((step.start,step.start,code))
 return lr.write(source,edits).replace('\n     \n     (:set (stream 0))', '\n     (:set (stream 0))')

def validate_callbacks(source):
 p=lr.parse(source);body=named(p.forms,'defmachine-arms','fn2-cns')
 arms={head(n):n for n in value(body,':arms').items};subs={head(n):n for n in value(body,':subarms').items}
 def count(node,fn):return sum(head(x)==fn for x in walk(node))
 for phase in (':decode',':check',':lookup',':read',':page',':refresh'):
  if phase not in arms or count(arms[phase],'fn2-cns-request-acquire')!=1:raise ValueError('partial metadata admission '+phase)
 for phase in (':commit',':committed',':append',':park'):
  if head(arms[phase].items[3])!=':do' or head(arms[phase].items[3].items[2])!='fn2-cns-request-release':raise ValueError('missing metadata drop '+phase)
 for name in ('hand','cancel','page-end','page-fail','page-cancel'):
  if ':source' in arms and name in ('cancel','page-fail','page-cancel'):
   first=subs[name].items[3]
   if head(first)!=':if' or head(first.items[1])!='fn2-cns-source-boundp' or first.items[2].items:raise ValueError('early source cancellation drop '+name)
   continue
  if head(subs[name].items[3])!=':do' or head(subs[name].items[3].items[2])!='fn2-cns-request-release':raise ValueError('missing metadata handoff '+name)
 for phase in (':commit',':committed'):
  if count(arms[phase],'fn2-cns-lookup-cursor'):raise ValueError('yielding metadata read still consumes commit result '+phase)
 if count(arms[':draining'],'fn2-cns-request-release'):raise ValueError('draining changed instead of preserving its original semantic subject')
 if ':source' in arms:
  if count(subs['item'],'fn2-cns-request-release'):raise ValueError('root-only claim dropped META')
  case=next(n for n in arms[':source'].items if head(n)==':case')
  for branch in case.items[2:]:
   label=head(branch.items[0]) if isinstance(branch,lr.Lst) and isinstance(branch.items[0],lr.Lst) else ''
   drops=[n for n in walk(branch) if head(n)=='fn2-cns-request-release']
   if label in (':covered',':handoff'):
    if len(drops)!=1 or head(branch.items[1])!=':if' or head(branch.items[1].items[1])!='posp':raise ValueError('missing once-only physical handoff '+label)
   elif drops:raise ValueError('precoverage metadata drop '+label)

 if '"cns-request-observer"' not in source or '(fn2-cns-request-observer-events)' not in source:raise ValueError('missing observer provider')
 opened=[n for f in p.forms for n in walk(f) if head(n)=='defun' and sym(n.items[1])=='fn2-cns-stream-source-open']
 if opened and (count(opened[0],'fn2-cns-entry-mid') or not count(opened[0],'fn2-cns-row-mid-checked')):raise ValueError('source handoff still borrows C')

def validate_kind(source):
 p=lr.parse(source);kind=named(p.forms,'defmachine','fn2-cns')
 fields={head(x) for x in value(kind,':fields').items}
 if not {'observer-serial','mid-checked','refresh'}<=fields:raise ValueError('partial observer fields')
 if ':refresh' not in [sym(x) for x in value(kind,':phases').items]:raise ValueError('missing refresh phase')
 if ':refresh' not in {head(x) for x in value(kind,':arms').items}:raise ValueError('missing refresh arm')
 if not {'observer-serial','mid-checked','refresh'}<=set(sym(x) for x in value(value(kind,':taken'),':clear').items):raise ValueError('uncleared observer receipt')

def transform_kind(source):
 p=lr.parse(source);kind=named(p.forms,'defmachine','fn2-cns');edits=[]
 if any(sym(n)=='observer-serial' for n in walk(value(kind,':fields'))):
  validate_kind(source);return source
 append_items(edits,value(kind,':fields'),'(observer-serial :u60) (mid-checked :bool) (refresh (:enum fn2-cns-refresh (:none :unchanged :duplicate :accepted)))')
 append_items(edits,value(kind,':phases'),':refresh')
 append_items(edits,value(kind,':holds'),'(:refresh :tx-range :wait-row (:storage-window :while (lease :held)))')
 append_items(edits,value(kind,':arms'),'(:refresh)')
 append_items(edits,value(value(kind,':taken'),':clear'),'observer-serial mid-checked refresh')
 result=lr.write(source,edits);validate_kind(result);return result
def transform_callbacks(source,refresh,mid):
 p=lr.parse(source);body=named(p.forms,'defmachine-arms','fn2-cns');arms=value(body,':arms');subs=value(body,':subarms');edits=[]
 if '(fn2-cns-request-acquire id row-generation)' in source:
  source=source_handoff(source);validate_callbacks(source);return source
 include=next(f for f in p.forms if head(f)=='include-book' and text(p,f)=='(include-book "cns-kind")')
 edits.append((include.end,include.end,'\n(include-book "cns-request-observer")'))
 costs=[f for f in p.forms if head(f)=='defcost']
 edits.append((costs[0].start,costs[0].start,COST))
 # Every CNS callback already declaring a mutable READ child also carries
 # the newly observed child/control effects. This is one declaration class.
 for cost in costs:
  if not sym(cost.items[1]).startswith('fn2-cns-'):continue
  try:tables=value(cost,':tables')
  except ValueError:continue
  if sym(cost.items[1])=='fn2-cns-stream-source-open':
   edits.append((tables.start,tables.end,'(fn2-ctl-table fn2-core-sched fn2-core-trace fn2-core-control)'))
   doc=value(cost,':doc');edits.append((doc.start,doc.end,'"Open a captured source only after its retained actual MID check and complete authenticated coverage."'))
   continue
  if any(sym(x)=='fn2-core-reads' for x in tables.items):
   missing=[x for x in ('fn2-core-c-source-control','fn2-core-c-source-readers') if not any(sym(y)==x for y in tables.items)]
   if missing:append_items(edits,tables,' '.join(missing))
 byname={head(n):n for n in arms.items}
 for name in (':check',':lookup',':read',':page'):
  arm=byname[name];at=arm.items[3].start;edits.append((at,at,gate(name[1:])+'\n   '))
 decode=byname[':decode'];setx=next(n for n in decode.items if head(n)==':set' and any(head(a)=='xrow' for a in n.items[1:]))
 edits.append((setx.end,setx.end,'\n   '+gate('decode')))
 for name in (':commit',':committed',':append',':park'):
  arm=byname[name];at=arm.items[3].start;edits.append((at,at,drop(name[1:])+'\n   '))
 for sub in subs.items:
  if head(sub) in ('hand','cancel','page-end','page-fail','page-cancel'):
   at=sub.items[3].start;edits.append((at,at,drop(head(sub))+'\n   '))
 # PAGE lease pressure preserves IPOS and reselects the whole item.
 # Its borrowed READ is closed before reserving/parking for pool capacity.
 for n in walk(byname[':page']):
  if head(n)==':let' and len(n.items)>2 and head(n.items[2])=='fn2-cns-lease-class':
   edits.append((n.start,n.start,drop('page-lease')+'\n                     '))
 # Commit result consumption is atomic. Move subsequent C reads to a fresh
 # resumable phase so a closed gate cannot consume an accepted ticket twice.
 commit=next(n for n in walk(byname[':commit']) if head(n)==':commit' and any(sym(x)==':workspace' for x in n.items))
 un=value(commit,':unchanged').items[0]
 branch=un.items[2]
 edits.append((branch.start,branch.end,'((:set (refresh *fn2-cns-refresh-unchanged*)) (:next :refresh) (:charge :steps *fn2-work-transition* :runnable t))'))
 refused=value(commit,':refused').items[0];duplicate=refused.items[1]
 edits.append((duplicate.items[1].start,duplicate.items[-1].end,'(:set (refresh *fn2-cns-refresh-duplicate*)) (:next :refresh) (:charge :steps *fn2-work-transition* :runnable t)'))
 settled=next(n for n in walk(byname[':committed']) if head(n)==':commit' and any(sym(x)==':workspace' for x in n.items))
 accepted=value(settled,':accepted')
 edits.append((accepted.start,accepted.end,'((:set (refresh *fn2-cns-refresh-accepted*)) (:next :refresh) (:charge :steps *fn2-work-transition* :runnable t))'))
 edits.append((byname[':commit'].start,byname[':commit'].start,refresh+'\n'))
 firstloop=named(p.forms,'defun','fn2-cns-lookup-loop')
 edits.append((firstloop.start,firstloop.start,'(fn2-cns-request-observer-events)\n     '))
 # Streamed FETCH finishes C metadata before SOURCE can issue manifest reads.
 streamed=[n for f in p.forms for n in walk(f) if head(n)=='defun' and sym(n.items[1])=='fn2-cns-stream-source-open']
 if streamed:
  edits.append((costs[0].start,costs[0].start,MIDCOST))
  endmid=next(n for f in p.forms for n in walk(f) if head(n)=='in-theory' and 'disable fn2-cns-entry-mid' in text(p,n))
  edits.append((endmid.end,endmid.end,'\n'+mid))
  item=next(n for n in subs.items if head(n)=='item');cond=next(n for n in item.items if head(n)==':cond');clause=cond.items[1]
  if 'fn2-cns-source-boundp' not in text(p,clause.items[0]):raise ValueError('unexpected streamed item clause')
  edits.append((clause.items[1].start,clause.items[-1].end,'''(:do (meta-mid-code) (fn2-cns-stream-source-check-mid id row-generation) :accept (:ok :bad) :why "a mismatch enters owned-source cleanup before any prefix")
     '''+drop('fetch-capture')+'''
     (:set (stream 0))
     (:if (eq meta-mid-code :ok)
          ((:next :source) (:charge :bytes 12288 :steps *fn2-work-transition* :runnable t))
          ((:do () (fn2-cns-stream-source-abort id row-generation row-ctl row-ctl-gen row-request))
           (:next :source) (:charge :bytes 12288 :steps *fn2-work-transition* :runnable t)))'''))
  op=streamed[0];bstar=next(n for n in op.items[3:] if head(n)=='b*');bindings=bstar.items[1]
  start=next(n for n in bindings.items if head(n)=='slot')
  stop=next(n for n in bindings.items if isinstance(n,lr.Lst) and len(n.items)==2 and head(n.items[0])=='mv' and sym(n.items[0].items[1])=='code')
  edits.append((start.start,stop.start,'''((unless (equal (fn2-cns-row-mid-checked cns fn2-core) 1)) (mv :bad fn2-core))
           '''))
 result=source_handoff(lr.write(source,edits));validate_callbacks(result);return result
def main():
 ap=argparse.ArgumentParser();ap.add_argument('callbacks',type=Path);ap.add_argument('kind',type=Path);ap.add_argument('--write',action='store_true');a=ap.parse_args()
 here=Path(__file__).resolve().parent
 c=transform_callbacks(a.callbacks.read_text(),(here/'cns_read_observer_refresh.lisp').read_text(),(here/'cns_read_observer_mid.lisp').read_text())
 k=transform_kind(a.kind.read_text())
 for name,content in [(a.callbacks,c),(a.kind,k)]:
  lr.parse(content)
  if a.write:name.write_text(content)
  else:print(name,'changed' if content!=name.read_text() else 'unchanged')
if __name__=='__main__':main()
