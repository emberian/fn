"""Named current BOOT projection; lower codecs remain sole implementations."""
from pathlib import Path
import json,sys
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
BEFORE=json.loads((ROOT/'tools/fixtures/boot-routing-current-before.json').read_text())
def once(s,a,b):
 if s.count(a)!=1:raise ValueError('one actual source boundary '+a[:80])
 return s.replace(a,b,1)
def constructor(s):
 s=once(s,'(include-book "executor-loop-events")','(include-book "executor-loop-events")\n(include-book "checkpoint-geometry")')
 a=next(x for x in lr.parse(s).forms if isinstance(x,lr.Lst) and len(x.items)>1 and getattr(x.items[1],'low','')=='fn2-image-sizep')
 body='(fn2-checkpoint-image-sizep size extents groups)'
 s=lr.write(s,[(a.items[-1].start,a.items[-1].end,body)])
 s=once(s,'(* 12288 (nfix (fn2-boot-config-extents fn2-boot-config)))','(* *fn2-storage-extent-bytes* (nfix (fn2-boot-config-extents fn2-boot-config)))')
 s=once(s,'(/ base 12288)','(/ base *fn2-storage-extent-bytes*)')
 s=once(s,'(class (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (class) (fn2-pool-class-for 4096 fn2-pool) class))','(class (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (class) (fn2-pool-class-for *fn2-format-page-size* fn2-pool) class))\n      (rxclass (stobj-let ((fn2-pool (fn2-core-pool fn2-core))) (class) (fn2-pool-class-for *fn2-format-sector-size* fn2-pool) class))')
 s=once(s,'((unless class) (mv :window fn2-core))','((unless (and class rxclass)) (mv :window fn2-core))')
 s=once(s,'(fn2-core-reserve class *fn2-boot-kind* id gen fn2-core))\n      ((unless (and (eq code :ok) (unsigned-byte-p 32 rx) (unsigned-byte-p 60 rgen))) (mv :window fn2-core))','(fn2-core-reserve rxclass *fn2-boot-kind* id gen fn2-core))\n      ((unless (and (eq code :ok) (unsigned-byte-p 32 rx) (unsigned-byte-p 60 rgen)))\n       (mv-let (release-code fn2-core) (fn2-core-release slot sgen *fn2-boot-kind* id gen fn2-core)\n        (mv (if (member-eq release-code (list :ok :retired)) :window :bounds) fn2-core)))')
 s=once(s,'(index 0) (stage 0) (epoch0 0)', '(index 0) (stage 0) (checkpoint-index 0) (checkpoint-length 0) (epoch0 0)')
 return s
PHASES=['bootstrap','bootstrap-write','bootstrap-write-result','bootstrap-read','bootstrap-result','bootstrap-verify','checkpoint-anchor','checkpoint-anchor-write','checkpoint-anchor-write-result','checkpoint-anchor-read','checkpoint-anchor-result','checkpoint-anchor-step','checkpoint-descriptor','checkpoint-descriptor-read','checkpoint-descriptor-result','checkpoint-descriptor-step','checkpoint-restore']
def kind(s):
 # Append rather than renumber any existing runtime phase.
 phases=' '.join(':'+x for x in PHASES)
 s=once(s,':release :ready :failed)',':release :ready :failed '+phases+')')
 s=once(s,'(event-ready :bool)', '(checkpoint-index :u32) (checkpoint-length :u32) (checkpoint-seen :bool) (checkpoint-invalid :bool) (event-ready :bool)')
 s=once(s,'(:epoch-result :storage-window))','(:epoch-result :storage-window) '+ ' '.join('(:'+x+' :storage-window)' for x in PHASES)+')')
 s=once(s,'(:ready) (:failed))','(:ready) (:failed) '+' '.join('(:'+x+')' for x in PHASES)+')')
 return s
def arms(s):
 advance='((:set (stage 1) (anchor-slot 0)) (:next :anchor) (:charge :steps *fn2-work-small* :runnable t))'
 s=once(s,'(include-book "boot-pack")','(include-book "boot-pack")\n(include-book "boot-checkpoint-core")')
 s=once(s,'(fn2-boot-operations) (defmachine-arms fn2-boot)','(fn2-boot-operations) (fn2-boot-checkpoint-core-operations) (defmachine-arms fn2-boot)')
 s=once(s,advance,'((:next :bootstrap) (:charge :steps *fn2-work-small* :runnable t))')
 # Prefix exactly one saved bootstrap address before packing or reading.
 # The callback derives it from actual config and writes it through CORE.
 snippets=(ROOT/'tools/boot_persisted_routing_arms.lisp').read_text()
 generated=[]
 for prefix,write,after in [('bootstrap',True,'bootstrap-read'),('bootstrap',False,'bootstrap-verify'),('checkpoint-anchor',True,'checkpoint-anchor-read'),('checkpoint-anchor',False,'checkpoint-anchor-step'),('checkpoint-descriptor',False,'checkpoint-descriptor-step')]:
  state=prefix+('-write' if write else '-read')
  result=prefix+('-write-result' if write else '-result')
  issue='(fn2-issue-write row-offset row-pool-slot row-pool-gen 0 4096 0 :principal 0)' if write else '(fn2-issue-read row-offset row-rx-slot row-rx-gen 4096 :principal 0)'
  generated.append('('+':'+state+' :on-refusal ((:stop :io)) (:if (not (and (natp budget) (< 0 budget))) ((:yield)) ((:issue '+issue+' :ok ((:set (pending 1) (event-ready 0)) (:next :'+result+') (:charge :bytes 4096 :steps *fn2-work-small* :descriptors 1))))))')
  reset='(:do (code) (fn2-core-reset row-rx-slot row-rx-gen))' if write else ''
  generated.append('(:'+result+' :on-refusal ((:stop :io)) (:cond ((equal row-event-ready 0) (:idle)) ((not (and (equal row-outcome *fn2-outcome-done*) (equal row-count 4096))) (:stop :io)) (t (:set (pending 0)) '+reset+' (:next :'+after+') (:charge :steps *fn2-work-stage* :runnable t))))')
 # New phases are appended in the declaration and arms, preserving old enums.
 s=once(s,'(:failed (:idle)))','(:failed (:idle))\n'+snippets+'\n'+'\n'.join(generated)+')')
 return s
if __name__=='__main__':
 for name,fn in [('executor',constructor),('boot-kind',kind),('boot',arms)]:
  text=fn(BEFORE[name]);lr.parse(text)
  if '--apply' in sys.argv:(ROOT/'books'/(name+'.lisp')).write_text(text)
