"""Named source transformation: ordered-source manifest -> schema compaction.

Only declared producers/authority/ownership are ported. Canonical codecs, page
writer, physical completion, root Ref/hash and construction-ledger scan remain.
"""
from pathlib import Path
import re
import lisp_rewrite as lr
BEFORE=Path(__file__).resolve().parent/'fixtures/checkpoint-compaction/manifest-before.lisp'
FAMILY=('begin','emit','finish','scan-begin','scan-step')
COMMON=('fn2-checkpoint-compaction fn2-checkpoint-build fn2-csnapshot fn2-checkpoints '
        'fn2-overlays fn2-run-installed fn2-checkpoint-predecessors fn2-checkpoint-predecessor-control')
EXTRAS={
 'begin':['fn2-overlays','fn2-run-installed'],
 'emit':['fn2-checkpoint-build','fn2-checkpoints','fn2-overlays','fn2-run-installed','fn2-checkpoint-predecessors','fn2-checkpoint-predecessor-control'],
 'finish':['fn2-checkpoint-build','fn2-checkpoints','fn2-overlays','fn2-run-installed','fn2-checkpoint-predecessors','fn2-checkpoint-predecessor-control'],
 'scan-begin':['fn2-checkpoint-build','fn2-checkpoints','fn2-overlays','fn2-run-installed','fn2-checkpoint-predecessors','fn2-checkpoint-predecessor-control'],
 'scan-step':['fn2-overlays','fn2-run-installed','fn2-checkpoint-predecessors','fn2-checkpoint-predecessor-control'],
}
def one(pattern,forms):
 found=lr.match(pattern,forms,deep=True)
 if len(found)!=1:raise ValueError('expected one manifest port subject: '+pattern)
 return found[0].node

def portable_function(text, suffix):
 for field in ('wfp','token','owner-kind','owner-slot','owner-gen','phase','schema'):
  text=text.replace('fn2-checkpoint-source-'+field,'fn2-checkpoint-compaction-'+field)
 text=text.replace('fn2-checkpoint-source-rank','fn2-checkpoint-compaction-output-rank')
 text=re.sub(r'(?<![\w-])fn2-checkpoint-source(?![\w-])','fn2-checkpoint-compaction',text)
 text=text.replace('*fn2-checkpoint-compaction-phase-scan*','*fn2-checkpoint-compaction-phase-schema*')
 text=text.replace('*fn2-checkpoint-source-phase-done*','*fn2-checkpoint-compaction-phase-done*')
 owner='(fn2-checkpoint-source-ownerp fn2-checkpoint-compaction fn2-csnapshot)'
 replacement=('(fn2-checkpoint-compaction-ownerp '+COMMON.rsplit(' fn2-checkpoint-predecessors',1)[0]+')'
              if suffix=='begin' else '(fn2-checkpoint-predecessor-complete-p '+COMMON+')')
 text=text.replace(owner,replacement)
 parsed=lr.parse(text);f=one('(defun fn2-checkpoint-metadata-manifest-'+suffix+' ?*body)',parsed.forms)
 decl=f.items[3];xargs=decl.items[1];stobjs=next(xargs.items[i+1] for i,x in enumerate(xargs.items[:-1]) if lr.emit(x,drop_comments=True)==':stobjs')
 guard=next(xargs.items[i+1] for i,x in enumerate(xargs.items[:-1]) if lr.emit(x,drop_comments=True)==':guard')
 extras=EXTRAS[suffix]
 text=lr.write(text,[(f.items[2].end-1,f.items[2].end-1,' '+' '.join(extras)),
                     (stobjs.end-1,stobjs.end-1,' '+' '.join(extras)),
                     (guard.end-1,guard.end-1,' '+' '.join('('+x+'-wfp '+x+')' for x in extras))])
 if suffix=='emit':
  parsed=lr.parse(text);changes=[]
  selected=one('(fn2-checkpoint-source-selectedp ?*args)',parsed.forms)
  changes.append((selected.start,selected.end,'(and (fn2-checkpoint-predecessor-ready-p '+COMMON+')\n                     (fn2-checkpoint-compaction-schema-drained-p '+COMMON.rsplit(' fn2-checkpoint-predecessors',1)[0]+'))'))
  obsolete=one('(equal (fn2-checkpoint-source-order ?*args) ?value)',parsed.forms)
  changes.append((obsolete.start,obsolete.end,'(equal (fn2-run-builds-run b fn2-run-builds) (fn2-checkpoint-compaction-output-rank 0 fn2-checkpoint-compaction))'))
  old_advance=one('(fn2-checkpoint-compaction (fn2-checkpoint-source-put ?*args))',parsed.forms)
  changes.append((old_advance.start,old_advance.end,'''(fn2-checkpoint-compaction (fn2-checkpoint-compaction-put 0
       (phase *fn2-checkpoint-compaction-phase-schema*) (schema-open 0)
       (has-last-schema 1) (last-schema (fn2-checkpoint-compaction-schema 0 fn2-checkpoint-compaction))
       (scan-kind 0) (scan-row 0) (schema-found 0) (best 0) (has-lower 0) (source-started 0)))'''))
  capture=one('(fn2-checkpoint-metadata-manifest-put extent ?*fields)',parsed.forms)
  for binding in capture.items[2:]:
   if not hasattr(binding,'items') or not binding.items:continue
   name=lr.emit(binding.items[0],drop_comments=True)
   if name.startswith('catalog-old-') and name!='catalog-old-stage':
    start=text.rfind('\n',0,binding.start)+1
    end=text.find('\n',binding.end)+1
    if text[start:binding.start].strip() or text[binding.end:end].strip():raise ValueError('old capture binding shares a line')
    changes.append((start,end,''))
   elif name in ('catalog-source-kind','catalog-source-row','catalog-source-order'):
    changes.append((binding.start,binding.end,'('+name+' '+('2' if name=='catalog-source-kind' else '0')+')'))
  text=lr.write(text,changes)
 return text

def project(source):
 if source!=BEFORE.read_text():raise ValueError('not the frozen ordered-source manifest class')
 parsed=lr.parse(source);changes=[]
 for suffix in FAMILY:
  f=one('(defun fn2-checkpoint-metadata-manifest-'+suffix+' ?*body)',parsed.forms)
  changes.append((f.start,f.end,portable_function(source[f.start:f.end],suffix)))
 macro=one('(defmacro fn2-checkpoint-metadata-manifest-emit-mv ?*body)',parsed.forms)
 changes.append((macro.start,macro.end,source[macro.start:macro.end].replace('fn2-checkpoint-source','fn2-checkpoint-compaction')))
 include=one('(include-book "checkpoint-build-state")',parsed.forms)
 changes.append((include.end,include.end,'\n(include-book "checkpoint-compaction-production")'))
 result=lr.write(source,changes)
 return result.replace('; One completed real source contributes one canonical schema10 entry. Only\n; successful append advances the ordered selector; page backpressure retains\n; the same source, builder and verified root for a later retry.', '; One completed nonempty schema contributes one canonical directory entry.\n; Successful append advances the actual schema continuation; page backpressure\n; retains the same completed physical root for a later retry.').replace('; Finish only after the selector exhausted every held source and each emitted\n; rank entered schema10 once.', '; Finish only after actual compaction and original-source coverage complete,\n; with each emitted schema rank entering the directory once.')
