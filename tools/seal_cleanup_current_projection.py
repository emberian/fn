"""Project bounded cleanup from explicit actual before-schema declarations.

ROOT099 and cold a565 remain separate exact before/after witnesses. The tool
checks production projections read-only and emits only an explicitly named
held test fixture; no runtime schema/fence is inferred from the test caller.
"""
from pathlib import Path
import json
import lisp_rewrite as lr
import seal_release_row_rewrite as row
import seal_release_held_rewrite as held
import seal_cleanup_phase_rewrite as phase
import seal_cleanup_consumer_rewrite as consumer
import seal_cleanup_schema as inventory
ROOT=Path(__file__).resolve().parents[1]
BEFORE=json.loads((ROOT/'tools/fixtures/seal-cleanup-current-before.json').read_text())
def one(pattern,source):
 found=lr.match(pattern,lr.parse(source).forms,deep=False)
 if len(found)!=1:raise ValueError(pattern)
 return found[0].node

def project(before,before_schema):
 inventory.validate_before(before,before_schema)
 physical=inventory.has_physical(before_schema)
 release=one('(defun fn2-seal-release ?*args)',before['books/sealer.lisp'])
 fences=lr.match('(fn2-run-installed-physical r fn2-run-installed)',[release])
 if len(fences)!=(1 if physical else 0):raise ValueError('before physical source/fence mismatch')
 out=dict(before)
 out['books/runs.lisp'],_=held.transform('books/runs.lisp',before['books/runs.lisp'])
 s=row.transform(before['books/sealer.lisp']);ed=[]
 for pattern,replacement in held.REPLACEMENTS['books/sealer.lisp'].items():
  n=one(pattern,s)
  if 'release-row' in pattern:
   # Remove the physical fence/read only when the actual before schema lacks it.
   if pattern.startswith('(defun') and not physical:
    replacement=held.ROW
    node=lr.parse(replacement).forms[0]
    fence=lr.match('((when (= (fn2-run-installed-physical r fn2-run-installed) 1)) ?*rest)',[node])
    assert len(fence)==1
    replacement=lr.write(replacement,[(fence[0].start,fence[0].end,'')]).replace('\n      \n','\n')
   elif not pattern.startswith('(defun') and not physical:replacement=replacement.replace(' fn2-run-installed-physical','')
  else:assert s[n.start:n.end]==held.BEFORE['books/sealer.lisp'][pattern]
  ed.append((n.start,n.end,replacement))
 for pattern in held.CALLERS:
  n=one(pattern,s);current=s[n.start:n.end]
  # caller_target edits only acceptance of actual retire/release results.
  ed.append((n.start,n.end,held.caller_target(pattern,current)))
 s=lr.write(s,ed);ed=[]
 for pattern in phase.BEFORE:
  n=one(pattern,s);current=s[n.start:n.end]
  changed=phase.target(pattern,current)
  if pattern.startswith('(fn2-seal-shape fn2-seal-install '):changed+=phase.OVERLAY
  ed.append((n.start,n.end,changed))
 out['books/sealer.lisp']=lr.write(s,ed).replace('; Install, then retire the overlay and release the hash workspace: one step\n; (no reader sees the run beside its published overlay, nor neither).', '; Publish once, then return overlay and hash handles in bounded cleanup steps.')
 file='books/machines-c-sealer-kind.lisp';s=before[file];n=one('(defcost fn2-sealer-step ?*body)',s)
 out[file]=lr.write(s,[(n.start,n.end,consumer.target(file,s[n.start:n.end]))])
 file='books/machines-c-sealer-events.lisp';s=before[file]
 arm=lr.match('((:more :retired :done) (:charge ?*body))',lr.parse(s).forms)
 if len(arm)!=1:raise ValueError('actual current runnable arm changed')
 values=arm[0].node.items[0]
 # CREDIT remains the existing retained refusal (:otherwise); no credit return.
 out[file]=lr.write(s,[(values.end-1,values.end-1,' :held')])
 return out

def schema_from_current():return inventory.current(ROOT)

def fixture_source(schema=None,label=None):
 if schema is None:schema=schema_from_current()
 if label is None:label="actual current schema"
 source=(ROOT/'tools/fixtures/seal-release-held-unit-provider-before.lisp').read_text()
 edits=[]
 for carrier,short in [('fn2-run-installed','run-installed'),('fn2-run-cache','run-cache'),('fn2-overlays','overlays'),('fn2-pool','pool'),('fn2-seals','seals')]:
  cols=inventory.columns(schema,carrier)
  fn=one(f'(defun fn2-srh-{short}-rows ?*args)',source)
  lists=lr.match('(cons (list ?*fields) ?tail)',[fn]);assert len(lists)==1
  getters='(list\n'+''.join(f'   ({carrier}-{c.items[0].low} i {carrier})\n' for c in cols)+'   )'
  target=lists[0].node.items[1];edits.append((target.start,target.end,getters))
 # Remove only historical scalar readers absent from this explicit schema.
 installed_scalars,_=inventory.extras(schema,'fn2-run-installed')
 for field in ('version-floor','physical-count'):
  if 'fn2-run-installed-'+field not in installed_scalars:
   for m in lr.match(f'(fn2-run-installed-{field} fn2-run-installed)',lr.parse(source).forms):edits.append((m.start,m.end,''))
 fn=one('(defun fn2-srh-staged-cleanup-body ?*args)',source)
 pub=lr.match('(published (fn2-srh-run-installed-rows 0 fn2-run-installed))',[fn]);assert len(pub)==1
 edits.append((pub[0].end,pub[0].end, '\n      (atomic-replacement (and (= (fn2-overlays-phase 0 fn2-overlays) *fn2-overlay-phase-draining*)\n       (= (fn2-run-installed-state 0 fn2-run-installed) *fn2-run-installed-state-live*)\n       (= (fn2-overlays-slot 0 fn2-overlays) oslot) (= (fn2-overlays-gen 0 fn2-overlays) ogen)\n       (eq (fn2-pool-slot-state oslot fn2-pool) :workspace)))'))
 result=lr.match('(and (eq reserve-o :ok) ?*rest)',[fn]);assert len(result)==1
 edits.append((result[0].node.items[0].end,result[0].node.items[0].end,' atomic-replacement'))
 for m in lr.match('(= (fn2-overlays-phase 0 fn2-overlays) *fn2-overlay-phase-frozen*)',[fn]):
  v=m.node.items[-1];edits.append((v.start,v.end,'*fn2-overlay-phase-draining*'))
 source='\n'.join(line.rstrip() for line in lr.write(source,edits).split('\n'))
 source=source.replace('; ordinary release must return :credit while retaining the row and handle.', '; Hypothesis-removal control: manual run-install after reserve-credit is not\n; the current sealer producer. Ordinary release must refuse :credit, retaining\n; the row/handle; no credit retry or return authority is asserted.')
 source=complete_scalar_snapshots(source,schema)
 return source.replace('; provider 826e44b7fd086f13cee9344aa6a4dacef74c144b. This branch does not\n; carry that pool API yet; integrate with the provider before ACL2 execution.', '; provider826 query API retained by current '+label+'. All assertions are prepared\n; and unexecuted; snapshots enumerate the actual current carrier columns.')


def complete_scalar_snapshots(source,schema):
 for carrier,short in [('fn2-run-installed','run-installed'),('fn2-run-cache','run-cache'),('fn2-overlays','overlays'),('fn2-seals','seals')]:
  scalars,arrays=inventory.extras(schema,carrier)
  if arrays:raise ValueError('nonpool array snapshot requires explicit projection '+carrier)
  if not scalars:continue
  row=f'(fn2-srh-{short}-rows 0 {carrier})';snapshot=f'(fn2-srh-{short}-snapshot {carrier})'
  # Replace legacy hand-listed globals as a whole before replacing direct
  # row captures. Every actual scalar, including future appended ones, follows.
  edits=[]
  for m in lr.match(f'(list {row} ?*globals)',lr.parse(source).forms):
   if all(getattr(x,'items',None) and x.items[0].low in scalars for x in m.node.items[2:]):edits.append((m.start,m.end,snapshot))
  source=lr.write(source,edits)
  source=lr.write(source,[(m.start,m.end,snapshot) for m in lr.match(row,lr.parse(source).forms)])
  fn=one(f'(defun fn2-srh-{short}-rows ?*args)',source)
  helper=f"\n(defun fn2-srh-{short}-snapshot ({carrier})\n (declare (xargs :stobjs {carrier} :verify-guards nil))\n (list {row} ({carrier}-rows {carrier})"+''.join(f' ({name} {carrier})' for name in scalars)+'))\n'
  source=lr.write(source,[(fn.end,fn.end,helper)])
 # Existing pool arrays are bounded snapshots too; refuse a new array rather
 # than silently omit it. New pool scalar fields are generated automatically.
 scalars,arrays=inventory.extras(schema,'fn2-pool')
 for name in arrays:
  if not lr.match(f'({name}i ?*args)',lr.parse(source).forms) or not lr.match(f'({name}-length fn2-pool)',lr.parse(source).forms):raise ValueError('pool array snapshot missing '+name)
 fn=one('(defun fn2-srh-pool-snapshot ?*args)',source);body=fn.items[-1];extra=[]
 for name in scalars:
  if not lr.match(f'({name} fn2-pool)',[fn]):extra.append(f' ({name} fn2-pool)')
 return lr.write(source,[(body.end-1,body.end-1,''.join(extra))]) if extra else source

def load_case(name):
 if name not in ('root','cold'):raise ValueError('unknown projection case '+name)
 fixtures=ROOT/'tools/fixtures'
 schemas=json.loads((fixtures/'seal-cleanup-before-schemas.json').read_text())
 before=json.loads((fixtures/('seal-cleanup-'+('current' if name=='root' else 'cold')+'-before.json')).read_text())
 after=json.loads((fixtures/('seal-cleanup-'+name+'-after.json')).read_text())
 return before,schemas[name],after

def composed_project(before,before_schema):
 import seal_overlay_draining_rewrite as draining
 result=project(before,before_schema)
 for file,source in list(result.items()):
  edits=[]
  for pattern in draining.BEFORE.get(file,{}):
   n=one(pattern,source)
   edits.append((n.start,n.end,draining.target(pattern,source[n.start:n.end])))
  result[file]=lr.write(source,edits)
 return result

if __name__=='__main__':
 import argparse
 parser=argparse.ArgumentParser(description='Read-only production projection check; optional held test emission.')
 parser.add_argument('--case',choices=('root','cold'),required=True)
 parser.add_argument('--check-current',action='store_true')
 parser.add_argument('--emit-held',type=Path)
 args=parser.parse_args();before,schema,after=load_case(args.case)
 result=composed_project(before,schema)
 for file,source in result.items():
  if source!=after[file]:raise ValueError('fixed after fixture differs '+file)
  if args.check_current and source!=(ROOT/file).read_text():raise ValueError('current runtime differs '+file)
 if args.emit_held:
  actual=schema_from_current() if args.check_current else schema
  args.emit_held.write_text(fixture_source(actual,label=('ROOT099' if args.case=='root' else 'cold-a565')))
 print(args.case+': exact projection matched'+(' current runtime' if args.check_current else ' fixed after fixture'))
