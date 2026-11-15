"""Project the same bounded cleanup transformations onto exact current ROOT099 source.

No physical-loader/observer or adoption implementation is imported. Original
historical fixtures remain intact; current source is a separate exact witness.
"""
from pathlib import Path
import json
import lisp_rewrite as lr
import seal_release_row_rewrite as row
import seal_release_held_rewrite as held
import seal_cleanup_phase_rewrite as phase
import seal_cleanup_consumer_rewrite as consumer
ROOT=Path(__file__).resolve().parents[1]
BEFORE=json.loads((ROOT/'tools/fixtures/seal-cleanup-current-before.json').read_text())
def one(pattern,source):
 found=lr.match(pattern,lr.parse(source).forms,deep=False)
 if len(found)!=1:raise ValueError(pattern)
 return found[0].node

def project(before):
 out=dict(before)
 out['books/runs.lisp'],_=held.transform('books/runs.lisp',before['books/runs.lisp'])
 s=row.transform(before['books/sealer.lisp']);ed=[]
 for pattern,replacement in held.REPLACEMENTS['books/sealer.lisp'].items():
  n=one(pattern,s)
  if 'release-row' in pattern:
   # Root has resident columns only; remove the absent physical fence/read.
   if pattern.startswith('(defun'):
    replacement=held.ROW
    node=lr.parse(replacement).forms[0]
    fence=lr.match('((when (= (fn2-run-installed-physical r fn2-run-installed) 1)) ?*rest)',[node])
    assert len(fence)==1
    replacement=lr.write(replacement,[(fence[0].start,fence[0].end,'')]).replace('\n      \n','\n')
   else:replacement=replacement.replace(' fn2-run-installed-physical','')
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
if __name__=='__main__':
 for name,new in project(BEFORE).items():
  path=ROOT/name
  allowed=(BEFORE[name],new)
  if name=='books/sealer.lisp':allowed=allowed+(row.transform(BEFORE[name]),)
  if path.read_text() not in allowed:raise ValueError('changed current source '+name)
  path.write_text(new)

def fixture_source():
 source=(ROOT/'tools/fixtures/seal-release-held-unit-provider-before.lisp').read_text()
 edits=[]
 for carrier,book,short in [('fn2-run-installed','runs','run-installed'),('fn2-run-cache','runs','run-cache'),('fn2-overlays','overlay','overlays'),('fn2-pool','pool','pool'),('fn2-seals','sealer','seals')]:
  # Find the sole actual declaration without importing a replacement carrier.
  matches=[]
  for path in [ROOT/'books'/(book+'.lisp')]:
   for m in lr.match(f'(defcolumns {carrier} ?*args)',lr.parse(path.read_text()).forms,deep=False):matches.append(m.node)
  if len(matches)!=1:raise ValueError('canonical declaration '+carrier)
  d=matches[0];cols=d.items[2].items
  fn=one(f'(defun fn2-srh-{short}-rows ?*args)',source)
  lists=lr.match('(cons (list ?*fields) ?tail)',[fn]);assert len(lists)==1
  getters='(list\n'+''.join(f'   ({carrier}-{c.items[0].low} i {carrier})\n' for c in cols)+'   )'
  target=lists[0].node.items[1];edits.append((target.start,target.end,getters))
 # The current carrier has no version-floor scalar; preserve every actual
 # scalar via current declaration inventory rather than import that feature.
 for field in ('version-floor','physical-count'):
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
 return source.replace('; provider 826e44b7fd086f13cee9344aa6a4dacef74c144b. This branch does not\n; carry that pool API yet; integrate with the provider before ACL2 execution.', '; provider826 query API retained by current ROOT099. All assertions are prepared\n; and unexecuted; snapshots enumerate the actual current carrier columns.')
