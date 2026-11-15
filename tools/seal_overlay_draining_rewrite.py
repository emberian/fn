"""Atomic source replacement, distinct lease-bearing DRAINING overlay state."""
from pathlib import Path
import json
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
BEFORE=json.loads((ROOT/'tools/fixtures/seal-overlay-draining-before.json').read_text())
def one(pattern,source):
 found=lr.match(pattern,lr.parse(source).forms,deep=False)
 if len(found)!=1:raise ValueError(pattern)
 return found[0].node

def target(pattern,source):
 n=lr.parse(source).forms[0];ed=[]
 if pattern.startswith('(defcolumns'):
  e=lr.match('(:enum fn2-overlay-phase (:free :active :frozen :private :spare))',[n]);assert len(e)==1
  values=e[0].node.items[2];ed.append((values.end-1,values.end-1,' :draining'))
 elif pattern.startswith('(defun fn2-seal-retire '):
  bindings=n.items[-1].items[1].items
  gate=lr.match('(equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-frozen*)',[bindings[1]]);assert len(gate)==1
  ed.append((bindings[0].end,bindings[0].end,'\n      (phase (fn2-overlays-phase o fn2-overlays))'))
  ed.append((gate[0].start,gate[0].end,'(member-equal phase (list *fn2-overlay-phase-frozen* *fn2-overlay-phase-draining*))'))
  advance=lr.match('(fn2-ov-advance o *fn2-overlay-phase-frozen* *fn2-overlay-phase-free* fn2-overlays)',[n]);assert len(advance)==1
  arg=advance[0].node.items[2];ed.append((arg.start,arg.end,'phase'))
 elif pattern.startswith('(defun fn2-seal-install '):
  bindings=n.items[-1].items[1].items
  has=lr.match('(has-ov (< o orows))',[n]);assert len(has)==1
  # The row bounds are checked before inspecting the overlay phase.
  boundary=lr.match('((unless (or (zp k) ?*rest)) ?*answer)',[n]);assert len(boundary)==1
  pre='''((unless (or (not has-ov)
                       (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-frozen*)))
       (mv :state fn2-seals fn2-overlays fn2-run-installed fn2-pool))
      '''
  ed.append((boundary[0].start,boundary[0].start,pre))
  final=lr.match('(fn2-seals (fn2-seals-set-phase 0 *fn2-seal-phase-overlay-return* fn2-seals))',[n]);assert len(final)==1
  replace='''(fn2-overlays (if has-ov
       (fn2-overlays-set-phase o *fn2-overlay-phase-draining* fn2-overlays) fn2-overlays))
      '''
  ed.append((final[0].start,final[0].start,replace))
 elif pattern.startswith('(fn2-seal-shape fn2-seal-install '):
  reads=n.items[-1];ed.append((reads.end-1,reads.end-1,' fn2-overlays-phase fn2-overlays-set-phase'))
 elif pattern.startswith('(defun fn2-seal-overlay-return '):
  call=lr.match('((mv code fn2-overlays fn2-pool) ?*rest)',[n]);assert len(call)==1
  gate='''((unless (or (= o rows)
                       (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-draining*)))
       (mv :state fn2-seals fn2-overlays fn2-pool))
      '''
  ed.append((call[0].start,call[0].start,gate))
 elif pattern.startswith('(fn2-seal-shape fn2-seal-overlay-return '):
  reads=n.items[-1];ed.append((reads.end-1,reads.end-1,' fn2-overlays-phase'))
 else:raise ValueError(pattern)
 return lr.write(source,ed)
def transform(file,source):
 edits=[]
 for pattern,old in BEFORE.get(file,{}).items():
  n=one(pattern,source);current=source[n.start:n.end];new=target(pattern,old)
  if current==new:continue
  if current!=old:raise ValueError('changed input '+pattern)
  edits.append((n.start,n.end,new))
 return lr.write(source,edits)
if __name__=='__main__':
 for file in BEFORE:
  p=ROOT/file;p.write_text(transform(file,p.read_text()))
